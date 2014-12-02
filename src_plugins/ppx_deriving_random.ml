open Longident
open Location
open Asttypes
open Parsetree
module AH = Ast_helper
module AC = Ast_convenience

let deriver = "random"
let raise_errorf = Ppx_deriving.raise_errorf

let parse_options options =
  options |> List.iter (fun (name, expr) ->
    match name with
    | _ -> raise_errorf ~loc:expr.pexp_loc "%s does not support option %s" deriver name)

(* custom generator *)
let attr_generator attrs =
  Ppx_deriving.(attrs |> attr ~deriver "generator" |> Arg.(get_attr ~deriver expr))

(* return a constant *)
let attr_const attrs =
  Ppx_deriving.(attrs |> attr ~deriver "const" |> Arg.(get_attr ~deriver expr))

(* integer range *)
let attr_range attrs =
  Ppx_deriving.(attrs |> attr ~deriver "range" |> Arg.(get_attr ~deriver expr))

let argn = Printf.sprintf "a%d"

let char_offset = 32
let char_range = 125 - char_offset

(* generate a random value using the variable [st] *)
let rec expr_of_typ ~self typ =
  let rec expr_of_typ typ = match attr_generator typ.ptyp_attributes, attr_const typ.ptyp_attributes with
  | Some gen, _ -> gen  (* user-provided gen *)
  | None, Some cst -> [%expr fun _ -> [%e cst]]  (* constant *)
  | None, None ->
    match typ with
    | [%type: int] ->
        let low, high =
          match attr_range typ.ptyp_attributes with
          | Some {pexp_desc=Pexp_tuple
              [ {pexp_desc=Pexp_constant(Const_int x)};
                {pexp_desc=Pexp_constant(Const_int y)}]} -> x,y
          | Some e -> raise_errorf ~loc:typ.ptyp_loc "bad attribute (expected int*int)"
          | None -> 0,100
        in
        [%expr fun st ->
          [%e  AC.int low] + Random.State.int st [%e AC.int (high-low)]
        ]
    | [%type: float] -> [%expr fun st -> Random.State.float st 100.]
    | [%type: int64] -> [%expr fun st -> Random.State.int64 st 100L]
    | [%type: int32] -> [%expr fun st -> Random.State.int32 st 100l]
    | [%type: nativeint] ->
        [%expr fun st -> Random.State.nativeint st (Nativeint.of_int 100)]
    | [%type: bool] -> [%expr Random.State.bool]
    | [%type: bytes]
    | [%type: string] ->
        [%expr fun st ->
          let len = Random.State.int st 15 in
          String.init len
            (fun _ ->
              Char.chr ([%e AC.int char_offset]
                + Random.State.int st [%e AC.int char_range])
            )
        ]
    | [%type: [%t? typ] ref] ->
        [%expr fun st -> ref [%e expr_of_typ typ]]
    | [%type: [%t? typ] list]  ->
        [%expr fun st ->
          let i = Random.State.int st 30 in
          let gen = [%e expr_of_typ typ] in
          let rec list_make i f st = match i with
            | 0 -> []
            | _ -> f st :: list_make (i-1) f st
          in
          list_make i gen st
        ]
    | [%type: [%t? typ] array] ->
        [%expr fun st ->
          let len = Random.State.int st 30 in
          let gen = [%e expr_of_typ typ] in
          Array.init len (fun _ -> gen st)
        ]
    | [%type: [%t? typ] option] ->
        [%expr fun st ->
          if Random.State.bool st then Some ([%e expr_of_typ typ] st) else None
        ]
    | { ptyp_desc = Ptyp_tuple typs} ->
        [%expr fun st ->
          [%e AC.tuple
            (List.map (fun ty -> [%expr [%e expr_of_typ ty] st]) typs)
          ]
        ]
    | { ptyp_desc = Ptyp_constr ({ txt = lid }, args) } ->
      begin match self with
      | Some (`Variant name, used) when Longident.last lid=name ->
          (* typ is actually a recursive reference to the type
            being defined. Use a "self" variable and a "depth" parameter
            that will be bound by the caller *)
          incr used;
          [%expr self depth]
      | Some (`Record name, used) when Longident.last lid=name ->
          (* recursive type, but as a record it doesn't control depth *)
          incr used;
          [%expr self]
      | _ ->
          [%expr fun st ->
            [%e AC.app
              (AH.Exp.ident
                (mknoloc (Ppx_deriving.mangle_lid (`Prefix "random") lid)))
              (List.map
                (fun ty ->
                  [%expr [%e expr_of_typ ty] st]
                ) args @ [[%expr st]])
            ]
          ]
      end
    | { ptyp_loc } ->
      raise_errorf ~loc:ptyp_loc "%s cannot be derived for %s"
                   deriver (Ppx_deriving.string_of_core_type typ)
  in
  expr_of_typ typ

(* fold right, with index of element *)
let fold_right_i f l acc =
  let rec fold' f acc i l = match l with
  | [] -> acc
  | x::tail ->
      let acc = fold' f acc (i+1) tail in
      f i x acc
  in
  fold' f acc 0 l

(* choice among the given generators. [st] in scope. *)
let choice l = match l with
  | [] -> assert false
  | [x] -> x
  | _ ->
    let n = List.length l in
    assert (n>0);
    [%expr
      let choice = Random.State.int st [%e AC.int n] in
      [%e fold_right_i
        (fun i x tail ->
          [%expr if choice = [%e AC.int i]
            then [%e x]
            else [%e tail]
          ]
        ) l [%expr assert false]
      ]
    ]

let str_of_type ~options ~path ({ ptype_loc = loc } as type_decl) =
  parse_options options;
  let generator =
    match type_decl.ptype_kind, type_decl.ptype_manifest with
    | Ptype_abstract, Some manifest ->
      expr_of_typ ~self:None manifest
    | Ptype_variant constrs, _ ->
        let self_used = ref 0 in
        let self = Some (`Variant type_decl.ptype_name.txt, self_used) in
        (* some cases are not recursive, some others are *)
        let base_cases, rec_cases =
          List.fold_right
            (fun {pcd_name={txt=name'};pcd_args} (base,rec_) ->
              let used = !self_used in
              (* given random arguments, apply the constructor *)
              let apply_constr = AC.constr
                name'
                (List.mapi (fun i arg -> AC.evar (argn i)) pcd_args)
              in
              (* compute random argument for each parameter. [st] in scope *)
              let gen = fold_right_i
                (fun i typ tail ->
                  [%expr
                    let [%p AC.pvar (argn i)] =
                      [%e AC.app (expr_of_typ ~self typ) [[%expr st]]]
                    in [%e tail]
                  ]
                ) pcd_args apply_constr
              in
              (* is at least one argument recursive? *)
              let is_rec = !self_used > used in
              if is_rec
                then base, gen::rec_
                else gen::base, rec_
            ) constrs ([], [])
        in
        (* build the generator *)
        if !self_used > 0
        then (
          assert (rec_cases <> []);
            [%expr
            (* recursive function *)
            let rec self depth st =
              let proba_stop = exp (-1. /. (5. *. depth +. 1.)) in (* the deeper, the more likely *)
              if Random.State.float st 1. < proba_stop
                then [%e choice base_cases]
                else
                  let depth = depth +. 1. in
                  [%e choice rec_cases ]
            in
            self 0.
          ]
        ) else [%expr fun st -> [%e choice base_cases]]
    | Ptype_record labels, _ ->
        let self_used = ref 0 in
        let self = Some (`Record type_decl.ptype_name.txt, self_used) in
        (* some cases are not recursive, some others are *)
        let fields =
          List.mapi
            (fun i field ->
              let gen = expr_of_typ ~self field.pld_type in
              field.pld_name.txt, [%expr [%e gen] st]
            ) labels
        in
        (* build the record *)
        let record = AC.record fields in
        (* build the generator *)
        if !self_used > 0
        then
          [%expr
            (* recursive function *)
            let rec self st = [%e record] in
            self
          ]
        else [%expr fun st -> [%e record]]
    | Ptype_abstract, None ->
      raise_errorf ~loc "%s cannot be derived for fully abstract types" deriver
    | Ptype_open, _        ->
      raise_errorf ~loc "%s cannot be derived for open types" deriver
  in
  let polymorphize  = Ppx_deriving.poly_fun_of_type_decl type_decl in
  [AH.Vb.mk (AC.pvar (Ppx_deriving.mangle_type_decl (`Prefix "random") type_decl))
               (polymorphize generator);
  ]

let sig_of_type ~options ~path type_decl =
  parse_options options;
  let typ = Ppx_deriving.core_type_of_type_decl type_decl in
  let polymorphize = Ppx_deriving.poly_arrow_of_type_decl
        (fun var -> [%type: Random.State.t -> [%t var]]) type_decl in
  [AH.Sig.value (AH.Val.mk
    (mknoloc (Ppx_deriving.mangle_type_decl (`Prefix "random") type_decl))
              (polymorphize [%type: Random.State.t -> [%t typ]]));
  ]

let () =
  Ppx_deriving.(register deriver {
    core_type = Some (fun typ ->expr_of_typ ~self:None typ) ;
    structure = (fun ~options ~path type_decls ->
      [AH.Str.value Nonrecursive
        (List.concat (List.map (str_of_type ~options ~path) type_decls))]);
    signature = (fun ~options ~path type_decls ->
      List.concat (List.map (sig_of_type ~options ~path) type_decls));
  })
