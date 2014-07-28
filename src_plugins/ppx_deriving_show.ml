open Longident
open Location
open Asttypes
open Parsetree
open Ast_helper
open Ast_convenience

let prefix = "show"
let raise_errorf = Ppx_deriving.raise_errorf

let () =
  Ppx_deriving.register "Show" (fun ~options ~path type_decls ->
    let argn i = Printf.sprintf "a%d" i in
    let rec expr_of_typ typ =
      match Ppx_deriving.attr ~prefix "printer" typ.ptyp_attributes with
      | Some (_, PStr [{ pstr_desc = Pstr_eval (printer, _) }]) -> [%expr [%e printer] fmt]
      | Some ({ loc }, _) -> raise_errorf ~loc "Invalid [@deriving.%s.printer] syntax" prefix
      | None ->
        let format x = [%expr Format.fprintf fmt [%e str x]] in
        let seq start finish fold typ =
          [%expr fun x ->
            Format.pp_print_string fmt [%e str start];
            ignore ([%e fold] (fun sep x ->
              if sep then Format.pp_print_string fmt "; ";
              [%e expr_of_typ typ] x; true) false x);
            Format.pp_print_string fmt [%e str finish];]
        in
        match typ with
        | [%type: int]    -> format "%d"
        | [%type: int32]     | [%type: Int32.t] -> format "%ldl"
        | [%type: int64]     | [%type: Int64.t] -> format "%LdL"
        | [%type: nativeint] | [%type: Nativeint.t] -> format "%ndn"
        | [%type: float]  -> format "%F"
        | [%type: bool]   -> format "%B"
        | [%type: char]   -> format "%C"
        | [%type: string] -> format "%S"
        | [%type: bytes]  -> [%expr fun x -> Format.fprintf fmt "%S" (Bytes.to_string x)]
        | [%type: [%t? typ] list]  -> seq "["   "]" [%expr List.fold_left]  typ
        | [%type: [%t? typ] array] -> seq "[|" "|]" [%expr Array.fold_left] typ
        | [%type: [%t? typ] option] ->
          [%expr
            function
            | None -> Format.pp_print_string fmt "None"
            | Some x ->
              Format.pp_print_string fmt "Some (";
              [%e expr_of_typ typ] x;
              Format.pp_print_string fmt ")"]
        | { ptyp_desc = Ptyp_constr ({ txt = lid }, args) } ->
          app (Exp.ident (mknoloc (Ppx_deriving.mangle_lid (`Prefix "pp") lid)))
              ((List.map (fun typ -> [%expr fun fmt -> [%e expr_of_typ typ]]) args) @
               [[%expr fmt]])
        | { ptyp_desc = Ptyp_tuple typs } ->
          let args = List.mapi (fun i typ -> app (expr_of_typ typ) [evar (argn i)]) typs in
          [%expr
            fun [%p ptuple (List.mapi (fun i _ -> pvar (argn i)) typs)] ->
            Format.pp_print_string fmt "(";
            [%e args |> Ppx_deriving.(fold_exprs
                    (seq_reduce ~sep:[%expr Format.pp_print_string fmt ", "]))];
            Format.pp_print_string fmt ")"]
        | { ptyp_desc = Ptyp_variant (fields, _, _); ptyp_loc } ->
          let cases =
            fields |> List.map (fun field ->
              match field with
              | Rtag (label, _, true (*empty*), []) ->
                Exp.case (Pat.variant label None)
                         [%expr Format.pp_print_string fmt [%e str ("`" ^ label)]]
              | Rtag (label, _, false, [typ]) ->
                Exp.case (Pat.variant label (Some (pvar "x")))
                         [%expr Format.pp_print_string fmt [%e str ("`" ^ label ^ " ")];
                                [%e expr_of_typ typ] x]
              | Rinherit ({ ptyp_desc = Ptyp_constr (tname, []) } as typ) ->
                Exp.case (Pat.alias (Pat.type_ tname) (mknoloc "x"))
                         [%expr [%e expr_of_typ typ] x]
              | _ ->
                raise_errorf ~loc:ptyp_loc "Cannot derive Show for %s"
                             (Ppx_deriving.string_of_core_type typ))
          in
          Exp.function_ cases
        | { ptyp_desc = Ptyp_var name } -> [%expr [%e evar ("poly_"^name)] fmt]
        | { ptyp_desc = Ptyp_alias (typ, _) } -> expr_of_typ typ
        | { ptyp_loc } ->
          raise_errorf ~loc:ptyp_loc "Cannot derive Show for %s"
                       (Ppx_deriving.string_of_core_type typ)
    in
    let struct_of_type ({ ptype_name = { txt = name }; ptype_loc = loc } as type_decl) =
      let path = Ppx_deriving.path_of_type_decl ~path type_decl in
      let prettyprinter =
        match type_decl.ptype_kind, type_decl.ptype_manifest with
        | Ptype_abstract, Some manifest ->
          [%expr fun fmt -> [%e expr_of_typ manifest]]
        | Ptype_variant constrs, _ ->
          let cases =
            constrs |> List.map (fun { pcd_name = { txt = name' }; pcd_args } ->
              let constr_name = Ppx_deriving.expand_path ~path name' in
              let args = List.mapi (fun i typ -> app (expr_of_typ typ) [evar (argn i)]) pcd_args in
              let result =
                match args with
                | []   -> [%expr Format.pp_print_string fmt [%e str constr_name]]
                | args ->
                  [%expr Format.pp_print_string fmt [%e str (constr_name ^ " (")];
                  [%e args |> Ppx_deriving.(fold_exprs
                        (seq_reduce ~sep:[%expr Format.pp_print_string fmt ", "]))];
                  Format.pp_print_string fmt ")"]
              in
              Exp.case (pconstr name' (List.mapi (fun i _ -> pvar (argn i)) pcd_args)) result)
          in
          [%expr fun fmt -> [%e Exp.function_ cases]]
        | Ptype_record labels, _ ->
          let fields =
            labels |> List.mapi (fun i { pld_name = { txt = name }; pld_type } ->
              let field_name = if i = 0 then Ppx_deriving.expand_path ~path name else name in
              [%expr Format.pp_print_string fmt [%e str (field_name ^ " = ")];
                [%e expr_of_typ pld_type] [%e Exp.field (evar "x") (mknoloc (Lident name))]])
          in
          [%expr fun fmt x ->
            Format.pp_print_string fmt "{ ";
            [%e fields |> Ppx_deriving.(fold_exprs
                  (seq_reduce ~sep:[%expr Format.pp_print_string fmt "; "]))];
            Format.pp_print_string fmt " }"]
        | Ptype_abstract, None -> raise_errorf ~loc "Cannot derive Show for fully abstract type"
        | Ptype_open, _        -> raise_errorf ~loc "Cannot derive Show for open type"
      in
      let pp_poly_apply = Ppx_deriving.poly_apply_of_type_decl type_decl (evar
                            (Ppx_deriving.mangle_type_decl (`Prefix "pp") type_decl)) in
      let stringprinter = [%expr fun x -> Format.asprintf "%a" [%e pp_poly_apply] x] in
      let polymorphize  = Ppx_deriving.poly_fun_of_type_decl type_decl in
      [Vb.mk (pvar (Ppx_deriving.mangle_type_decl (`Prefix "pp") type_decl))
                   (polymorphize prettyprinter);
       Vb.mk (pvar (Ppx_deriving.mangle_type_decl (`Prefix "show") type_decl))
                   (polymorphize stringprinter);]
    in
    let sig_of_type type_decl =
      let typ = Ppx_deriving.core_type_of_type_decl type_decl in
      let polymorphize = Ppx_deriving.poly_arrow_of_type_decl
            (fun var -> [%type: Format.formatter -> [%t var] -> unit]) type_decl in
      [Sig.value (Val.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Prefix "pp") type_decl))
                  (polymorphize [%type: Format.formatter -> [%t typ] -> unit]));
       Sig.value (Val.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Prefix "show") type_decl))
                  (polymorphize [%type: [%t typ] -> string]))]
    in
    Ppx_deriving.catch (fun () ->
      [Str.value Recursive (List.concat (List.map struct_of_type type_decls))]),
    List.concat (List.map sig_of_type type_decls))
