open OUnit2

type a1 = int        [@@deriving random,show]
type a1_bis = int    [@const 4] [@@deriving random,show]
type a2 = int32      [@@deriving random,show]
type a3 = int64      [@@deriving random,show]
type a4 = nativeint  [@@deriving random,show]
type a5 = float      [@@deriving random,show]
type a6 = bool       [@@deriving random,show]
(*
type a7 = char       [@@deriving random,show]
type a8 = string     [@@deriving random,show]
type a9 = bytes      [@@deriving random,show]
*)
type r  = int ref    [@@deriving random,show]
type l  = int list   [@@deriving random,show]
(*
type a  = int array  [@@deriving random,show]
*)
type o  = int option [@@deriving random,show]


type foo= int ref option list list [@@deriving random]
(*
type foobar = (int * bool ref) option list list [@@deriving random]
*)

let st = Random.State.make [||]

let test_const _ctxt =
  for _i=1 to 100 do
    assert_equal ~printer:show_a1_bis 4 (random_a1_bis st st)
  done;
  ()


let suite = "Test deriving(Random)" >::: [
  "test_const" >:: test_const
]

