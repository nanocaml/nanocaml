open OUnit2
open Migrate_parsetree
open Ast_405.Parsetree
open Ast_405.Ast_helper

let tt =
  "codegen" >:::
    let open Nanocaml.Lang in
    let open Nanocaml.Codegen in
    let loc = !default_loc in
    let ct_int = [%type: int] in
    let ct_expr = Typ.constr {txt = Lident "expr"; loc} [] in
    [

      "gen_core_type(1)" >::
        begin fun _ ->
        assert_equal
          (Typ.constr ~loc {txt = Lident "list"; loc}
             [ Typ.tuple ~loc [ ct_int; ct_expr ] ])
          (gen_core_type ~loc
             (NP_list
                (NP_tuple
                   [ NP_term ct_int;
                     NP_nonterm "expr" ])));
        end;

    ]
