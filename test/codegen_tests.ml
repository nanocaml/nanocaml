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

      "gen_type_decl(1)" >::
        begin fun _ ->
        assert_equal
          (Type.mk ~loc
             {txt = "expr"; loc}
             ~manifest:(Typ.variant ~loc
                          [ Rtag ("Zero", [], true, []);
                            Rtag ("Succ", [], false, [ ct_expr ]) ]
                          Closed None))
          (gen_type_decl
             {npnt_name = "expr";
              npnt_loc = loc;
              npnt_productions =
                [ {nppr_name = "Zero"; nppr_args = []};
                  {nppr_name = "Succ"; nppr_args = [ NP_nonterm "expr" ]} ]})
        end;

      "gen_module_binding(1)" >::
        begin fun _ ->
        let var_a =
          Typ.variant ~loc
            [ Rtag ("A", [], true, []) ]
            Closed None
        in
        let var_b =
          Typ.variant ~loc
            [ Rtag ("B", [], false, [ ct_int ]) ]
            Closed None
        in

        assert_equal
          (Mb.mk ~loc {txt = "L0"; loc}
             (Mod.structure ~loc
                [ Str.type_ ~loc Recursive
                    [ Type.mk ~loc {txt = "a"; loc} ~manifest:var_a;
                      Type.mk ~loc {txt = "b"; loc} ~manifest:var_b; ] ]))
          (gen_module_binding
             {npl_name = "L0";
              npl_loc = loc;
              npl_nonterms =
                [ {npnt_name = "a";
                   npnt_loc = loc;
                   npnt_productions =
                     [ {nppr_name = "A"; nppr_args = []} ]};
                  {npnt_name = "b";
                   npnt_loc = loc;
                   npnt_productions =
                     [ {nppr_name = "B"; nppr_args = [ NP_term ct_int ]} ]} ]})
        end;

    ]
