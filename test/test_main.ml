open OUnit2
open Migrate_parsetree
open Ast_405.Parsetree
open Ast_405.Longident
module Nano = Nanocaml

let t_parsing =
  "parsing" >:::
    let open Nanocaml.Lang in
    let nt_names = ["expr"; "stmt"] in
    let t_of_ct = type_of_core_type ~nt_names in
    let nt_of_td = nonterm_of_type_decl ~nt_names in
    let l_of_mb = language_of_module in
    [

      "type_of_core_type(1)" >::
        begin fun _ ->
        match t_of_ct [%type: (int * expr) list] with
        | NPtype_list
          (NPtype_tuple
             [NPtype_term {ptyp_desc = Ptyp_constr ({txt = Lident "int"}, [])};
              NPtype_nonterm "expr"]) -> ()
        | _ ->
           assert_failure "[(int * expr) list] does not match"
        end;

      "type_of_core_type(2)" >::
        begin fun _ ->
        match t_of_ct [%type: int list] with
        | NPtype_term {ptyp_desc = Ptyp_constr ({txt = Lident "list"}, _)} -> ()
        | _ -> assert_failure "[int list] should be a list terminal"
        end;

      "type_of_core_type(3)" >::
        begin fun _ ->
        match t_of_ct [%type: int * string] with
        | NPtype_term {ptyp_desc = Ptyp_tuple [_; _]} -> ()
        | _ -> assert_failure "[int * string] should be a tuple terminal"
        end;

      "nonterm_of_type_decl(1)" >::
        begin fun _ ->
        let si = [%stri type expr = [ `Var of string | `Int of int ] ] in
        match si.pstr_desc with
        | Pstr_type (_, [td]) ->
           begin match nt_of_td td with
           | {npnt_name = "expr";
              npnt_productions = [
                  {npp_name = "Var"};
                  {npp_name = "Int"} ]} -> ()
           | _ ->
              assert_failure "expr nonterm has the wrong structure"
           end
        | _ -> assert_failure "unreachable"
        end;

      "nonterm_of_type_decl(2)" >::
        begin fun _ ->
        let si = [%stri type expr = Var of string | Int of int ] in
        match si.pstr_desc with
        | Pstr_type (_, [td]) ->
           (try let _ = nt_of_td td in
                assert_failure "expected nonterm to fail"
            with Location.Error _ -> ());
        | _ -> assert_failure "unreachable"
        end;

      "language_of_module(1)" >::
        begin fun _ ->
        let si = [%stri module L0 = struct
                    type a = [ `A of b ]
                    and b = [ `B of a ]
                  end]
        in
        match si.pstr_desc with
        | Pstr_module mb ->
           let lang = l_of_mb mb in
           assert_equal "L0" lang.npl_name;
           assert_equal ["a"; "b"] (List.map (fun nt -> nt.npnt_name)
                                      lang.npl_nonterms);
           assert_equal [ {npp_name = "A"; npp_args = [ NPtype_nonterm "b" ]};
                          {npp_name = "B"; npp_args = [ NPtype_nonterm "a" ]} ]
             (lang.npl_nonterms
              |> List.map (fun nt -> nt.npnt_productions)
              |> List.concat)
        | _ ->
           assert_failure "unreachable"
        end;

      "language_of_module(2)" >::
        begin fun _ ->
        let si = [%stri module L0 = struct
                    type a = [ `A of b ]
                    type b = [ `B of a ] (* must be single recursive declaration *)
                  end ]
        in
        match si.pstr_desc with
        | Pstr_module mb ->
           (try let _ = l_of_mb mb in
                assert_failure "expected language to fail"
            with Location.Error _ -> ())
        | _ ->
           assert_failure "unreachable"
        end;

    ]



let () =
  run_test_tt_main
    (test_list [
         t_parsing
    ])
