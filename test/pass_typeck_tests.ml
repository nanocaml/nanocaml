open OUnit2
open Migrate_parsetree
open Ast_405.Parsetree
open Ast_405.Ast_helper

let test_L0 = Parsing_tests.test_L0
let test_L0_a = Parsing_tests.test_L0_a

let tt =
  "pass_typeck" >:::
    let open Nanocaml.Pass in
    let open Nanocaml.Lang in
    let module TC = Nanocaml.Pass_typeck in
    let loc = !default_loc in

    let pass1 =
      [%stri let[@pass Test_L0 => Test_L0] pass1 =
         let rec a = function
           | `A _ -> true
           | `A0 -> false
         and b = function
           | `B x -> a x
         in
         a]
      |> Parsing_tests.stri_value_binding
      |> pass_of_value_binding
    in

    let any = NPpat_any loc in
    let var_x = NPpat_var {txt = "x"; loc} in

    [

      "catamorphism(1)" >::
        begin fun _ ->
        let pass =
          Parsing_tests.stri_value_binding
            [%stri let[@pass Test_L0 => Test_L0] s =
               let rec a = function
                 | `A0 _ -> 0
               in 0 ]
          |> pass_of_value_binding
        in
        match TC.catamorphism ~loc ~pass test_L0_a with
        | {pexp_desc = Pexp_ident {txt = Lident "a"}} -> ()
        | _ -> assert_failure "cata of 'a' has wrong form"
        end;

      "catamorphism(2)" >::
        begin fun _ ->
        let pass =
          Parsing_tests.stri_value_binding
            [%stri let[@pass Test_L0 => Test_L0] s =
               let rec b = function
                 | `B _ -> 0
               in 0 ]
          |> pass_of_value_binding;
        in
        try
          TC.catamorphism ~loc ~pass test_L0_a
          |> ignore;
          assert_failure "expected cata for 'a' to fail (not defined)"
        with Location.Error _ -> ()
        end;

      "typeck_pat(1)" >::
        begin fun _ ->
        assert_equal any (TC.typeck_pat ~pass:pass1 (NP_nonterm "a") any);
        assert_equal var_x (TC.typeck_pat ~pass:pass1 (NP_nonterm "b") var_x);
        end;

      "typeck_pat(2)" >::
        begin fun _ ->
        let pat = NPpat_variant ("A", Some any, loc) in
        assert_equal pat (TC.typeck_pat ~pass:pass1 (NP_nonterm "a") pat);
        end;

      "typeck_pat(3)" >::
        begin fun _ ->
        let pat = NPpat_alias (var_x, {txt = "y"; loc}) in
        assert_equal pat (TC.typeck_pat ~pass:pass1 (NP_nonterm "a") pat);
        assert_equal pat (TC.typeck_pat ~pass:pass1 (NP_term [%type: int]) pat);
        end;

      "typeck_pat(4)" >::
        begin fun _ ->
        let pat = NPpat_tuple ([ any; any ], loc) in
        assert_equal pat (TC.typeck_pat ~pass:pass1
                            (NP_tuple [ NP_term [%type: int]; NP_nonterm "a" ])
                            pat);
        end;

      "typeck_pat(5)" >::
        begin fun _ ->
        try
          TC.typeck_pat ~pass:pass1
            (NP_tuple [ NP_term [%type: int];
                        NP_nonterm "a" ])
            (NPpat_tuple ([ any; any; any ], loc))
          |> ignore;
          assert_failure "expected bad arg-count tuple to fail"
        with Location.Error e ->
          assert_bool "shows arg counts"
            (e.msg = "wrong number of tuple arguments; expected 2, found 3");
        end;

      "typeck_pat(6)" >::
        begin fun _ ->
        let pat = NPpat [%pat? 0] in
        assert_equal pat (TC.typeck_pat ~pass:pass1 (NP_term [%type: int]) pat);
        (* note: we don't typecheck against ocaml types; if it's a terminal, just
           let ocaml do the typechecking *)
        assert_equal pat (TC.typeck_pat ~pass:pass1 (NP_term [%type: string]) pat);
        end;

      "typeck_pat(7)" >::
        begin fun _ ->
        try
          TC.typeck_pat ~pass:pass1
            (NP_nonterm "a")
            (NPpat [%pat? [1,2,3]])
          |> ignore;
          assert_failure "expected NPpat to fail on something other than NP_term type"
        with Location.Error _ -> ()
        end;

      "typeck_nonterm(1)" >::
        begin fun _ ->
        assert_equal None (TC.typeck_nonterm ~pass:pass1 ~loc "a" "A0" None);
        assert_equal (Some var_x) (TC.typeck_nonterm ~pass:pass1 ~loc "a" "A" (Some var_x));
        end;

      "typeck_nonterm(2)" >::
        begin fun _ ->
        try
          TC.typeck_nonterm ~pass:pass1 ~loc "a" "A0" (Some any)
          |> ignore; assert_failure "expected typeck to fail (nonterm doesn't expect arguments)"
        with Location.Error e ->
          assert_bool "contains 'unexpected'"
            (String.sub e.msg 0 10 = "unexpected");
        end;

      "typeck_nonterm(3)" >::
        begin fun _ ->
        try
          TC.typeck_nonterm ~pass:pass1 ~loc "a" "A" None
          |> ignore; assert_failure "expected typeck to fail (nonterm expects arguments)"
        with Location.Error e ->
          assert_bool "contains 'expected'"
            (String.sub e.msg 0 8 = "expected");
        end;

    ]
