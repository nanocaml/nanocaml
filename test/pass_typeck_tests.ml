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

    ]
