open OUnit2

let () =
  [
    (*Parsing_tests.tt;
      Lang_codegen_tests.tt;
      Expand_tests.tt;
      Pass_typeck_tests.tt;
      Pass_codegen_tests.tt;*)
    Docs_example.tt
  ]
  |> test_list
  |> run_test_tt_main
