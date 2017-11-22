module MPT = Migrate_parsetree
open Ast

(* artificially create dependency *)
let () =
  let open Lang in
  ()

let mapper _config _cookies =
  Ast_mapper.default_mapper

let () =
  MPT.Driver.register
    ~name:"nanocaml" ~args:[]
    ocaml_version mapper
