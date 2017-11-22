module MPT = Migrate_parsetree
open Ast

let mapper _config _cookies =
  Ast_mapper.default_mapper

let () =
  MPT.Driver.register
    ~name:"nanocaml" ~args:[]
    ocaml_version mapper
