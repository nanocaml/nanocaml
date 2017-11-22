(* this file is used as a single-point-of-control for
   the parsetree version *)
open Migrate_parsetree
include Ast_405
include Ast_405.Parsetree
let ocaml_version = Versions.ocaml_405
