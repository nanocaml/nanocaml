open Migrate_parsetree

open Ast_405
let ocaml_version = Versions.ocaml_405

let migrate = Versions.migrate Versions.ocaml_current ocaml_version

open Parsetree

let gen_language ({pmb_expr = {pmod_desc = Pmod_structure s} as me} as m) =
  let rec extends = function
    | [] -> (None, [])
    | {pstr_desc = Pstr_include {pincl_mod = {pmod_desc = Pmod_ident id}}}::xs ->
      (Some id, snd (extends xs))
    | x::xs ->
      let (id, ast) = extends xs in
      (id, x::ast) in
  { m with pmb_expr =
             { me with pmod_desc = Pmod_structure
                           begin match extends s with
                             | (Some id, ast) -> begin
                                 ast
                               end
                             | (None, ast) -> begin
                                 ast
                               end
                           end} }

let mapper _config _cookies =
  let open Ast_mapper in
  let open Ast_helper in
  let structure_item mapper stri =
    match stri.pstr_desc with
    | Pstr_extension (({txt = "language"},
                       PStr [{pstr_desc = Pstr_module m}]), []) ->
      default_mapper.structure_item mapper
        { stri with pstr_desc = Pstr_module (gen_language m)}
    | _ -> default_mapper.structure_item mapper stri in
  { default_mapper with structure_item }

let () =
  Driver.register
    ~name:"nanocaml" ~args:[]
    ocaml_version mapper
