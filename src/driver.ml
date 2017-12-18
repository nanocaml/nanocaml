module MPT = Migrate_parsetree
open Ast

let rewriter _config _cookies =
  let fallback = Ast_mapper.default_mapper in

  let structure_item mapper = function
    (* module%language Lx = ... *)
    | {pstr_loc = loc;
       pstr_desc =
         Pstr_extension
           (({txt = "language"},
             PStr [ {pstr_desc = Pstr_module mb} ]),
            [])}
      ->
       let lang = Lang.language_of_module mb in
       Lang.add_language lang;
       let mb' = Lang_codegen.gen_module_binding lang in
       {pstr_loc = loc;
        pstr_desc = Pstr_module mb'}

    (* let[@pass ...] pass_x = ... *)
    | {pstr_loc = loc;
       pstr_desc =
         Pstr_value
           (recflag,
            [ {pvb_attributes = [ {txt = "pass"}, _ ]} as vb ])}
      ->
       if recflag = Asttypes.Recursive then
         Location.raise_errorf ~loc
           "nanopass may not be declared recursive"
       else
         let pass = Pass.pass_of_value_binding vb |> Pass_typeck.typeck_pass in
         let vb' = Pass_codegen.gen_pass_vb pass in
         {pstr_loc = loc;
          pstr_desc = Pstr_value (Nonrecursive, [ vb' ])}

    | str -> fallback.structure_item mapper str
  in

  {fallback with structure_item = structure_item }



let () =
  MPT.Driver.register
    ~name:"nanocaml" ~args:[]
    ocaml_version
    rewriter
