open Migrate_parsetree

open Ast_405
let ocaml_version = Versions.ocaml_405

let migrate = Versions.migrate Versions.ocaml_current ocaml_version

open Parsetree

(* A reference to an existing type/valid expression composed of references
   to existing types. *)
type type_ref =
  | Named of string (* e.g.: expr *)
  | List of type_ref  (* e.g.: stmt list *)
  | Tuple of type_ref list (* e.g.: (expr, int) *)

(* A "branch" in the AST. Contains a data constructor and a list of type
   references, describing what the branch holds. For example:
   Call of expr * expr list *)
type node_branch = {constructor : string; params : type_ref list}

(* A complete type of node within a language's AST. For example:
   [Int of int | Let of id * expr * expr | Succ of expr] *)
type node_type = node_branch list

(* The type of a map from string -> node_type. These make up the AST of
   a language. For example:
   type id = [Name of string]
   type expr = [Int of int | Let of id * expr * expr | Succ of expr] *)
module TypeMap = Map.Make(String)
type language_type = { entry : type_ref;
                       productions: node_type TypeMap.t }

(* A hash table from string -> language_type. This represents the database
   of all languages defined in a program. *)
let languages : (string, language_type) Hashtbl.t = Hashtbl.create 10

let rec ref_of_type = function
  | {ptyp_desc = Ptyp_constr ({txt = Longident.Lident "list"}, [t])} ->
    List (ref_of_type t)
  | {ptyp_desc = Ptyp_constr ({txt}, _)} ->
    Named (String.concat "." (Longident.flatten txt))
  | {ptyp_desc = Ptyp_tuple tys} ->
    Tuple (List.map ref_of_type tys)
  | _ -> failwith "Invalid type in reference location of production type"

let branch_of_type = function
  | {pcd_name; pcd_args = Pcstr_tuple ts} ->
    { constructor = pcd_name.txt
    ; params = List.map ref_of_type ts }
  | _ -> failwith "Invalid branch in production type"

let node_of_type = function
  | Ptype_variant branches -> List.map branch_of_type branches
  | _ -> failwith "All productions must be variant types"

let ref_of_opt_type = function
  | None -> failwith "Entry type must be an alias to a core_type"
  | Some ty -> ref_of_type ty

(* Register a type as a part of a language's AST. For example,
   register_type "L0" (type expr = [Int of int | Add of expr * expr])
   stores L0.expr so that it can be extended or used to generate
   subsequent passes automatically. *)
let register_type language ({ptype_name} as ty) =
  let lang =
    match Hashtbl.find_opt languages language with
    | Some lang -> lang
    | None -> { entry = Named "entry"
              ; productions = TypeMap.empty } in
  if ptype_name.txt = "entry" then
    Hashtbl.add languages language
      { lang with entry = ref_of_opt_type ty.ptype_manifest }
  else
    Hashtbl.add languages language
      { lang with productions =
                    TypeMap.add ptype_name.txt (node_of_type ty.ptype_kind) lang.productions }

let update_type language parent ast = ast

let extend_language language parent ast = ast

let new_language language ast =
  let register_types stri =  match stri.pstr_desc with
    | Pstr_type (_, decls) -> List.iter (register_type language) decls
    | _ -> () in
  List.iter register_types ast;
  ast

let gen_language ({pmb_name = {txt = name}; pmb_expr = {pmod_desc = Pmod_structure s} as me} as m) =
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
                             | (Some id, ast) -> extend_language name id ast
                             | (None, ast) -> new_language name ast
                           end } }

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
