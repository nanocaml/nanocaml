open Batteries
open Ast

(** a type recognized by nanopass; usually a part of a production.
    e.g. [string], [stmt], [(string * expr) list] **)
type np_type =
  | NPtype_term of core_type      (** external types are "terminals" **)
  | NPtype_nonterm of string      (** named nonterminal **)
  | NPtype_tuple of np_type list  (** [t * u * ...] **)
  | NPtype_list of np_type        (** [t list] **)

(** a production is one of the forms in a nonterminal -- essentially
    just a variant, e.g. [`Var], [`App]. **)
type np_production =
  { npp_name : string
  ; npp_args : np_type list }

(** a nonterminal is a type defined by a nanopass language, e.g.
    [expr], [stmt]. **)
type np_nonterm =
  { npnt_name : string
  ; npnt_productions : np_production list }

(** a nanopass language, e.g. L0, L1 (as traditionally named) **)
type np_language =
  { npl_loc : Location.t
  ; npl_name : string
  ; npl_nonterms : np_nonterm list (* TODO: hash tbl? *)
  }


(** global table of all defined languages.
    TODO: nv wants to make this into a real database,
      which would allow caching, cross-file nanopass, etc. **)
let languages : (string, np_language) Hashtbl.t
  = Hashtbl.create 30


(** returns the language with the given name. raises
    [Not_found] if no such language has been defined. **)
let find_language ?(exn=Not_found) name =
  Option.get_exn
    (Hashtbl.find_option languages name)
    exn

(** [language_nonterm l ~name] returns the nonterminal
    in language [l] with the given name. raises [Not_found]
    if no such nonterminal. *)
let language_nonterm ?(exn=Not_found) lang ~name =
  List.find_exn
    (fun nt -> nt.npnt_name = name)
    exn lang.npl_nonterms



(** convert [core_type] into nanopass type. **)
let type_of_core_type ~nt_names t =
  let rec cvt ptyp =
    match ptyp.ptyp_desc with
    (* nonterminal: *)
    | Ptyp_constr ({txt = Longident.Lident name}, [])
         when List.mem name nt_names ->
       NPtype_nonterm name
    (* tuple: *)
    | Ptyp_tuple typs ->
       let npts = List.map cvt typs in
       if npts |> List.for_all (function | NPtype_term _ -> true | _ -> false) then
         NPtype_term ptyp (* [<term> * <term>] is a terminal *)
       else
         NPtype_tuple npts
    (* list: *)
    | Ptyp_constr ({txt = Longident.Lident "list"}, [elem]) ->
       begin match cvt elem with
       | NPtype_term _ -> NPtype_term ptyp (* [<term> list] is a terminal, not a list *)
       | npt -> NPtype_list npt
       end
    (* otherwise, it's a terminal: *)
    | _ ->
       NPtype_term ptyp
  in
  cvt t

(** convert [row_field] (from polymorphic variant) into nanopass production **)
let production_of_row_field ~nt_names =
  function
  | Rtag (name, _, _, args) ->
     {npp_name = name;
      npp_args = List.map (type_of_core_type ~nt_names) args}

  | Rinherit {ptyp_loc = loc} ->
     Location.raise_errorf ~loc
       "invalid nanopass production form"

(** convert [type_declaration] into nanopass nonterminal **)
let nonterm_of_type_decl ~nt_names =
  function
  | {ptype_name = {txt = name};
     ptype_params = [];
     ptype_kind = Ptype_abstract;
     ptype_manifest = Some {ptyp_desc = Ptyp_variant (rows, Closed, _)}}
    ->
     let prods = List.map (production_of_row_field ~nt_names) rows in
     {npnt_name = name;
      npnt_productions = prods}

  | {ptype_loc = loc} ->
     Location.raise_errorf ~loc
       "invalid nanopass type declaration form"

(** convert [module_binding] into nanopass language **)
let language_of_module =
  function
  | {pmb_name = {txt = name};
     pmb_loc = loc;
     pmb_expr =
       {pmod_desc =
          Pmod_structure
            [ {pstr_desc = Pstr_type (Recursive, type_decls)} ]}}
    ->
     let nt_names = List.map (fun {ptype_name = {txt}} -> txt) type_decls in
     let nonterms = List.map (nonterm_of_type_decl ~nt_names) type_decls in
     {npl_loc = loc;
      npl_name = name;
      npl_nonterms = nonterms}

  | {pmb_name = {txt = name};
     pmb_loc = loc;
     pmb_expr =
       {pmod_desc =
          Pmod_structure
            [ {pstr_desc =
                 Pstr_include
                   {pincl_mod =
                      {pmod_desc =
                         Pmod_ident {txt = Lident ext_lang_name}}}};
              {pstr_desc = Pstr_type (Recursive, type_decls)} ]}}
    ->
     let ext_lang =
       find_language
         ~exn:(Location.Error
                 (Location.errorf ~loc
                    "language %S has not been defined" ext_lang_name))
         ext_lang_name
     in

     let nt_names = List.map (fun {ptype_name = {txt}} -> txt) type_decls in
     let nt_names' = List.map (fun {npnt_name} -> npnt_name) ext_lang.npl_nonterms in
     let nonterms =
       List.map (nonterm_of_type_decl
                   ~nt_names:(nt_names @ nt_names'))
         type_decls
     in
     let nonterms' =
       List.filter_map (fun name ->
           if List.mem name nt_names then
             None
           else
             Some (language_nonterm ext_lang name))
         nt_names'
     in
     {npl_loc = loc;
      npl_name = name;
      npl_nonterms = nonterms @ nonterms'}

  | {pmb_loc = loc} ->
     Location.raise_errorf ~loc
       "invalid nanopass language form"
