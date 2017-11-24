open Batteries
open Ast

(** a type recognized by nanopass; usually a part of a production.
    e.g. [string], [stmt], [(string * expr) list] **)
type np_type =
  | NP_term of core_type      (** external types are "terminals" **)
  | NP_nonterm of string      (** named nonterminal **)
  | NP_tuple of np_type list  (** [t * u * ...] **)
  | NP_list of np_type        (** [t list] **)

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
       NP_nonterm name
    (* tuple: *)
    | Ptyp_tuple typs ->
       let npts = List.map cvt typs in
       if npts |> List.for_all (function | NP_term _ -> true | _ -> false) then
         NP_term ptyp (* [<term> * <term>] is a terminal *)
       else
         NP_tuple npts
    (* list: *)
    | Ptyp_constr ({txt = Longident.Lident "list"}, [elem]) ->
       begin match cvt elem with
       | NP_term _ -> NP_term ptyp (* [<term> list] is a terminal, not a list *)
       | npt -> NP_list npt
       end
    (* otherwise, it's a terminal: *)
    | _ ->
       NP_term ptyp
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
let nonterm_of_type_decl ?extending ~nt_names =
  function
  (* type nt = [ `A | `B ... ] *)
  | {ptype_name = {txt = name};
     ptype_params = [];
     ptype_kind = Ptype_abstract;
     ptype_manifest = Some {ptyp_desc = Ptyp_variant (rows, Closed, _)}}
    ->
     let prods = List.map (production_of_row_field ~nt_names) rows in
     {npnt_name = name;
      npnt_productions = prods}

  (* type nt = { add : [ `A ... ] ; del : [ `B ... ] } *)
  | {ptype_name = {txt = name};
     ptype_loc = loc;
     ptype_params = [];
     ptype_kind = Ptype_record decls}
    ->
     let lang =
       Option.get_exn extending
         (Location.Error
            (Location.errorf ~loc "must be extending a language to use this form"))
     in
     let old_nontem =
       language_nonterm lang ~name
         ~exn:(Location.Error
                 (Location.errorf ~loc "no such nonterminal %S in language %S"
                    name lang.npl_name))
     in

     (* get the 'lname' label out of the record, and parse
        the productions contained in the type. *)
     let get_prods lname =
       match List.find_opt
               (fun {pld_name = {txt = x}} -> x = lname)
               decls
       with
       | None -> None
       | Some {pld_type = {ptyp_desc = Ptyp_variant (rows, Closed, _)}} ->
          Some (List.map (production_of_row_field ~nt_names) rows)
       | Some _ ->
          Location.raise_errorf ~loc
            "invalid extended production"
     in

     (* create functions for adding productions / deleting productions
        if the 'add' or 'del' labels are omitted, then nothing is added / removed. *)
     let add =
       Option.map_default
         (fun add_prs -> List.append add_prs)
         identity (* do nothing when [None] *)
         (get_prods "add")
     in
     let del =
       Option.map_default
         (fun del_prs ->
           let keep p = List.for_all (fun p' -> p.npp_name <> p'.npp_name) del_prs in
           List.filter keep)
         identity
         (get_prods "del")
     in

     let prods = old_nontem.npnt_productions |> del |> add in
     {npnt_name = name;
      npnt_productions = prods}

  (* invalid nonterminal *)
  | {ptype_loc = loc} ->
     Location.raise_errorf ~loc
       "invalid nanopass type declaration form"

(** convert [module_binding] into nanopass language **)
let language_of_module =
  function
  (* module L = struct type nt = ... end *)
  (* must be one single recursive type decl *)
  | {pmb_name = {txt = lang_name};
     pmb_loc = loc;
     pmb_expr =
       {pmod_desc =
          Pmod_structure
            [ {pstr_desc = Pstr_type (Recursive, type_decls)} ]}}
    ->
     let nt_names = List.map (fun {ptype_name = {txt}} -> txt) type_decls in
     let nonterms = List.map (nonterm_of_type_decl ~nt_names) type_decls in
     {npl_loc = loc;
      npl_name = lang_name;
      npl_nonterms = nonterms}

  (* module L = struct
       include L'
       type nt = ...
     end *)
  (* must be a single include + a single recursive type decl*)
  | {pmb_name = {txt = lang_name};
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
     (* the language we are extending *)
     let ext_lang =
       find_language ext_lang_name
         ~exn:(Location.Error
                 (Location.errorf ~loc
                    "language %S has not been defined" ext_lang_name))
     in

     (* new nonterminal names *)
     let nt_names = List.map (fun {ptype_name = {txt}} -> txt) type_decls in
     (* old nonterminal names *)
     let nt_names' = List.map (fun {npnt_name} -> npnt_name) ext_lang.npl_nonterms in
     (* new nonterminals *)
     let nonterms =
       List.map (nonterm_of_type_decl
                   ~extending:ext_lang
                   ~nt_names:(nt_names @ nt_names'))
         type_decls
     in
     (* old nonterminals (only the unmodified ones) *)
     let nonterms' =
       List.filter_map (fun name ->
           if List.mem name nt_names then
             None
           else
             Some (language_nonterm ext_lang name))
         nt_names'
     in

     {npl_loc = loc;
      npl_name = lang_name;
      npl_nonterms = nonterms @ nonterms'}

  | {pmb_loc = loc} ->
     Location.raise_errorf ~loc
       "invalid nanopass language form"
