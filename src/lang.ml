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


(** convert [Parsetree.core_type] into nanopass type. **)
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
