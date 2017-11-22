open Ast

(** a type recognized by nanopass; usually a part of a production.
    e.g. [string], [stmt], [(string * expr) list] **)
type np_type =
  | Np_term of core_type      (** external types are "terminals" **)
  | Np_nonterm of string      (** named nonterminal **)
  | Np_tuple of np_type list  (** [t * u * ...] **)
  | Np_list of np_type        (** [t list] **)

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
