open Batteries
open Ast

(** represents a processor definition (a transformation
    between languages, in a pass **)
type np_processor =
  { npc_nonterm : string
  ; npc_loc : Location.t
  ; npc_args : fun_arg list
  ; npc_clauses : (pattern * expression) list }

(** represents a nanopass definition **)
type np_pass =
  { npp_name : string
  ; npp_loc : Location.t
  ; npp_input : Lang.np_language
  ; npp_output : Lang.np_language
  ; npp_pre : expression -> expression
  ; npp_post : expression
  ; npp_procs : np_processor list }

