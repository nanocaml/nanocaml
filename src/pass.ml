open Batteries
open Ast

type fun_arg = Asttypes.arg_label * expression option * pattern

(** represents a processor definition (a transformation
    between languages, in a pass **)
type np_processor =
  { npc_name : string
  ; npc_nonterm : string
  ; npc_loc : Location.t
  ; npc_args : fun_arg list
  ; npc_clauses : case list }

(** represents a nanopass definition **)
type np_pass =
  { npp_name : string
  ; npp_loc : Location.t
  ; npp_input : Lang.np_language
  ; npp_output : Lang.np_language
  ; npp_pre : expression -> expression
  ; npp_post : expression
  ; npp_procs : np_processor list }


(** convert the RHS of a [let] into a [np_processor]. **)
let processor_of_rhs ~name ~loc e0 =
  let rec get_args acc = function
    | {pexp_desc = Pexp_fun (lbl, dflt, pat, body)} ->
       get_args ((lbl, dflt, pat)::acc) body
    | {pexp_desc = Pexp_function cases } ->
       List.rev acc, cases
    | {pexp_loc = loc} ->
       Location.raise_errorf ~loc
         "processor must end in 'function' expression"
  in
  let args, cases = get_args [] e0 in
  {npc_name = name;
   npc_nonterm = name;
   npc_loc = loc;
   npc_args = args;
   npc_clauses = cases}

