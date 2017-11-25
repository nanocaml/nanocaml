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
let processor_of_rhs ~name ?(nonterm=name) ~loc e0 =
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
   npc_nonterm = nonterm;
   npc_loc = loc;
   npc_args = args;
   npc_clauses = cases}


(** extract [L0] and [L1] out of expression of form [L0 --> L1].
    returns "L0", loc_L0, "L1", loc_L1 (for this particular example). **)
let extract_pass_sig = function
  | {pexp_desc =
       Pexp_apply
         ({pexp_desc = Pexp_ident {txt = Lident "-->"}},
          [ Nolabel, {pexp_desc = Pexp_construct ({txt = Lident l0_name; loc = l0_loc}, None)};
            Nolabel, {pexp_desc = Pexp_construct ({txt = Lident l1_name; loc = l1_loc}, None)} ])}
    ->
     l0_name, l0_loc,
     l1_name, l1_loc

  | {pexp_loc = loc} ->
     Location.raise_errorf ~loc
       "invalid language specification; expected 'LX --> LY'"


(** convert a [value_binding] into a [np_pass] *)
let pass_of_value_binding = function
  | {pvb_pat = {ppat_desc = Ppat_var {txt = name}};
     pvb_loc = loc;
     pvb_expr = e0;
     pvb_attributes = pass_attr::_} ->

     (* parse language from [[@pass L0 --> L1]] *)
     let find_lang l loc =
       Lang.find_language l
         ~exn:(Location.Error
                 (Location.errorf ~loc "language %S has not been defined" l))
     in
     let l0, l1 =
       match snd pass_attr with
       | PStr [ {pstr_desc = Pstr_eval (lang_expr, [])} ] ->
          let l0_name, l0_loc, l1_name, l1_loc = extract_pass_sig lang_expr in
          find_lang l0_name l0_loc,
          find_lang l1_name l1_loc
       | _ ->
          Location.raise_errorf ~loc:(fst pass_attr).loc
            "invalid [@pass] syntax"
     in

     (* convert expression [e] into [f, vbs, body], where
        [vbs] are the value_bindings of the processors, [body]
        is the final expression, and [f] is a function that inserts
        its argument in place of the processors/body. *)
     let rec extract_definitions f =
       function
       | {pexp_desc = Pexp_fun (lbl, dflt, pat, body)} as e ->
          extract_definitions
            (fun e' -> f {e with pexp_desc = Pexp_fun (lbl, dflt, pat, e')})
            body

       | {pexp_desc = Pexp_let (recf, vbs, ({pexp_desc = Pexp_let _} as body))} as e ->
          extract_definitions
            (fun e' -> f {e with pexp_desc = Pexp_let (recf, vbs, e')})
            body

       | {pexp_desc = Pexp_let (Recursive, vbs, body)} ->
          f, vbs, body

       | {pexp_loc = loc} ->
          Location.raise_errorf ~loc
            "let[@pass] must end in recursive let, followed by a single expression"
     in
     let pre, bindings, post = extract_definitions identity e0 in

     (* parse processors from bindings in final letrec *)
     let procs =
       List.map (function
           | {pvb_pat = {ppat_desc = Ppat_var {txt = name}};
              pvb_expr = proc_rhs;
              pvb_loc = loc;
              pvb_attributes = ats}
             ->
              (* TODO: naming scheme for processors;
                 nonterm configurable using attributes? *)
              let nonterm = name in
              Lang.language_nonterm l0 ~name:nonterm
                ~exn:(Location.Error
                        (Location.errorf ~loc
                           "no such nonterminal %S in language %S" nonterm l0.Lang.npl_name))
              |> ignore;
              processor_of_rhs ~name ~nonterm ~loc proc_rhs

           | {pvb_loc = loc} ->
              Location.raise_errorf ~loc
                "invalid processor definition")
         bindings
     in

     {npp_name = name;
      npp_loc = loc;
      npp_input = l0;
      npp_output = l1;
      npp_pre = pre;
      npp_post = post;
      npp_procs = procs}


  | {pvb_loc = loc} ->
     Location.raise_errorf ~loc
       "invalid pass definition"
