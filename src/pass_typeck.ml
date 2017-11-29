open Batteries
open Ast
open Pass
open Lang

(** perform "typechecking" on the clauses in each processor of the pass.
    this checks the patterns against the production signatures, to make sure that
    they are well formed. additionally, it elaborates patterns in the following
    ways:
      1) infers catamorphism expressions
      2) elaborates catamorphisms that aren't applied directly to a nonterminal

    for instance, given the nonterm
      type stmt = [ `Def of (string, expr) list ]
    it expands the pattern
      `Def (defs [@r])
    into
      `Def ( (_, _ [@r expr]) [@l] as defs )

    this way, NPpat_cata is only applied directly to nonterminals (in this case,
    'expr'), which simplifies the generation of code. **)
let rec typeck_pass
          ({npp_input = lang;
            npp_procs = procs} as pass) =
  pass


(** generate an appropriate catamorphism function expression for the
    given nonterminal. **)
(* TODO: create a more sophisticated algorithm for choosing catamorphisms *)
and catamorphism ~loc ~pass nonterm =
  match List.filter (fun proc ->
            proc.npc_nonterm == nonterm
            && List.is_empty proc.npc_args)
          pass.npp_procs
  with
  | [] ->
     (* TODO: autogenerate processors? *)
     Location.raise_errorf ~loc
       "cannot find suitable processor for nonterminal %S" nonterm.npnt_name
  | _::_::_ ->
     Location.raise_errorf ~loc
       "catamorphism for %S is ambiguous due to multiple processors"
       nonterm.npnt_name

  | [proc] ->
     {pexp_desc = Pexp_ident {txt = Lident proc.npc_name; loc};
      pexp_loc = loc;
      pexp_attributes = []}
