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
    'expr'), which simplifies the generation of code.

    because catamorphims (and list maps) expand into [let] bindings AFTER a pattern
    is matched, we have to place restrictions on patterns that contain these transfor-
    mations. once one is found, proceeding patterns must not be conditional. e.g. the
    following are rejected:
    - [`Def ( ("x", _) @[l] )] (conditional pattern ["x"] within [[@l]])
    - [`App (fn [@r], [])] (conditional pattern [[]] after [[@r]])
    the following are accepted:
    - [`Int 0] (no [[@r]] or [[@l]])
    - [`Let ( [], e [@r] )] (conditional pattern [[]] before [[@r]])

 **)
let rec typeck_pass
          ({npp_input = lang;
            npp_procs = procs} as pass) =
  pass

(** returns an [exn] for type errors. **)
(* TODO: better error messages *)
and typeck_err ~loc typ =
  Location.Error
    (Location.errorf ~loc
       "nanopass pattern type mismatch")


(** typecheck a single pattern, with the given expected type.
    [~total] is a [bool ref] that should be [false] (default) when the pattern is
    allowed to be conditional, but can be changed to [true] when list maps / catas are
    encountered. **)
and typeck_pat ~pass ?(total=ref false) typ pat =
  let conditional_pattern () =
    if !total then
      Location.raise_errorf ~loc:(loc_of_pat pat)
        "this pattern must always succeed, due to [@l] or [@r] patterns elsewhere"
  in
  match pat with
  | NPpat_any _ | NPpat_var _ -> pat

  | NPpat_alias (sub_pat, name) ->
     NPpat_alias (typeck_pat ~total ~pass typ sub_pat, name)

  | NPpat_tuple (sub_pats, loc) ->
     begin match typ with
     | NP_tuple sub_typs ->
        if List.length sub_typs <> List.length sub_pats then
          Location.raise_errorf ~loc
            "wrong number of tuple arguments; expected %d, found %d"
            (List.length sub_typs)
            (List.length sub_pats)
        else
          let sub_pats' =
            List.map2 (typeck_pat ~total ~pass)
              sub_typs
              sub_pats
          in
          NPpat_tuple (sub_pats', loc)
     | _ -> raise (typeck_err ~loc typ)
     end

  | NPpat_variant (name, arg, loc) ->
     conditional_pattern ();
     (* TODO: single-variant-types should be allowed
        to be recursively destructured (?) *)
     begin match typ with
     | NP_term _ -> pat
     | NP_nonterm nt_name ->
        let arg' = typeck_nonterm ~pass ~loc nt_name name arg in
        NPpat_variant (name, arg', loc)
     | _ -> raise (typeck_err ~loc typ)
     end

  | NPpat p ->
     conditional_pattern ();
     begin match typ with
     | NP_term _ -> pat
     | _ -> raise (typeck_err ~loc:p.ppat_loc typ)
     end

  | _ -> raise (Failure "unimplemented pattern typechecking")

(** typecheck the (optional) argument to a nontermal given [pr_name],
    the name of the production it is associated with. [nt_name] must
    be a valid nonterminal in the input language. *)
and typeck_nonterm ~pass ~loc nt_name pr_name arg =
  let lang = pass.npp_input in
  let nonterm = language_nonterm lang nt_name in
  let arg_typ =
    try
      List.find_map
        (fun {nppr_name = n; nppr_arg = a} ->
          if pr_name = n then Some a
          else None)
        nonterm.npnt_productions
    with Not_found ->
      Location.raise_errorf ~loc
        "nonterminal %S has no production %S" nt_name pr_name
  in
  match arg_typ, arg with
  | Some typ, None -> Location.raise_errorf ~loc
                        "expected argument to production %S" pr_name
  | None, Some pat -> Location.raise_errorf ~loc
                        "unexpected argument to production %S" pr_name
  | None, None -> None
  | Some typ, Some pat -> Some (typeck_pat ~pass typ pat)


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
