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
      type stmt = [ `Def of (string, expr) list | ... ]
    it expands the pattern
      `Def (defs [@r])
    into
      `Def ( (_, _ [@r expr]) [@l] as defs )

    this way, NPpat_cata is only applied directly to nonterminals (in this case,
    'expr'), which simplifies the generation of code.

    non-exhaustive patterns are not allowed within [@l] or [@r] forms. This is
    because they expand to let definitions that match the inner pattern.
    e.g.
      `Def ([])             ok
      `Var ((x,i) [@r])     ok

      `Def ([] [@r])        bad
         would expand into roughly
           `Def (defs_) ->
             let [] = List.map (fun (x,e) -> ...) defs_ in
                 ^ if this pattern fails, we are fucked

      `Expr (e' [@r], [])   ok   NOTE: if the [] match fails, the cata for e'
                                 will not be called!
         expands into
           `Expr (e_, []) ->
             let e' = expr_of_expr e_ in
 **)
let rec typeck_pass
    ({npp_input = lang;
      npp_procs = procs} as pass) =
  let check_pattern nt_name = function
    | (NPpat_variant (name, _, _) as pat, expr) ->
      let ty = NP_nonterm nt_name in
      (typeck_pat ~pass ty pat, expr)
    | (pat, expr) -> (pat, expr) in
  let make_exhaustive {npc_dom; npc_clauses = clauses; npc_loc = loc} =
    let missing_prods = cross_off npc_dom.npnt_productions clauses in
    let missing_clauses = gen_missing ~pass ~loc missing_prods in
    List.map (check_pattern npc_dom.npnt_name) (clauses @ missing_clauses) in
  { pass with npp_procs = List.map (fun proc -> { proc with npc_clauses = make_exhaustive proc }) procs }

(** returns an [exn] for type errors. **)
(* TODO: better error messages *)
and typeck_err ~loc typ =
  Location.Error
    (Location.errorf ~loc
       "nanopass pattern type mismatch %s" (string_of_type typ))

(** Find all missing productions for a pass *)
and cross_off prods = function
  | [] -> prods
  | (NPpat_any _, _)::_ -> []
  | (NPpat_variant (variant_name, _, _), _)::clauses ->
    let remove name =
      List.remove_if (fun {nppr_name = n} -> n = name) in
    cross_off (remove variant_name prods) clauses
  | _::clauses -> cross_off prods clauses

and gen_missing ~pass ~loc prods =
  let fresh =
    let num = ref 0 in
    fun () ->
      num := !num + 1;
      string_of_int !num in
  let rec gen_clause {nppr_name; nppr_arg} =
    let rec arg_clause = function
      | NP_term core ->
        let name = fresh () in
        let desc = Pexp_ident {txt = Lident name; loc} in
        (NPpat_var {txt = name; loc}, {pexp_desc = desc; pexp_loc = loc; pexp_attributes = []})
      | NP_nonterm nt_name ->
        let name = fresh () in
        (typeck_pat ~pass (NP_nonterm nt_name) (NPpat_cata (NPpat_var {txt = name; loc}, None)),
         {pexp_desc = Pexp_ident {txt = Lident name; loc}; pexp_loc = loc; pexp_attributes = []})
      | NP_tuple tys ->
        let (pats, exprs) = tys |> List.map arg_clause |> List.split in
        (NPpat_tuple (pats, loc), {pexp_desc = Pexp_tuple exprs; pexp_loc = loc; pexp_attributes = []})
      | NP_list (NP_tuple tys) ->
        let (pats, exprs) = tys |> List.map arg_clause |> List.split in
        (typeck_pat ~pass (NP_list (NP_tuple tys)) (NPpat_map (NPpat_tuple (pats, loc))),
        {pexp_desc = Pexp_tuple exprs; pexp_loc = loc; pexp_attributes = [{txt="l"; loc}, PStr []]})
      | NP_list ty ->
        let (pat, expr) = arg_clause ty in
        (typeck_pat ~pass (NP_list ty) (NPpat_map pat),
         {expr with pexp_attributes = [{txt="l"; loc}, PStr []]})
    in
    let construct e =
      {pexp_desc = Pexp_variant (nppr_name, e); pexp_loc = loc; pexp_attributes = []} in
    match nppr_arg with
    | None -> (NPpat_variant (nppr_name, None, loc), construct None)
    | Some arg ->
      let (pat, expr) = arg_clause arg in
      (NPpat_variant (nppr_name, Some pat, loc), construct (Some expr)) in
  List.map gen_clause prods

(** typecheck a single pattern, with the given expected type. if it
    succeeds, returns a pattern that is the same as the given pattern,
    with all empty [@r] patterns filled in with an inferred catamorphism
    function. **)
and typeck_pat ~pass typ pat =
  match pat with
  | NPpat_any _ | NPpat_var _ -> pat

  | NPpat_alias (sub_pat, name) ->
     NPpat_alias (typeck_pat ~pass typ sub_pat, name)

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
            List.map2 (typeck_pat ~pass)
              sub_typs
              sub_pats
          in
          NPpat_tuple (sub_pats', loc)
     | _ -> raise (typeck_err ~loc typ)
     end

  | NPpat_variant (name, arg, loc) ->
     begin match typ with
     | NP_term _ -> pat
     | NP_nonterm nt_name ->
        let arg' = typeck_nonterm ~pass ~loc nt_name name arg in
        NPpat_variant (name, arg', loc)
     | _ -> raise (typeck_err ~loc typ)
     end

  | NPpat_map elem_pat ->
     begin match typ with
     | NP_list elem_typ -> NPpat_map (typeck_pat ~pass elem_typ elem_pat)
     | _ -> raise (typeck_err ~loc:(loc_of_pat elem_pat) typ)
     end

  | NPpat_cata (pat, opt_cata) ->
     begin match typeck_cata ~pass ~loc:(loc_of_pat pat) opt_cata typ pat with
     | `Infer cata ->
        NPpat_cata (pat, Some cata)
     | `Rewrite pat' ->
        typeck_pat ~pass typ pat'
     end

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


(** typechecks a catamorphism pattern, which either infers
    the catamorphism, or rewrites the pattern by moving the
    catamorphism to deeper sub-patterns. **)
and typeck_cata ~pass ~loc opt_cata typ inner_pat =
  (* wraps given pattern with 'as x' if [inner_pat] is a variable *)
  let wrap_pattern pat = match inner_pat with
    | NPpat_any _ -> pat
    | NPpat_var var -> NPpat_alias (pat, var)
    | _ -> raise (typeck_err ~loc typ)
  in
  match typ with
  | NP_nonterm nt_name ->
     if pat_is_conditional inner_pat then
       Location.raise_errorf ~loc
         "catamorphism binding must always succeed"
     else
       let cata =
         Option.default_delayed (fun () ->
             catamorphism ~pass ~loc
               (language_nonterm pass.npp_input nt_name))
           opt_cata
       in
       `Infer cata

  (* ignore [@r] on terminals *)
  | NP_term _ -> `Rewrite inner_pat

  (* if [xs] has list type, then [xs [@r]] = [_ [@r] [@l] as xs] *)
  | NP_list _ ->
     let pat_cata = NPpat_cata (NPpat_any loc, opt_cata) in
     let pat_map = NPpat_map pat_cata in
     `Rewrite (wrap_pattern pat_map)

  (* if [y] has tuple type, then [y [@r]] = [(_ [@r], ...) as y] *)
  | NP_tuple elems ->
     let pat_cata = NPpat_cata (NPpat_any loc, opt_cata) in
     let pat_tuple = NPpat_tuple (List.map (const pat_cata) elems, loc) in
     `Rewrite (wrap_pattern pat_tuple)


(** determines if a pattern is conditional, e.g. it can fail for
    certain values. **)
and pat_is_conditional = function
  | NPpat_any _ -> false
  | NPpat_var _ -> false
  | NPpat_variant _ -> true
  | NPpat_alias (pat, _) -> pat_is_conditional pat
  | NPpat_map pat -> pat_is_conditional pat
  | NPpat_cata (pat, _) -> pat_is_conditional pat
  | NPpat_tuple (pats, _) -> List.exists pat_is_conditional pats


(** generate an appropriate catamorphism function expression for the
    given nonterminal. **)
(* TODO: create a more sophisticated algorithm for choosing catamorphisms *)
and catamorphism ~pass ~loc nonterm =
  match List.filter (fun proc ->
            proc.npc_dom == nonterm
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
