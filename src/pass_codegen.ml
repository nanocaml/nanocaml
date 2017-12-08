open Batteries
open Ast
open Pass
open Lang
module A = Ast_helper

(* general helpers --------------------------------------------------------- *)

module Enum = struct
  include Enum

  (** collects each [x, y] in this enumeration into respective lists [xs, ys]. **)
  let collect2 e =
    let xs, ys =
      Enum.fold (fun (xs, ys) (x, y) -> x::xs, y::ys)
        ([], [])
        e
    in
    List.rev xs, List.rev ys

  (** collects each [x, y, z] in this enumeration into respective lists [xs, ys, zs]. **)
  let collect3 e =
    let xs, ys, zs =
      Enum.fold (fun (xs, ys, zs) (x, y, z) -> x::xs, y::ys, z::zs)
        ([], [], [])
        e
    in
    List.rev xs, List.rev ys, List.rev zs
end

(** [compose_all [f; g; h] x] = [f (g (h x))] **)
let compose_all = function
  | [] -> identity
  | [f] -> f
  | fs -> fun x -> List.fold_right (fun f y -> f y) fs x


(* ocaml ast helpers --------------------------------------------------------- *)

(** convert [string loc] into [Longident.t loc] as just a [Lident]. **)
let lident_of_id (id : string loc) = Location.mkloc (Longident.Lident id.txt) id.loc

(** convert [string loc] into [expr] that is just a [Pexp_ident]. **)
let exp_of_id (id : string loc) = A.Exp.ident ~loc:id.loc (lident_of_id id)

(** generates simple [let x = e1 in e2] expression **)
let simple_let ?(recflag=Asttypes.Nonrecursive) x e1 e2 =
  let loc = x.Asttypes.loc in
  let vb = A.Vb.mk ~loc (A.Pat.var ~loc x) e1 in
  A.Exp.let_ ~loc recflag [ vb ] e2

(** generates simple [let p = e1 in e2] expression **)
let simple_pat_let ?(recflag=Asttypes.Nonrecursive) p e1 e2 =
  let loc = p.ppat_loc in
  let vb = A.Vb.mk ~loc p e1 in
  A.Exp.let_ ~loc recflag [ vb ] e2

(** generate fresh [string loc] using the given [int ref]. *)
let fresh ~next_id ~loc =
  let i = !next_id in
  next_id := i + 1;
  ({txt = Printf.sprintf "np tmp_id%d" i; loc} : string loc)


(* nanopass ast helpers --------------------------------------------------------- *)

(** finds all the variables mentioned in the given pattern. returns
    a list of their names only, sorted alphabetically. *)
let vars_of_pattern pat0 : string list =
  let open Set.String in
  let rec trav vrs = function
    | NPpat_any _ -> vrs
    | NPpat_var {txt = x} -> add x vrs
    | NPpat_alias (pat, {txt = x}) -> trav (add x vrs) pat
    | NPpat_tuple (pats, _) -> List.fold_left trav vrs pats
    | NPpat_variant (_, None, _) -> vrs
    | NPpat_variant (_, Some pat, _) -> trav vrs pat
    | NPpat_map pat -> trav vrs pat
    | NPpat_cata (pat, _) -> trav vrs pat
  in
  Set.String.to_list (trav empty pat0)


(* library --------------------------------------------------------- *)

module Lib_ast = struct
  open Longident
  let fold_lid = Ldot (Ldot (Lident "Nanocaml", "Lib"), "fold")
  let map_lid = Ldot (Ldot (Lident "Nanocaml", "Lib"), "map")

  (** generates expression of the form [fold l z0 (fun x z -> e)]. **)
  let fold_exp ~loc list_exp init_exp elem_pat acc_pat body_exp =
    A.Exp.apply ~loc (A.Exp.ident ~loc {txt = fold_lid; loc})
      [ Nolabel, list_exp;
        Nolabel, init_exp;
        Nolabel, A.Exp.fun_ ~loc Nolabel None elem_pat
                   (A.Exp.fun_ ~loc Nolabel None acc_pat
                      body_exp) ]

  (** generates expression of the form [map l (fun p -> e)]. **)
  let map_exp ~loc list_exp elem_pat body_exp =
    A.Exp.apply ~loc (A.Exp.ident ~loc {txt = map_lid; loc})
      [ Nolabel, list_exp;
        Nolabel, A.Exp.fun_ ~loc Nolabel None elem_pat body_exp ]
end


(* codegen begins here --------------------------------------------------------- *)

(** given an unconditional pattern, converts it to an equivalent parsetree pattern. *)
let rec gen_simple_pat = function
  | NPpat_any loc -> A.Pat.any ~loc ()
  | NPpat_var id -> A.Pat.var ~loc:id.loc id
  | NPpat_alias (pat, id) -> A.Pat.alias ~loc:id.loc (gen_simple_pat pat) id
  | NPpat_tuple (pats, loc) -> A.Pat.tuple ~loc (List.map gen_simple_pat pats)
  | pat -> failwith "gen_simple_pat called on non-simple pat"


(** given an [np_pat], returns [p, f], where [p] is the generated
    pattern, and [f] is a function on expressions which introduces
    let bindings around the given expression.

    [~next_id] is a [ref int] used to generate fresh identifies
    if [~bind_as] is [Some <string loc>], the given string will be
    bound to the result of the pattern.
 *)
let rec gen_pattern ~next_id ~bind_as pat =
  let loc = loc_of_pat pat in
  match pat with
  | NPpat_any _ ->
     let p = match bind_as with
       | None -> A.Pat.any ~loc ()
       | Some id -> A.Pat.var ~loc id (* [_ as x] becomes just [x] *)
     in p, identity

  | NPpat_var id ->
     let p0 = A.Pat.var ~loc:id.loc id in
     let p = match bind_as with
       | None -> p0
       | Some id' -> A.Pat.alias ~loc:id.loc p0 id' (* [x as y] = [x as y] *)
     in p, identity

  | NPpat_alias (pat, id) ->
     begin match bind_as with
     | None -> gen_pattern ~next_id ~bind_as:(Some id) pat
     | Some outer_id ->
        (* BEFORE: (p as x) as y -> e
           AFTER: p as x -> let y = x in e *)
        let p, f = gen_pattern ~next_id ~bind_as:(Some id) pat in
        p, f % simple_let outer_id (exp_of_id id)
     end

  | NPpat_tuple (pats, _) ->
     let ps, fs = match bind_as with
       | None ->
          List.enum pats
          |> Enum.map (gen_pattern ~next_id ~bind_as)
          |> Enum.collect2
       | Some id ->
          (* BEFORE: (p,q) as x -> e
             AFTER: (p as t0, q as t1) -> let x = t0, t1 in e *)
          let ps, fs, binds =
            List.enum pats
            |> Enum.map (fun pat ->
                   let bind = fresh ~next_id ~loc in
                   let p, f = gen_pattern ~next_id ~bind_as:(Some bind) pat in
                   p, f, bind)
            |> Enum.collect3
          in
          let tuple_exp = A.Exp.tuple ~loc (List.map exp_of_id binds) in
          ps, fs @ [simple_let id tuple_exp]
     in
     A.Pat.tuple ~loc ps,
     compose_all fs

  | NPpat_variant (lbl, opt_pat, _) ->
     (* TODO: this may be refactor-able, but i'm not sure. *)
     begin match opt_pat, bind_as with
     | None, None ->
        A.Pat.variant ~loc lbl None, identity
     | None, Some id ->
        (* note: we can't just do [`Var as x] because that may cause type errors
           if we're expecting the reinterpret the variant. *)
        A.Pat.variant ~loc lbl None,
        simple_let id (A.Exp.variant ~loc lbl None)
     | Some pat, None ->
        let p, f = gen_pattern ~next_id ~bind_as:None pat in
        A.Pat.variant ~loc lbl (Some p), identity
     | Some pat, Some id ->
        let bind = fresh ~next_id ~loc in
        let p, f = gen_pattern ~next_id ~bind_as:(Some bind) pat in
        A.Pat.variant ~loc lbl (Some p),
        simple_let id (A.Exp.variant ~loc lbl (Some (exp_of_id bind)))
     end

  (* this should never be the case after typeck, but
     in case it is, just ignore the missing catamorphism. *)
  | NPpat_cata (pat, None) ->
     gen_pattern ~next_id ~bind_as pat

  | NPpat_cata (pat, Some cata_exp) ->
     (* BEFORE: (p [@r cata]) -> e
        AFTER: t0 -> let p = cata t0 in e *)
     let cata_tmp = fresh ~next_id ~loc in
     let p, f = gen_pattern ~next_id ~bind_as pat in
     let app_cata_exp = A.Exp.apply ~loc cata_exp
                          [ Nolabel, exp_of_id cata_tmp ] in
     A.Pat.var ~loc cata_tmp,
     simple_pat_let p app_cata_exp

  | NPpat_map pat ->
     (* (x,y) [@l] as z = (x,y) as z [@l] *)
     let pat = match bind_as with
       | None -> pat
       | Some id -> NPpat_alias (pat, id)
     in
     begin match vars_of_pattern pat with
     | [] -> A.Pat.any ~loc (), identity
     | [x] ->
        (* BEFORE: (x,_) [@l] -> e
           AFTER:  t0 -> let x = Lib.map t0 (fun (x,_) -> x) in e *)
        let list_tmp = fresh ~next_id ~loc in
        let x_id : string loc = {txt = x; loc} in
        A.Pat.var ~loc list_tmp,
        simple_let x_id
          (Lib_ast.map_exp ~loc    (* Lib.map *)
             (exp_of_id list_tmp)  (* list_tmp *)
             (gen_simple_pat pat)  (* (fun pat -> *)
             (exp_of_id x_id))     (*   x) *)

     | vars ->
        (* BEFORE: p [@l] -> e
           AFTER:  t0 -> let x,y ... =
                           Lib.fold t0 ([], [] ...)
                             (fun p (xs, ys ...) -> x::xs, y::ys ...)
                         in e *)
        let empty_exp = A.Exp.construct ~loc {txt = Lident "[]"; loc} None in
        let cons_exp e1 e2 = A.Exp.construct ~loc {txt = Lident "::"; loc} (Some (A.Exp.tuple ~loc [ e1; e2 ])) in

        let list_tmp = fresh ~next_id ~loc in
        let acc_tmps = List.map (fun _ -> fresh ~next_id ~loc) vars in

        A.Pat.var ~loc list_tmp,
        simple_pat_let (A.Pat.tuple ~loc (List.map (fun var -> A.Pat.var ~loc {txt = var; loc}) vars))
          (Lib_ast.fold_exp ~loc
             (exp_of_id list_tmp) (* t0 *)
             (A.Exp.tuple ~loc (List.map (const empty_exp) acc_tmps)) (* ([], ...) *)
             (gen_simple_pat pat) (* p *)
             (A.Pat.tuple ~loc (List.map (A.Pat.var ~loc) acc_tmps)) (* (xs, ...) *)
             (A.Exp.tuple ~loc (List.map2 (fun var acc_id ->
                                    cons_exp (* (x::xs, ...) *)
                                      (A.Exp.ident ~loc {txt = Lident var; loc})
                                      (exp_of_id acc_id))
                                  vars acc_tmps)))
     end


(** generate type expression from language and nonterm **)
let typ_of_nonterm ~loc lang nt =
  A.Typ.constr ~loc
    {txt = Ldot (Lident lang.npl_name, nt.npnt_name); loc}
    []

(** generate [value_binding] from [np_processor]. **)
let gen_processor_vb l0 l1 proc =
  let loc = proc.npc_loc in

  (* generate pattern/exprs for clauses *)
  let clause_lhs, clause_rhs =
    List.enum proc.npc_clauses
    |> Enum.map (fun (pat, rhs_exp) ->
           let p_lhs, intro = gen_pattern ~next_id:(ref 0) ~bind_as:None pat in
           p_lhs, intro rhs_exp)
    |> Enum.collect2
  in

  (* generate domain/co-domain type *)
  let dom_typ = typ_of_nonterm ~loc l0 proc.npc_dom in
  let opt_cod_typ = Option.map (typ_of_nonterm ~loc l1) proc.npc_cod in

  (* generate [match arg0 with clause -> rhs ...] *)
  let arg_id : string loc = {txt = "np proc_arg"; loc} in
  let match_expr =
    A.Exp.match_ ~loc (exp_of_id arg_id)
      (List.map2 (fun lhs rhs ->
           {pc_lhs = lhs;
            pc_guard = None;
            pc_rhs = rhs})
         clause_lhs
         clause_rhs)
  in
  (* annotate match expr if co-domain is present *)
  let match_expr = match opt_cod_typ with
    | None -> match_expr
    | Some typ -> A.Exp.constraint_ ~loc match_expr typ
  in
  (* generate [fun arg0 -> match arg0 with ...] *)
  let clauses_fn_expr =
    A.Exp.fun_ ~loc:proc.npc_clauses_loc Nolabel None
      (A.Pat.constraint_ ~loc (A.Pat.var ~loc arg_id) dom_typ) (* annotate domain type *)
      match_expr
  in

  (* [let proc arg ... = function ...] *)
  A.Vb.mk ~loc
    (A.Pat.var ~loc {txt = proc.npc_name; loc})
    (List.fold_right (fun (lbl, dflt, p) body_exp ->
         A.Exp.fun_ ~loc:p.ppat_loc lbl dflt p body_exp)
       proc.npc_args
       clauses_fn_expr)


(** generate [value_binding] from [np_pass]. **)
let gen_pass_vb pass =
  let loc = pass.npp_loc in
  let l0 = pass.npp_input in
  let l1 = pass.npp_output in
  let pre_introducer = pass.npp_pre in
  let proc_vbs = List.map (gen_processor_vb l0 l1) pass.npp_procs in
  A.Vb.mk ~loc
    (A.Pat.var ~loc {txt = pass.npp_name; loc})
    (pre_introducer
       (A.Exp.let_ ~loc Recursive
          proc_vbs
          pass.npp_post))
