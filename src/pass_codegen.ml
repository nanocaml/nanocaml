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


(* ast helpers --------------------------------------------------------- *)

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
  ({txt = Printf.sprintf "np_gen_id%d" i; loc} : string loc)


(* codegen begins here --------------------------------------------------------- *)

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

  | NPpat_cata (pat, Some cata_exp) ->
     (* BEFORE: (p [@r cata]) -> e
        AFTER: t0 -> let p = cata t0 in e *)
     let cata_tmp = fresh ~next_id ~loc in
     let p, f = gen_pattern ~next_id ~bind_as pat in
     let app_cata_exp = A.Exp.apply ~loc cata_exp
                          [ Nolabel, exp_of_id cata_tmp ] in
     A.Pat.var ~loc cata_tmp,
     simple_pat_let p app_cata_exp

  | _ -> failwith "unimplemented pattern"
