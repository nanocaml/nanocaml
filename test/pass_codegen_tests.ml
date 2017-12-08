open Batteries
open OUnit2
open Migrate_parsetree
open Ast_405.Parsetree
module A = Ast_405.Ast_helper

let tt =
  let open Nanocaml.Pass in
  let open Nanocaml.Pass_codegen in
  let loc = !A.default_loc in
  let id_x = Location.mkloc "x" loc in
  let id_y = Location.mkloc "y" loc in
  let id_z = Location.mkloc "z" loc in
  let id_tmp0 = fresh (ref 0) loc in
  let id_tmp1 = fresh (ref 1) loc in
  (* let id_tmp2 = fresh (ref 2) loc in
     let id_tmp3 = fresh (ref 2) loc in *)
  let var_x = NPpat_var id_x in
  let var_y = NPpat_var id_y in
  let any = NPpat_any loc in
  let test_exp1 = [%expr foo a b c] in
  let test_exp2 = [%expr 1 + 2 * 3] in
  let gen_pat ?(v=None) p = gen_pattern ~next_id:(ref 0) ~bind_as:v p in
  "pass_codegen" >:::
    [

      "compose_all" >::
        begin fun _ ->
        let eq = assert_equal ~printer:Int.to_string in
        eq 4 (compose_all [] 4);
        eq 4 (compose_all [succ] 3);
        eq 19 (compose_all [succ; ( * ) 3; succ] 5);
        end;

      "simple_let" >::
        begin fun _ ->
        assert_equal (A.Exp.let_
                        Asttypes.Nonrecursive
                        [ A.Vb.mk
                            (A.Pat.var id_x)
                            test_exp1 ]
                        test_exp2)
          (simple_let id_x test_exp1 test_exp2);
        end;

      "vars_of_pattern" >::
        begin fun _ ->
        assert_equal [ id_x; id_y; id_z ] (* alphabetical; sorted from Set.String *)
          (vars_of_pattern ~loc
             (NPpat_tuple ([ var_y;
                             any;
                             NPpat_map (NPpat_variant ("X", Some var_x, loc));
                             NPpat_cata (NPpat_alias (any, id_z), None) ],
                           loc)));
        end;

      "Lib.fold" >::
        begin fun _ ->
        assert_equal "a-bc-d-e"
          (Nanocaml.Lib.fold ["a"; "bc"; "d"] "e"
             (Printf.sprintf "%s-%s"));
        end;

      "fold_exp" >::
        begin fun _ ->
        let l = exp_of_id id_y in
        let z0 = exp_of_id id_z in
        let x = A.Pat.var id_x in
        let z = A.Pat.var id_z in
        let e = test_exp1 in
        assert_equal (A.Exp.apply
                        (A.Exp.ident
                           {txt = Ldot (Ldot (Lident "Nanocaml", "Lib"), "fold"); loc})
                        [ Nolabel, l;
                          Nolabel, z0;
                          Nolabel, A.Exp.fun_ Nolabel None x
                                     (A.Exp.fun_ Nolabel None z e) ])
          (Lib_ast.fold_exp ~loc l z0 x z e);
        end;

      "gen_pattern(1)" >::
        begin fun _ ->
        assert_equal (A.Pat.any ()) (fst (gen_pat any));
        assert_equal (A.Pat.var id_x) (fst (gen_pat ~v:(Some id_x) any));
        assert_equal (A.Pat.var id_x) (fst (gen_pat var_x));
        assert_equal (A.Pat.alias (A.Pat.var id_x) id_y) (fst (gen_pat ~v:(Some id_y) var_x))
        end;

      "gen_pattern(2)" >::
        begin fun _ ->
        (* _ as x  ==>  x *)
        assert_equal (A.Pat.var id_x) (fst (gen_pat (NPpat_alias (any, id_x))));
        (* BEFORE: (x as y) as z -> ee *)
        (* AFTER:  x as y        -> let z = y in ee *)
        let p, f = gen_pat ~v:(Some id_z) (NPpat_alias (var_x, id_y)) in
        assert_equal (A.Pat.alias (A.Pat.var id_x) id_y) p;
        assert_equal (simple_let id_z (exp_of_id id_y) test_exp1) (f test_exp1);
        end;

      "gen_pattern(3)" >::
        begin fun _ ->
        assert_equal (A.Pat.tuple
                        [ A.Pat.var id_x;
                          A.Pat.any () ])
          (fst (gen_pat (NPpat_tuple ([ var_x; any ], loc))));
        (* BEFORE: (x,_) as y           -> ee
           AFTER:  (x as t_0, t_1)      -> let y = t_0, t_1 in ee *)
        let p, f = gen_pat ~v:(Some id_y)
                     (NPpat_tuple ([ var_x; any ], loc)) in
        assert_equal (A.Pat.tuple
                        [ A.Pat.alias (A.Pat.var id_x) id_tmp0;
                          A.Pat.var id_tmp1 ]) p;
        assert_equal (simple_let id_y
                        (A.Exp.tuple [ exp_of_id id_tmp0; exp_of_id id_tmp1 ])
                        test_exp1)
          (f test_exp1);
        end;

      "gen_pattern(4)" >::
        begin fun _ ->
        assert_equal (A.Pat.variant "Z" None) (fst (gen_pat (NPpat_variant ("Z", None, loc))));
        assert_equal (A.Pat.variant "S" (Some (A.Pat.any ())))
          (fst (gen_pat (NPpat_variant ("S", Some any, loc))));
        (* BEFORE: `Z as y -> ee
           AFTER:  `Z      -> let y = `Z in e *)
        let p1, f1 = gen_pat ~v:(Some id_y) (NPpat_variant ("Z", None, loc)) in
        assert_equal (A.Pat.variant "Z" None) p1;
        assert_equal (simple_let id_y (A.Exp.variant "Z" None) test_exp1) (f1 test_exp1);
        (* BEFORE: (`S _) as y -> ee
           AFTER:  `S t_0      -> let y = `S t_0 in ee *)
        let p2, f2 = gen_pat ~v:(Some id_y) (NPpat_variant ("S", Some any, loc)) in
        assert_equal (A.Pat.variant "S" (Some (A.Pat.var id_tmp0))) p2;
        assert_equal (simple_let id_y
                        (A.Exp.variant "S" (Some (exp_of_id id_tmp0)))
                        test_exp2)
          (f2 test_exp2);
        end;

      "gen_pattern(5)" >::
        begin fun _ ->
        (* BEFORE: x [@r test1] -> ee
           AFTER:  t_0          -> let x = test1 t_0 in ee *)
        let p, f = gen_pat (NPpat_cata (var_x, Some test_exp1)) in
        assert_equal (A.Pat.var id_tmp0) p;
        assert_equal (simple_let id_x
                        (A.Exp.apply test_exp1
                           [ Nolabel, exp_of_id id_tmp0 ])
                        test_exp2)
          (f test_exp2);
        end;

    ]
