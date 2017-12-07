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
  let var_x = NPpat_var id_x in
  let tmp_exp1 = [%expr 1 + 3 * 4] in
  let tmp_exp2 = [%expr 8 * f 9] in
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
        assert_equal (A.Exp.let_ ~loc
                        Asttypes.Nonrecursive
                        [ A.Vb.mk ~loc
                            (A.Pat.var ~loc id_x)
                            tmp_exp1 ]
                        tmp_exp2)
          (simple_let id_x tmp_exp1 tmp_exp2);
        end;

      "gen_pattern(1)" >::
        begin fun _ ->
        assert_equal (A.Pat.any ~loc ()) (fst (gen_pat (NPpat_any loc)));
        assert_equal (A.Pat.var ~loc id_x) (fst (gen_pat ~v:(Some id_x) (NPpat_any loc)));
        assert_equal (A.Pat.var ~loc id_x) (fst (gen_pat var_x));
        assert_equal (A.Pat.alias ~loc (A.Pat.var id_x) id_y) (fst (gen_pat ~v:(Some id_y) var_x))
        end;

      "gen_pattern(2)" >::
        begin fun _ ->
        assert_equal (A.Pat.var ~loc id_x) (fst (gen_pat (NPpat_alias (NPpat_any loc, id_x))));
        (* BEFORE: (x as y) as z *)
        (* AFTER:  x as y -> let z = y in ... *)
        let p, f = gen_pat ~v:(Some id_z) (NPpat_alias (var_x, id_y)) in
        assert_equal (A.Pat.alias ~loc (A.Pat.var id_x) id_y) p;
        assert_equal (simple_let id_z (exp_of_id id_y) tmp_exp1) (f tmp_exp1);
        end;

    ]
