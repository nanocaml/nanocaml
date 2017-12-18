open OUnit2
(* everything in this file should compile *)
let tt = "expand_tests" >::: []

module%language Lfirst = struct
  type a = [ `A of int * int ]
  and b = [ `B of a | `Bb ]
end

let x : Lfirst.a = `A (1, 2)
let y : Lfirst.b = `B x

module%language Lsecond = struct
  include Lfirst
  type b =
    { del : [ `Bb ]
    ; add : [ `Bc ] }
end


module%language L0 = struct
  type nt = [ `Pairs of (int * string) list ]
end

module%language L1 = struct
  type nt = [ `Lists of (int list * string list) ]
end

                   (*
this currently breaks the PPX, because
  NPpat_cata (NPpat_map ...)
should never be possible. the typeck algorithm (currently
not being called) moves NPpat_cata directly

let[@pass L0 => L1] split nt0 =
  let rec nt = function
    | `Pairs ((x,y) [@l] [@r foo]) -> `Lists (x, y)
  in nt nt0
                    *)

let[@pass L0 => L1] split nt0 =
  let rec nt = function
    | `Pairs ((x,y) [@l]) -> `Lists (x, y)
  in nt nt0
