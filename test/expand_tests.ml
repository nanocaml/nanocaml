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

let z : Lsecond.b = `Bc
