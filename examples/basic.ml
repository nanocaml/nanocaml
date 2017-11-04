module%language L0 = struct
  type entry = expr list
  type expr  = [`Int of int | `Plus of expr * expr | `Minus of expr * expr]
end

module%language L1 = struct
  include L0
  type%remove expr = [`Plus of expr * expr]
end

module%language L2 = struct
  include L1
  type%remove expr = [`Int of int | `Minus of expr * expr]
  type%extend expr = [`Result of string]
end

let%pass rewrite_plus : L0.entry -> L1.entry =
  { expr = function
    | `Plus ([%r a], [%r b]) -> `Minus (a, `Minus (`Int 0, b)) }

let%pass eval : L1.entry -> L2.entry =
  let rec compute : L1.expr -> int = function
    | `Int i -> 0
    | `Minus (a, b) -> (compute a) - (compute b) in
  { expr = fun e -> `Result (compute e |> string_of_int) }

let arith program = program |> rewrite_plus |> eval

let () =
  let program =
    `Plus (`Int 5, `Minus (`Int 6, `Int 3)) in
  List.iter (fun `Result r -> print_endline r) (arith program)
