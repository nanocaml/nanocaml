module L0 = struct
  type entry = expr list
  type expr  = [`Int of int | `Plus of expr * expr | `Minus of expr * expr]
end

module L1 = struct
  type entry = expr list
  type expr = [`Int of int | `Minus of expr * expr]
end

module L2 = struct
  type entry = expr list
  type expr = [`Result of string]
end

let rewrite_plus : L0.entry -> L1.entry =
  let rec entry ast = List.map expr ast
  and expr = function
    | `Plus (a, b) ->
      let a = expr a
      and b = expr b in
      `Minus (a, `Minus (`Int 0, b)) in
  entry

let eval : L1.entry -> L2.entry
  let rec compute : L1.expr -> int = function
    | `Int i -> 0
    | `Minus (a, b) -> (compute a) - (compute b) in
  let rec entry ast = List.map expr ast
  and expr = fun e -> `Result (compute e |> string_of_int) in
  entry

let arith program = program |> rewrite_plus |> eval

let () =
  let program =
    `Plus (`Int 5, `Minus (`Int 6, `Int 3)) in
  List.iter (fun `Result r -> print_endline r) (arith program)
