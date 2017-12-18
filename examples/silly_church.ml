(* From https://github.com/rootmos/silly-church/blob/master/silly-church.scm *)

let is_operator x = List.mem x ["+"; "-"; "*"]
let is_variable x = not (is_operator x)

exception Unknown_operator of string
exception Invalid_variable of string

module%language Lsrc = struct
  type expr =
    [ `Number of int
    | `Op of string * expr * expr
    ]
end

let[@pass Lsrc => Lsrc] check_operators =
  [%passes
    let[@entry] rec expr = function
      | `Op (op, e0 [@r], e1 [@r]) ->
        if is_operator op
          then `Op (op, e0, e1)
          else raise (Unknown_operator op)]

module%language L1 = struct
  include Lsrc

  type expr =
    { del : [ `Number of int ]
    ; add : [ `Var of string
            | `Lambda of string * expr
            | `Apply of expr * expr
            ]
    }
end
let[@pass Lsrc => L1] encode_numbers =
  let rec go = function
    | 0 -> `Var "x"
    | n -> `Apply (`Var "f", go (n - 1)) in
  [%passes
    let[@entry] rec expr = function
      | `Number n ->
        `Lambda ("f",
          `Lambda ("x", go n))]

let[@pass L1 => L1] check_variables =
  [%passes
    let[@entry] rec expr = function
      | `Var var ->
        if is_variable var
          then `Var var
          else raise (Invalid_variable var)
      | `Lambda (var, e [@r]) ->
        if is_variable var
          then `Lambda (var, e)
          else raise (Invalid_variable var)]

module%language L2 = struct
  include L1

  type expr =
    { del : [ `Op of string * expr * expr ]
    ; add : [ `Op of string ]
    }
end

let[@pass L1 => L2] curry_operators =
  [%passes
    let[@entry] rec expr = function
      | `Op (op, e0 [@r], e1 [@r]) ->
        `Apply (`Apply (`Op op, e0), e1)]

module%language L3 = struct
  include L2

  type expr =
    { del : [ `Op of string ] }
end

let[@pass L2 => L3] encode_operators =
  let plus =
    `Lambda ("m",
      `Lambda ("n",
        `Lambda ("f",
          `Lambda ("x",
            `Apply (`Apply (`Var "m", `Var "f"), `Apply (`Apply (`Var "n", `Var "f"), `Var "x")))))) in
  let pred =
    `Lambda ("n",
      `Lambda ("f",
        `Lambda	("x",
          `Apply (`Apply (`Apply (`Var "n",
                                  `Lambda ("g",
                                    `Lambda ("h",
                                      `Apply (`Var "h", `Apply (`Var "g", `Var "f"))))),
                          `Lambda ("u", `Var "x")),
                  `Lambda ("u", `Var "u"))))) in
  let minus =
    `Apply (
      `Lambda ("pred",
        `Lambda ("m",
          `Lambda ("n",
            `Apply (`Apply (`Var "n", `Var "pred"), `Var "m")))),
      pred) in
  let multiply =
    `Lambda ("m",
      `Lambda ("n",
        `Lambda ("f",
          `Apply (`Var "m", `Apply (`Var "n", `Var "f"))))) in
  [%passes
    let[@entry] rec expr = function
      | `Op op ->
        begin match op with
          | "+" -> plus
          | "-" -> minus
          | "*" -> multiply
          | _ -> raise (Unknown_operator op)
        end]

let rec string_of_ast = function
  | `Var v -> v
  | `Apply (e0, e1) -> "(" ^ string_of_ast e0 ^ " " ^ string_of_ast e1 ^ ")"
  | `Lambda (v, e) -> "(lambda (" ^ v ^ ") " ^ string_of_ast e ^ ")"

let encode x =
  x |> encode_numbers |> curry_operators |> encode_operators |> string_of_ast

let () =
  let expr =
    `Op ("+", `Op ("-", `Number 3, `Number 1),
              `Op ("*", `Number 2, `Number 4)) in
  print_endline (encode expr)
