let is_primitive =
  List.mem [ "+"; "-"; "*"; "/"; "cons"; "car"; "cdr"; "pair?"; "vector"
           ; "make-vector"; "vector-length"; "vector-ref"; "vector-set!"
           ; "vector?"; "string"; "make-string"; "string-length"
           ; "string-ref"; "string-set!"; "string?"; "void"]

module%language L0 = struct
  type expr =
    [ `Var of string
    | `Primitive of string
    | `Constant of [`Int of int | `Char of char | `String of string]
    | `Begin of expr list * expr
    | `If1 of expr * expr
    | `If  of expr * expr * expr
    | `Lambda of string list * expr list * expr
    | `Let of (string * expr) list * expr list * expr
    | `Letrec of (string * expr) list * expr list * expr
    | `Apply of expr * expr list
    ]
end

module%language L1 = struct
  include L0

  type expr =
    { del : [ `If1 of expr * expr
            | `Lambda of string list * expr list * expr
            | `Let of (string * expr) list * expr list * expr
            | `Letrec of (string * expr) list * expr list * expr
            ]
    ; add : [ `Lambda of string list * expr
            | `Let of (string * expr) list * expr
            | `Letrec of (string * expr) list * expr
            ]
    }
end

let[@pass L0 => L1] make_explicit =
  [%passes
    let[@entry] rec expr = function
      | `If1 (p [@r], e [@r]) ->
        `If (p, e, `Apply (`Primitive "void", []))
      | `Lambda (xs, bodies [@r] [@l], body [@r]) ->
        `Lambda (xs, `Begin (bodies, body))
      | `Let ((xs, es [@r]) [@l], bodies [@r] [@l], body [@r]) ->
        `Let (List.map2 (fun x e -> (x, e)) xs es, `Begin (bodies, body))
      | `Letrec ((xs, es [@r]) [@l], bodies [@r] [@l], body [@r]) ->
        `Letrec (List.map2 (fun x e -> (x, e)) xs es, `Begin (bodies, body))
  ]

let test_ast =
  `Let (["x", `Constant (`Int 5)],
        [],
        `If1 (`Apply (`Var "equal?", [`Var "x"; `Constant (`Int 6)]),
              `Apply (`Var "print", [`Constant (`String "Hello, world!")])))

let explicit_test_ast =
  `Let (["x", `Constant (`Int 5)],
        `Begin ([],
                `If (`Apply (`Var "equal?", [`Var "x"; `Constant (`Int 6)]),
                     `Apply (`Var "print", [`Constant (`String "Hello, world!")]),
                     `Apply (`Primitive "void", []))))

let () =
  if make_explicit test_ast = explicit_test_ast
    then ()
    else print_endline "make_explicit test failed"
