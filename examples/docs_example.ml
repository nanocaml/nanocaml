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
      | `If1 (p, e [@r]) ->
        `If (p, e, `Apply (`Primitive "void", []))
      | `Lambda (xs, bodies [@r], body [@r]) ->
        `Lambda (xs, `Begin (bodies, body))
      | `Let ((xs, es [@r]) [@l], bodies [@r], body [@r]) ->
        `Let (List.map2 (fun x e -> (x, e)) xs es, `Begin (bodies, body))
      | `Let ((xs, es [@r]) [@l], bodies [@r], body [@r]) ->
        `Letrec (List.map2 (fun x e -> (x, e)) xs es, `Begin (bodies, body))
  ]
