module%language L0 = struct
  type expr =
    [ `Variable of string
    | `Primitive of string
    | `Constant of [ `Number of int | `Char of char | `String of string ]
    | `Datum of { d : 'a. 'a }
    | `Begin of expr list * expr
    | `If1 of expr * expr
    | `If2 of expr * expr * expr
    | `Lambda of string list * expr list * expr
    | `Let of (string * expr) list * expr list * expr
    | `Letrec of (string * expr) list * expr list * expr
    | `App of expr * expr list
    ]
  type entry = expr
end

module%language L1 = struct
  include L0
  type%remove expr =
    [ `If1 of expr * expr
    | `Lambda of string list * expr list * expr
    | `Let of (string * expr) list * expr list * expr
    | `Letrec of (string * expr) list * expr list * expr
    ]
  type%extend expr =
    [ `Lambda of string list * expr
    | `Let of (string * expr) list * expr
    | `Letrec of (string * expr) list * expr
    ]
end

let%pass make_explicit : L0.entry -> L1.entry =
  let void = `Primitive "void" in
  { expr = function
    | `If1 ([%r e0], [%r e1]) ->
      `If2 (e0, e1, void)
    | `Lambda (params, [%r body], [%r last]) ->
      `Lambda (params, `Begin (body, last))
    | `Let ((id, [%mr bindings fun (x, e) -> (x, [%r e])], [%r body], [%r last]) ->
      `Let (bindings, `Begin (body, last))
    | `Letrec ((id, [%mr bindings fun (x, e) -> (x, [%r e])], [%r body], [%r last]) ->
      `Letrec (bindings, `Begin (body, last)) }
