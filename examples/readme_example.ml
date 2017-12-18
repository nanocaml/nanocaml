module%language Scheme0 = struct
  type expr = (* Define all forms of expressions *)
    [ `Var of string
    (* x *)
    | `Let of string * expr * expr
    (* (let (x y) e) *)
    | `Lambda of string * expr
    (* (lambda (x) e) *)
    | `Apply of expr * expr
    (* (f x) *)
    | `Begin of expr list
    (* (begin e ...) *)
    ]
end

module%language SchemeNoLet = struct
  include Scheme0 (* Means that SchemeNoLet extends Scheme0 *)
  type expr =
    { del : [ `Let of string * expr * expr (* Must perfectly match the 
existing production rule *)
            ]
    } (* Nothing to add *)
end

let[@pass Scheme0 => SchemeNoLet (* Declare the type of the pass*)] 
remove_let =
  [%passes (* Start writing the passes over each non-terminal. In this 
case, we only have [expr] *)
    let[@entry] rec expr = function (* [@entry] means that the pass 
function will take an entry and recurse from there *)
      | `Let (id, value [@r] (* [@r] = Recursively apply this pass *), 
body [@r]) -> (* Matches the Scheme0 let expression *)
        `Apply (`Lambda (id, body), value) (* Must be a 
SchemeNoLet-compatible AST *)
  ]

let input_program = (* (let (f (lambda (x) x)) (f f)) *)
  `Let ("f",
    `Lambda ("x", `Var "x"),
    `Apply (`Var "f", `Var "f"))

let expected_result = (* ((lambda (f) (f f)) (lambda (x) x)) *)
  `Apply (`Lambda ("f", `Apply (`Var "f", `Var "f")),
          `Lambda ("x", `Var "x"))

let () =
  let real_result = remove_let input_program in (* Apply the 
transformation to a Scheme0-compatible AST *)
  if real_result = expected_result
    then print_endline "Test passed!"
    else print_endline "Test failed!"
