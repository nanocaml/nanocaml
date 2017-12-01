module%language L0 = struct
  type a = [`A of string | `B]
  and  c = [`C of a]
end

module%language L1 = struct
  include L0
  type a = { del : [`B]
           ; add : [`B of c]
           }
end

let[@pass L0 => L1] annotate_b =
  let empty_a = `A "hello" in
  let empty_b = `B (`C empty_a) in
  [%passes
    let[@entry] rec a = function
      | `B -> `B empty_b
    and c = function
      | `C (a [@r]) -> `C a]
