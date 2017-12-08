
(** [fold (x::xs) z f] = [f x (fold xs z f)] **)
let fold l z0 f =
  let rec loop z = function
    | [] -> z
    | x::xs -> loop (f x z) xs
  in loop z0 (List.rev l)
