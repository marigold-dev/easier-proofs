module DL = struct
  type _ t =
    | [] : string t
    | ( :: ) : ('a * 'b t) -> ('a -> 'b) t
end

type quantifier = Forall
type _ binding = Binding : (string * string) -> 'a binding
type ('a, 'b) quantified_binding = quantifier * ('a binding -> 'b) DL.t

type ('a, 'b) fact =
  { name : string
  ; quantifier : ('a, 'b) quantified_binding
  ; block : 'a binding -> 'b
  }

let nat : string -> [ `Nat ] binding = fun x -> Binding ("nat", x)
let forall l = Forall, l
let fact name quantifier block = { name; quantifier; block }

(**exemples of terms*)

let t =
  fact
     ("add_right_zero")
     (forall DL.[ nat "x"; nat "y"; nat "z" ])
     (fun _x _y _z -> "")
;;