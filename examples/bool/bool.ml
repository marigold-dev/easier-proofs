type boolean = 
  | Vrai
  | Faux

let negb (b: boolean) : boolean = match b with
  | Vrai -> Faux
  | Faux -> Vrai

(** 

properties andb {
  andb_true  : andb Vrai b = b.
  andb_true2 : andb b Vrai = b.
} 

**)
let andb (b1:boolean) (b2: boolean) : boolean = match b1 with
  | Vrai -> b2
  | _ -> Faux

let orb (b1:boolean) (b2:boolean) : boolean = match b1 with
  | Vrai -> Vrai
  | _ -> b2