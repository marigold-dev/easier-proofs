type 'a myList = 
  | Nil
  | Cons of 'a * 'a myList

let length (l : 'a myList) : int = 
  let rec aux (acc : int) (l' : 'a myList) : int = match l' with
  | Nil -> 0
  | Cons (el,tl) -> aux (acc+1) tl in
  aux 0 l

let rec append (l : 'a myList) (d : 'a myList) : 'a myList = match l with
  | Nil -> d
  | Cons (el,tl) -> Cons (el,append tl d)
