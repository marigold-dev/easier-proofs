type nat =
  | Zero
  | S of nat

let pred (n : nat) : nat = match n with
  | Zero -> Zero
  | S(p) -> p

let rec add (n : nat) (m : nat) : nat = match n with
  | Zero -> m
  | S p -> S (add p m)

