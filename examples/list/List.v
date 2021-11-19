Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.
From Test Require Import CpdtTactics.


Inductive myList (a : Set) : Set :=
| Nil : myList a
| Cons : a -> myList a -> myList a.

Arguments Nil {_}.
Arguments Cons {_}.

Definition length {a : Set} (l : myList a) : int :=
  let fix aux (acc : int) (l' : myList a) : int :=
    match l' with
    | Nil => 0
    | Cons el tl => aux (Z.add acc 1) tl
    end in
  aux 0 l.

Fixpoint append {a : Set} (l : myList a) (d : myList a) : myList a :=
  match l with
  | Nil => d
  | Cons el tl => Cons el (append tl d)
  end.

(* ----PROOFS---- *)
(* Proofs for append *)
Fact append_neutral_left : forall  (a:Set) 
  (xs:myList a) , append Nil xs = xs.
crush.
Qed.

Fact append_neutral_right : forall  (a:Set) 
  (xs:myList a) , append xs Nil = xs.
induction xs.
crush.
crush.
Qed.

Fact and_left : forall (a:Set) (xs:myList a), append Nil xs = xs /\ append xs Nil = xs.
  crush.
  crush.
  induction xs.
  crush.
  crush.
Qed.