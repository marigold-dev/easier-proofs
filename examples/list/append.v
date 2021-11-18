From Test Require Import CpdtTactics.
(* ----PROOFS---- *)
(* Proofs for append *)
Fact append_neutral_left : forall  (a:Set) 
 (xs:myList a) , append Nil xs = xs.
crush.
Qed.Fact append_neutral_right : forall  (a:Set) 
 (xs:myList a) , append xs Nil = xs.
induction xs.
crush.
crush.
Qed.