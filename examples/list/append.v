From Test Require Import CpdtTactics.
(* ----PROOFS---- *)
(* Proofs for append *)
Fact append_neutral_left : forall  (xs:myList a) , app nil xs = xs.
crush.
Qed.
Fact append_neutral_right : forall  (xs:myList a) , app xs nil = xs.
induction xs
crush.
crush.
Qed.