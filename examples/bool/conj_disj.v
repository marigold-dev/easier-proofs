From Test Require Import CpdtTactics.
(* ----PROOFS---- *)
(* Proofs for andb *)
Fact andb_true1 : forall  (b:boolean) , andb b Vrai = b /\ andb Vrai b = b.
split.
destruct b.
crush.
crush.
crush.
Qed.