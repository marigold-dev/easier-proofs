From Test Require Import CpdtTactics.
(* ----PROOFS---- *)
(* Proofs for add *)
Fact add_0 : forall  (m:nat) , add Zero m = m.
crush.
Qed.
Fact add_1 : forall  (n:nat) , add n Zero = n.
induction n
crush.
crush.
Qed.