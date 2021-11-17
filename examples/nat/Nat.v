Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.
From Test Require Import CpdtTactics.

Inductive nat : Set :=
| Zero : nat
| S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
  | Zero => Zero
  | S p => p
  end.

Fixpoint add (n : nat) (m : nat) : nat :=
  match n with
  | Zero => m
  | S p => S (add p m)
  end.

Fact add_0 : forall (m:nat), (add Zero m) = m.
  intro m.
  simpl.
  reflexivity.
Qed.

(*on peut pas raisonner par cas sur n, car n peut etre infini*)
Fact add_1 : forall (n:nat), (add n Zero) = n.
  induction n.
  crush.
  crush.
Qed.

Fact add_S2 : forall (m n:nat), (add m (S n)) = S (add m n).
  induction m.
  crush.
  crush.
Qed.


