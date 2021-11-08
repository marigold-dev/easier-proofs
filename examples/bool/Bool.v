Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive boolean : Set :=
| Vrai : boolean
| Faux : boolean.

Definition negb (b : boolean) : boolean :=
  match b with
  | Vrai => Faux
  | Faux => Vrai
  end.

Definition andb (b1 : boolean) (b2 : boolean) : boolean :=
  match b1 with
  | Vrai => b2
  | _ => Faux
  end.

Definition orb (b1 : boolean) (b2 : boolean) : boolean :=
  match b1 with
  | Vrai => Vrai
  | _ => b2
  end.

Fact andb_true : forall (b:boolean), (andb Vrai b) = b.
  intro.
  simpl.
  reflexivity.
  Qed.

Fact andb_true2 : forall (b:boolean), (andb b Vrai) = b.
  intro.
  case b.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.

Fact andb_false : forall (b:boolean), (andb Faux b) = Faux.
  intro.
  simpl.
  reflexivity.
  Qed.

Fact andb_false2 : forall (b:boolean), (andb b Faux) = Faux.
  intro.
  case b.
  - auto.
  - auto.
  Qed.
  
Fact orb_true : forall (b:boolean), (orb b Vrai) = Vrai.
  intro.
  case b.
  - auto.
  - auto.
  Qed.

Fact orb_true2 : forall (b:boolean), (orb Vrai b) = Vrai.
  auto.
  Qed.

Fact orb_false : forall (b:boolean), (orb b Faux) = b.
  intro.
  case b.
  - auto.
  - auto.
  Qed.

Fact orb_false2 : forall (b:boolean), (orb Faux b) = b.
  intro.
  simpl.
  reflexivity.
  Qed.


(** Preuves triviales 
1/ les preuves "one shot"
  1/ faisable avec un seul auto : égalité, implication.
  2/ faisable avec un seul disciminate : inégalité.
2/ les preuves "case" de raisonnement par cas
*)

Fact dif : 42 <> 41.
  discriminate.