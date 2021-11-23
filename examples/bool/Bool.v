Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.
From Test Require Import CpdtTactics.

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