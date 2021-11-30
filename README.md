# easier-proofs
A project which aim to help engineers to make proofs easily

## HOW TO USE IT

A Simple example with a boolean custom type.

First of all, we have this ocaml code.

```ocaml
type boolean = 
  | Vrai
  | Faux

let andb (b1:boolean) (b2: boolean) : boolean = match b1 with
  | Vrai -> b2
  | _ -> Faux

let orb (b1:boolean) (b2:boolean) : boolean = match b1 with
  | Vrai -> Vrai
  | _ -> b2
```

We generate the coq code of this ocaml code with [**Coq-of-ocaml**](https://github.com/foobar-land/coq-of-ocaml).

```coq
Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive boolean : Set :=
| Vrai : boolean
| Faux : boolean.

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
```
Now, we use the DSL for express properties we want to prove about **andb** definition.

This piece of code
```ocaml
toProofs [
    block "andb" [
      prop "andb_true1" ~quantif:forall ~args:(args_ [("b","boolean")]) ((atom "andb b Vrai" =.= atom "b") >> case 2 "b");
      prop "andb_true2" ~quantif:forall ~args:(args_ [("b","boolean")]) ((atom "andb Vrai b" =.= atom "b") >> straight)
    ]
  ]
```
express those assertions : $\forall b:boolean, andb$ $b$ $Vrai = b$ and $\forall b:boolean, andb$ $Vrai$ $b= b$
The hints **case 2 "b"** and **straight** help the generator to know how generate the good proof for a given assertion.

This is the coq proof generated from the ocaml dsl code.

```coq
From Test Require Import CpdtTactics.

(* ----PROOFS---- *)
(* Proofs for andb *)

Fact andb_true1 : forall  (b:boolean) , andb b Vrai = b.
destruct b.
crush.
crush.

Fact andb_true2 : forall  (b:boolean) , andb Vrai b = b.
crush.
Qed.
```

This piece of code
```ocaml
toProofs [
    block "andb" [
      prop "andb_true1" ~quantif:forall ~args:(args_ [("b","boolean")]) 
        ((((atom "andb b Vrai" =.= atom "b") >> case 2 "b") &^ ((atom "andb Vrai b" =.= atom "b") >> straight)))
    ]
  ]
```

express this assertion : $\forall b:boolean, andb$ $b$ $Vrai = b$ $\wedge$ $andb$ $b$ $Vrai = b$
This is the coq proof generated from the ocaml dsl code.

```coq
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
```


## RUN TESTS

"dune build" and "dune exec test/<test_you_want>.exe" or "make", the Makefile will clean, build and run the tests.

## TODO/REPORT
1. Fow now, left and right part of the assertion are string.
2. For now, we specify the number of case at hand for "case" kind of proof. Maybe analyse myself the sum types ?
3. Add more kind of proofs and properties to handle (Monoid, Monad, etc).
4. improve the formatting (indent level for cases sub proofs)
5. lack of documentation
6. lack of tests

## Kind of proofs implemented
1. [DONE] "one shot" proofs for equality and inequality are made (solvable with auto/discriminate).
2. [DONE] "case" simple proofs (one variable) for equality and inequality assertions (solvable with as many auto/discriminate as cases).
3. [DONE] induction simple proofs (one variable).
4. [DONE] multiple variables for simple straight/case/induction proofs added.
5  [DONE] more complexe assertion with conjonction/disjonction.

("?" meaning i think its done but but I didn't have my code reviewed so i don't really know if its done.)