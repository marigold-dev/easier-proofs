# easier-proofs
This project aims to help making proofs easier by providing a DSL which can express assertions and proof. This tool is using the `Coq` Proof Assistance.

## Use easier-proof as a library in your project.

You have to clone easier-proof and install it locally with `opam install .` at the root of the project.
After that you can add "easier_proof" in your dune "librairies" stanza.


## How to use it

The [`crush`](https://github.com/jwiegley/coq-haskell/blob/master/src/Crush.v) custom tactic of [Adam Chlipala](http://adam.chlipala.net/) from certified programming with dependent types is widely use in this project.

Let us consider this simple example with the commutative property of addition on natural numbers.

First of all, we have this OCaml code in a "proof" directory, into your entire project.

```ocaml
type nat =
  | Zero
  | S of nat

let pred (n : nat) : nat = match n with
  | Zero -> Zero
  | S p -> p

let rec add (n : nat) (m : nat) : nat = match n with
  | Zero -> m
  | S p -> S (add p m)
```

We generate the Coq code for this Ocaml code by using the tool [**coq-of-ocaml**](https://github.com/foobar-land/coq-of-ocaml).

```coq
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
```

In order to prove the commutative property of the addition, we have to prove these two lemmas first:
  - n + 0 = n
  - S (x + y) = x + (S y)

We are using the [DSL](https://en.wikipedia.org/wiki/Domain-specific_language) (Domain-specific language) to express properties that we want to prove.

This OCaml code 

```ocaml
open Easier_proof.DslProp


let t = to_proofs [
  block "commutative property of Nat addition" [
    prop "add_right_zero" ~context:(forall [("n","nat")]) ((atom "add n Zero" =.= atom "n") >> induction "n");

    prop "add_s" ~context:(forall [("x","nat");("y","nat")]) ((atom "S (add x y)" =.= atom "add x (S y)") >> induction "x");

    prop "add_commut"
      ~context:(forall [("x","nat");("y","nat")])
      ((atom "add x y" =.= atom "add y x") >> induction "x")
      ~hints:["add_right_zero";"add_s"]
  ]
]

let _ = run t
```
express the two needed lemmas above and the commutative, and run the translation.

The code below is the Coq proof automatically generated from the OCaml DSL code above.

```coq
From Test Require Import CpdtTactics.
(* ----PROOFS---- *)
(* Proofs for commutativity of nat addition *)

Fact add_right_zero : forall  (n:nat) , add n Zero = n.
                                        
induction n;crush.
Qed.

Fact add_s : forall  (x:nat) (y:nat) , S (add x y) = add x (S y).
           
induction x;crush.
Qed.

Fact add_commut : forall  (x:nat) (y:nat) , add x y = add y x.
           
#[local] Hint Rewrite add_right_zero.
#[local] Hint Rewrite add_s.
induction x;crush.
Qed.
 (**END OF PROOFS**)

```

## Documentation

We need to install odoc (> 2.0.0), to build the document do `make; make doc`.

This is a document for private library and it can be found at `_build/default/_doc/_html/<library>`.