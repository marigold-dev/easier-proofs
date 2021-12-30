# Peano natural number operators

Peano natural number is defined as 

```
Inductive nat : Set :=
| Zero : nat
| S : nat -> nat.
```
It has some properties:

```
Lemma one_succ: 1 = S 0.
Lemma two_succ: 2 = S 1.
```

## Predecessor

The `pred` is defined as:
```
Definition pred (n : nat) : nat :=
  match n with
  | Zero => Zero
  | S p => p
  end.
```

It has some basic properties:

```
Lemma pred_succ (n: nat): pred (S n) = n.
Lemma pred_zero : pred 0 = 0. 
```

## Addition

The addition `add` is defined in `Nat.v` as:

```
Fixpoint add (n : nat) (m : nat) : nat :=
  match n with
  | Zero => m
  | S p => S (add p m)
  end.
```

It has some basic properties:

```
Lemma add_zero_left: forall (a:Set (m:nat) -> add Zero m = m.
Lemma add_zero_right: forall (a:Set) (n:nat) -> add n Zero = n.
Lemma add_succ_right: forall (a:Set) (m n:nat) -> add m (S n) = S (add m n).
```

## Subtraction
TODO

## Multiplication
TODO
