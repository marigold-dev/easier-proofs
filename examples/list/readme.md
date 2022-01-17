# Properties for polymorphic list operations

## Length

A length of list is defined in `List.v` as:

```
Definition length {a : Set} (l : myList a) : int :=
  let fix aux (acc : int) (l' : myList a) : int :=
    match l' with
    | Nil => 0
    | Cons el tl => aux (Z.add acc 1) tl
    end in
  aux 0 l.
```

These are some properties:

`Lemma length_zero : forall (A: Set) (l: myList A) <-> length l = 0 -> l = Nil.`

## Append

Appending a list is defined in `List.v` as:

```
Fixpoint append {a : Set} (l : myList a) (d : myList a) : myList a :=
  match l with
  | Nil => d
  | Cons el tl => Cons el (append tl d)
  end.
```

These are the basic properties:

- Concat with nil

```
Lemma app_nil_left: forall (A: Set) (xs: myList A) -> app nil xs = xs.
Lemma app_nil_right: forall (A:Set) (xs:myList A) -> app xs nil = xs.
```

- Length of the append list

```
Lemma length_app: forall (A:Set) (xs ys:myList A) -> length (app xs ys) = length xs + length ys.
```

- Association 

```
Lemma app_assoc: forall (A: Set) (l m n: myList A) -> app (app l n) m = app l (app n m).
```

## In
TODO

## Head and tail

TODO
## Nth element in a list

TODO
## Remove
TODO


<!--
Ideas:
ref: https://www.cs.princeton.edu/courses/archive/fall07/cos595/stdlib/html/Coq.Lists.List.html

Advance by combining with bool and natural numbers
chrome-extension://oemmndcbldboiebfnladdacbdfmadadm/http://www.lix.polytechnique.fr/~barras/mpri/exam2012.pdf
>