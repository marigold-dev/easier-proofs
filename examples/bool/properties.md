# Properties for boolean operators

## NEG

The boolean operator `negb` is defined in `Bool.v`:

```
Definition negb (b : boolean) : boolean :=
  match b with
  | True => False
  | False => True
  end.
```

TODO

## AND 

The boolean operator `andb` is defined in `Bool.v`:

```
Definition andb (b1 : boolean) (b2 : boolean) : boolean :=
  match b1 with
  | True => b2
  | _ => False
  end.
```

These are some basic properties:
  
```
Lemma andb_prop (a b: boolean) : andb a b = True -> a = True /\ b = True.
Lemma andb_true_intro (a b: boolean) : a = true /\ b = True -> andb a b = True.
Lemma andb_left (b: boolean) : andb True b = b.
Lemma andb_right (b: boolean) : andb b True = b. 
```

## OR
The boolean operator `orb` is defined in `Bool.v`: 

```
Definition orb (b1 : boolean) (b2 : boolean) : boolean :=
  match b1 with
  | True => True
  | _ => b2
  end.
```

The basic properties or `orb` is similar as `andb`:

```
Lemma orb_prop (a b: boolean) : orb a b = True -> a = True \/ b = True.
Lemma orb_true_intro (a b: boolean) : a = true \/ b = True -> orb a b = True.
Lemma orb_left (b: boolean): orb True b = True.
Lemma orb_right (b: boolean): orb b True = True.
```

## XOR

TODO

## IMPL

TODO