open Dslprop.DslProp
open Dslprop.GenerateProofs
open Format

let bool_and_expected = fprintf std_formatter
  "From Test Require Import CpdtTactics.
  (* ----PROOFS---- *)
  (* Proofs for my_and *)
  Fact andb_true1 : forall  (b:boolean) , andb Vrai b = b.
  crush.
  Qed.
  Fact andb_true2 : forall  (b:boolean) , andb b Vrai = b.
  destruct b
  crush.
  crush.
  Qed."
let nat_trivial_expected = fprintf std_formatter
  "From Test Require Import CpdtTactics.
  (* ----PROOFS---- *)
  (* Proofs for nat *)
  Fact diff42_41 :  42 <> 41.
  crush.
  Qed."

let nat_add_expected = fprintf std_formatter
  "From Test Require Import CpdtTactics.
  (* ----PROOFS---- *)
  (* Proofs for add *)
  Fact add_0 : forall  (m:nat) , add Zero m = m.
  crush.
  Qed.
  Fact add_1 : forall  (n:nat) , add n Zero = n.
  induction n.
  crush.
  crush.
  Qed."

let bool_and_properties =
  to_proofs [
    block "andb" [
      prop "andb_true1" ~context:(forall [("b","boolean")]) 
        ((((atom "andb b Vrai" =.= atom "b") >> case "b") &^ ((atom "andb Vrai b" =.= atom "b") >> straight)))
    ]
  ]

let nat_trivial =
  to_proofs [
    block "nat" [
      prop "diff42_41" ((atom "42" =!= atom "41") >> straight)
    ]
  ]

let nat_add_properties =
  to_proofs [
    block "add" [
      prop "add_0" ~context:(forall [("m","nat")]) ((atom "add Zero m" =.= atom "m") >> straight);
      prop "add_1" ~context:(forall [("n","nat")]) ((atom "add n Zero" =.= atom "n") >> induction "n");
    ]
  ]
let test_bool_and () = Alcotest.(check unit) "have to match" bool_and_expected (generate_proof std_formatter bool_and_properties)
let test_nat_inequal () = Alcotest.(check unit) "have to match" nat_trivial_expected (generate_proof std_formatter nat_trivial)

let test_nat_add () = Alcotest.(check unit) "have to match" nat_add_expected (generate_proof std_formatter nat_add_properties)

let () =
  let open Alcotest in
  run "DSL for express assertions and generate proofs on them"
  [
    ("Testing suite for bool/nat properties proofs ",
      [
        test_case "Simple straight and case proof on andb" `Quick test_bool_and;
        test_case "Simple auto proof of an nat inequality" `Quick test_nat_inequal;
        test_case "Simple straight and inductive proofs for add function on nat" `Quick test_nat_add
      ]
    )
  ]