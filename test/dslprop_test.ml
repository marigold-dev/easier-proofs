open Dslprop.DslProp
open Dslprop.GenerateProofs
open Format

let andbtrue_1_2_expected = fprintf std_formatter
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
let nat_discriminate_straight_expected = fprintf std_formatter
  "From Test Require Import CpdtTactics.
  (* ----PROOFS---- *)
  (* Proofs for nat *)
  Fact diff42_41 :  42 <> 41.
  crush.
  Qed."

let andtrue_1_2 =
  toProofs [
    block "my_and" [
      prop_case "andb_true1" ~quantif:forall ~args:(args_ [("b","boolean")]) ("andb Vrai b" =.= "b") Straight;
      prop_case "andb_true2" ~quantif:forall ~args:(args_ [("b","boolean")]) ("andb b Vrai" =.= "b") (case 2);
    ]
  ]

let nat_discriminate_straight =
  toProofs [
    block "nat" [
      prop_case "diff42_41" ("42" =!= "41") Straight
    ]
  ]

let test_andbtrue_straight () = Alcotest.(check unit) "have to match" andbtrue_1_2_expected (GenProof.compile std_formatter andtrue_1_2)
let test_inequal_nat_straight () = Alcotest.(check unit) "have to match" nat_discriminate_straight_expected (GenProof.compile std_formatter nat_discriminate_straight)

let () =
  let open Alcotest in
  run "DSL for express assertions and generate proofs on them"
  [
    ("Testing suite for andb function ",
      [
        test_case "Simple straight and case proof on andb" `Quick test_andbtrue_straight;
        test_case "Simple auto proof of an natinequality" `Quick test_inequal_nat_straight;
      ]
    )
  ]