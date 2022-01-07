(*****************************************************************************)
(*                                                                           *)
(* Open Source License                                                       *)
(* Copyright (c) 2021     Marigold <contact@marigold.dev>                    *)
(*                                                                           *)
(* Permission is hereby granted, free of charge, to any person obtaining a   *)
(* copy of this software and associated documentation files (the "Software"),*)
(* to deal in the Software without restriction, including without limitation *)
(* the rights to use, copy, modify, merge, publish, distribute, sublicense,  *)
(* and/or sell copies of the Software, and to permit persons to whom the     *)
(* Software is furnished to do so, subject to the following conditions:      *)
(*                                                                           *)
(* The above copyright notice and this permission notice shall be included   *)
(* in all copies or substantial portions of the Software.                    *)
(*                                                                           *)
(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR*)
(* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,  *)
(* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL   *)
(* THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER*)
(* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING   *)
(* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER       *)
(* DEALINGS IN THE SOFTWARE.                                                 *)
(*                                                                           *)
(*****************************************************************************)

open Dslprop.DslProp
open Dslprop.GenerateProofs
open Format

(** Boolean *)
let bool_and_expected =
  fprintf
    std_formatter
    "From Test Require Import CpdtTactics.\n\
    \  (* ----PROOFS---- *)\n\
    \  (* Proofs for my_and *)\n\
    \  Fact andb_true1 : forall  (b:boolean) , andb True b = b.\n\
    \  crush.\n\
    \  Qed.\n\
    \  Fact andb_true2 : forall  (b:boolean) , andb b True = b.\n\
    \  destruct b\n\
    \  crush.\n\
    \  crush.\n\
    \  Qed."

let bool_and_properties =
  to_proofs
    [
      block
        "andb"
        [
          prop
            "andb_true1"
            ~context:(forall [("b", "boolean")])
            (atom "andb b True" =.= atom "b" >> case "b"
            &^ (atom "andb True b" =.= atom "b" >> straight));
        ];
    ]

let test_bool_and () =
  Alcotest.(check unit)
    "have to match"
    bool_and_expected
    (generate_proof std_formatter bool_and_properties)

(** Natural numbers *)

let nat_trivial =
  to_proofs
    [block "nat" [prop "diff42_41" (atom "42" =!= atom "41" >> straight)]]

let nat_trivial_expected =
  fprintf
    std_formatter
    "From Test Require Import CpdtTactics.\n\
    \  (* ----PROOFS---- *)\n\
    \  (* Proofs for nat *)\n\
    \  Fact diff42_41 :  42 <> 41.\n\
    \  crush.\n\
    \  Qed."

let test_nat_inequal () =
  Alcotest.(check unit)
    "have to match"
    nat_trivial_expected
    (generate_proof std_formatter nat_trivial)

let nat_add_properties =
  to_proofs
    [
      block
        "add"
        [
          prop
            "add_0"
            ~context:(forall [("m", "nat")])
            (atom "add Zero m" =.= atom "m" >> straight);
          prop
            "add_1"
            ~context:(forall [("n", "nat")])
            (atom "add n Zero" =.= atom "n" >> induction "n");
        ];
    ]

let nat_add_expected =
  fprintf
    std_formatter
    "From Test Require Import CpdtTactics.\n\
    \  (* ----PROOFS---- *)\n\
    \  (* Proofs for add *)\n\
    \  Fact add_0 : forall  (m:nat) , add Zero m = m.\n\
    \  crush.\n\
    \  Qed.\n\
    \  Fact add_1 : forall  (n:nat) , add n Zero = n.\n\
    \  induction n.\n\
    \  crush.\n\
    \  crush.\n\
    \  Qed."

let test_nat_add () =
  Alcotest.(check unit)
    "have to match"
    nat_add_expected
    (generate_proof std_formatter nat_add_properties)

let () =
  let open Alcotest in
  run
    "DSL for express assertions and generate proofs on them"
    [
      ( "Testing suite for bool/nat properties proofs ",
        [
          test_case "Simple straight and case proof on andb" `Quick test_bool_and;
          test_case
            "Simple auto proof of an nat inequality"
            `Quick
            test_nat_inequal;
          test_case
            "Simple straight and inductive proofs for add function on nat"
            `Quick
            test_nat_add;
        ] );
    ]
