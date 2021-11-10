open Dslprop

let andbtrue_straight_expected = "(* ----PROOFS---- *)\n(* Proofs for andb *)\n\nFact andbTrue1 : forall  (b:boolean) ,andb Vrai b=b.\nauto.\nQed.\n"
let inequal_nat_straight_expected = "(* ----PROOFS---- *)\n(* Proofs for diff *)\n\nFact diff : 42<>41.\ndiscriminate.\nQed.\n"

let andtrue_straight = "property of andb { andbTrue1 (b:boolean) : \"andb Vrai b\" = \"b\" - straight }"
let inequal_nat_straight = "property of diff { diff : \"42\" <> \"41\" - straight }"

(**
I can't test those now as the generation doesn't work yet.

let proof_andbtrue_case = ""
let proof_inequal_case = ""

**)

let test_andbtrue_straight () = Alcotest.(check string) "have to match" andbtrue_straight_expected (GenerateProofs.compile (Lexing.from_string andtrue_straight))
let test_inequal_nat_straight () = Alcotest.(check string) "have to match" inequal_nat_straight_expected (GenerateProofs.compile (Lexing.from_string inequal_nat_straight))

let () =
  let open Alcotest in
  run "DSL for express assertions and generate proofs on them"
  [
    ("Testing suite for most simple proofs",
      [
        test_case "Simple proof of an equality for the & function" `Quick test_andbtrue_straight;
        test_case "Simple proof of an inequality" `Quick test_inequal_nat_straight;
      ]
    );
  ]