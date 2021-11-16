open Dslprop.DslProp
open Dslprop.GenerateProofs
open Format
let andbtrue_straight =
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
  

let () = 
  if Array.length Sys.argv = 2 then
    let oc = open_out Sys.argv.(1) in
    let oc_formatter = formatter_of_out_channel oc in
    GenProof.compile oc_formatter nat_discriminate_straight;
    pp_print_flush oc_formatter ()
  else
    fprintf err_formatter "target file name missing"