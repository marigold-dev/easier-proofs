open Dslprop.DslProp
open Dslprop.GenerateProofs
open Format
let my_bool_properties =
  toProofs [
    block "andb" [
      prop_case "andb_true1" ~quantif:forall ~args:(args_ [("b","boolean")]) ("andb Vrai b" =.= "b") straight;
      prop_case "andb_true2" ~quantif:forall ~args:(args_ [("b","boolean")]) ("andb b Vrai" =.= "b") (case 2);
    ];
    block "orb" [
      prop_case "orb_true1" ~quantif:forall ~args:(args_ [("b","boolean")]) ("orb Vrai b" =.= "b") straight;
      prop_case "orb_true2" ~quantif:forall ~args:(args_ [("b","boolean")]) ("orb b Vrai" =.= "b") (case 2);
    ]
  ]
let nat_trivial =
  toProofs [
    block "nat" [
      prop_case "diff42_41" ("42" =!= "41") straight
    ]
  ]

let my_nat_properties =
  toProofs [
    block "add" [
      prop_case "add_0" ~quantif:forall ~args:(args_ [("m","nat")]) ("add Zero m" =.= "m") straight;
      prop_case "add_1" ~quantif:forall ~args:(args_ [("n","nat")]) ("add n Zero" =.= "n") induction;
    ]
  ]
  

let () = 
  if Array.length Sys.argv = 2 then
    let oc = open_out Sys.argv.(1) in
    let oc_formatter = formatter_of_out_channel oc in
    GenProof.compile oc_formatter my_nat_properties;
    pp_print_flush oc_formatter ()
  else
    fprintf err_formatter "target file name missing"