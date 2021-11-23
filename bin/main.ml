open Dslprop.DslProp
open Dslprop.GenerateProofs
open Format
let my_bool_properties =
  toProofs [
    block "andb" [
      prop_case "andb_true1" ~quantif:forall ~args:(args_ [("b","boolean")]) 
        ((((atom "andb b Vrai" =.= atom "b") >> case 2 "b") &^ ((atom "andb Vrai b" =.= atom "b") >> straight)))
    ]
  ]
(*let nat_trivial =
  toProofs [
    block "nat" [
      prop_case "diff42_41" (atom "42" =!= atom "41") straight
    ]
  ]

let my_nat_properties =
  toProofs [
    block "add" [
      prop_case "add_0" ~quantif:forall ~args:(args_ [("m","nat")]) (atom "add Zero m" =.= atom "m") straight;
      prop_case "add_1" ~quantif:forall ~args:(args_ [("n","nat")]) (atom "add n Zero" =.= atom "n") (induction "n");
    ]
  ]

let my_list_properties = 
  toProofs [
    block "append" [
      prop_case "append_neutral_left" ~quantif:forall ~args:(args_ [("a","Set");("xs","myList a")]) (atom "append Nil xs" =.= atom "xs") straight;
      prop_case "append_neutral_right" ~quantif:forall ~args:(args_ [("a","Set");("xs","myList a")]) (atom "append xs Nil" =.= atom "xs") (induction "xs");
    ]
  ]
  *)

let () = 
  if Array.length Sys.argv = 2 then
    let oc = open_out Sys.argv.(1) in
    let oc_formatter = formatter_of_out_channel oc in
    GenProof.compile oc_formatter my_bool_properties;
    pp_print_flush oc_formatter ()
  else
    fprintf err_formatter "target file name missing"