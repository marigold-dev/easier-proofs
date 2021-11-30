open Dslprop.DslProp
open Dslprop.GenerateProofs
open Format
open Stdio

(* let nat_trivial =
  to_proofs [
    block "nat" [
      prop "diff42_41" ((atom "42" =!= atom "41") >> straight)
    ]
  ]
*)
let my_bool_properties =
  to_proofs [
    block "andb" [
      prop "andb_true1" ~quantif:forall ~args:(args_ [("b","boolean")]) ((atom "andb b Vrai" =.= atom "b") >> case 2 "b");
      prop "andb_true2" ~quantif:forall ~args:(args_ [("b","boolean")]) ((atom "andb Vrai b" =.= atom "b") >> straight);
    ];
    block "andb_conj" [
      prop "andb_true_both" ~quantif:forall ~args:(args_ [("b","boolean")]) 
        ((((atom "andb b Vrai" =.= atom "b") >> case 2 "b") &^ ((atom "andb Vrai b" =.= atom "b") >> straight)))
    ]
  ]

let my_nat_properties =
  to_proofs [
    block "add" [
      prop "add_0" ~quantif:forall ~args:(args_ [("m","nat")]) ((atom "add Zero m" =.= atom "m") >> straight);
      prop "add_1" ~quantif:forall ~args:(args_ [("n","nat")]) ((atom "add n Zero" =.= atom "n") >> induction "n");
    ]
  ]

let my_list_properties = 
  to_proofs [
    block "append" [
      prop "append_neutral_left" ~quantif:forall ~args:(args_ [("a","Set");("xs","myList a")]) ((atom "append Nil xs" =.= atom "xs") >> straight);
      prop "append_neutral_right" ~quantif:forall ~args:(args_ [("a","Set");("xs","myList a")]) ((atom "append xs Nil" =.= atom "xs") >> induction "xs");
    ]
  ]



let () = 
  if Array.length Sys.argv = 2 then
    (*let oc = open_out Sys.argv.(1) in
    let oc_formatter = formatter_of_out_channel oc in
    generate_proof oc_formatter my_bool_properties;
    pp_print_flush oc_formatter ();
    close_out oc*)
    let filename = Sys.argv.(1) in
    Out_channel.with_file ~append:true ~fail_if_exists:false
    filename ~f:(fun out -> let fmt = formatter_of_out_channel out in 
      generate_proof fmt my_list_properties; close_out out)

  else
    fprintf err_formatter "target file name missing"