open Dslprop.DslProp
open Dslprop.GenerateProofs
open Format
open Stdio

let my_bool_properties =
  to_proofs [
    block "andb" [
      prop "andb_true2" ~context:(forall [("b","boolean")]) ((atom "andb Vrai b" =.= atom "b") >> straight);
      prop "andb_true1" ~context:(forall [("b","boolean")]) ((atom "andb b Vrai" =.= atom "b") >> case 2 "b");
      prop "andb_true3"
        ~context:(forall [("b","boolean")])
        ((atom "andb b Vrai" =.= atom "b") >> induction "n")
        ~axioms:["andb_true1";"andb_true2"]
    ]
  ]


let () = 
  if Array.length Sys.argv = 2 then
    let filename = Sys.argv.(1) in
    Out_channel.with_file ~append:true ~fail_if_exists:false
    filename ~f:(fun out -> let fmt = formatter_of_out_channel out in
      generate_proof fmt my_bool_properties; close_out out)
  else
    fprintf err_formatter "target file name missing"