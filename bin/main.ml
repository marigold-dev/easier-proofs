open Dslprop
open Format 
let () =
  if Array.length Sys.argv = 2 then
    let oc = open_out Sys.argv.(1) in
    let oc_formatter = formatter_of_out_channel oc in
    let program = Lexing.from_channel stdin in
    GenerateProofs.compile oc_formatter program;
    pp_print_flush oc_formatter ()
  else
    fprintf err_formatter "target file name missing"