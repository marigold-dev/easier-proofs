open Dslprop

let () =
  let buff = Lexing.from_channel stdin in
  print_string (GenerateProofs.compile buff)