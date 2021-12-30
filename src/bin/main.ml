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
open Stdio

let my_bool_properties =
  to_proofs
    [
      block
        "andb"
        [
          prop
            "andb_true2"
            ~context:(forall [("b", "boolean")])
            (atom "andb Vrai b" =.= atom "b" >> straight);
          prop
            "andb_true1"
            ~context:(forall [("b", "boolean")])
            (atom "andb b Vrai" =.= atom "b" >> case "b");
          prop
            "andb_true3"
            ~context:(forall [("b", "boolean")])
            (atom "andb b Vrai" =.= atom "b" >> induction "n")
            ~axioms:["andb_true1"; "andb_true2"];
        ];
    ]

let () =
  if Array.length Sys.argv = 2 then
    let filename = Sys.argv.(1) in
    Out_channel.with_file
      ~append:true
      ~fail_if_exists:false
      filename
      ~f:(fun out ->
        let fmt = formatter_of_out_channel out in
        generate_proof fmt my_bool_properties ;
        close_out out)
  else fprintf err_formatter "target file name missing"
