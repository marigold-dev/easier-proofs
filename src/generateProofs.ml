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

open Ast
open Format

exception Not_Supported_Yet

exception Incoherent_Helper of string

let string_of_bop (b : bop) : string =
  match b with
  | Equality ->
      "="
  | Inequality ->
      "<>"
  | Conjunction ->
      "/\\"
  | Disjunction ->
      "\\/"
  | Implication ->
      "->"

let straight_tactic (fmt : formatter) : unit = fprintf fmt "crush"

let split_tactic (fmt : formatter) : unit = fprintf fmt "split"

let destruct_tactic (fmt : formatter) (var : string) : unit =
  fprintf fmt "destruct %s" var

let induction_tactic (fmt : formatter) (var : string) : unit =
  fprintf fmt "induction %s" var

let qed (fmt : formatter) : unit = fprintf fmt "@[Qed.@]@.\n"

let arg fmt = function ASTArg (id, typ) -> fprintf fmt " (%s: %s) " id typ

let semicolon fmt = fprintf fmt "; "

let dot fmt = fprintf fmt "@[.@]@."

(** only rewrite hints for now **)
let hint_rewrite fmt target =
  fprintf fmt "#[local] Hint Rewrite %s" target ;
  fprintf fmt "@[.@]"

(** [standalone_proof fmt binOp helper] handle the "standalone" proofs 
    which don't need auxiliary lemmas to be written. 
    It takes a binary operator and a proof helper to determine
    how to print the correct Coq code.**)
let standalone_proof fmt b h =
  match (b, h) with
  | Conjunction, Straight ->
      split_tactic fmt ; dot fmt
  | Disjunction, Left ->
      fprintf fmt "left" ; dot fmt
  | Disjunction, Right ->
      fprintf fmt "right" ; dot fmt
  | (Conjunction | Disjunction), _ ->
      raise (Incoherent_Helper "Unusable helper for conjunction/disjunction")
  | _, Straight ->
      straight_tactic fmt ; dot fmt
  | _, Case target ->
      destruct_tactic fmt target ; semicolon fmt ; straight_tactic fmt ; dot fmt
  | _, Induction target ->
      induction_tactic fmt target ;
      semicolon fmt ;
      straight_tactic fmt ;
      dot fmt
  | _ ->
      raise (Incoherent_Helper "left and right are helpers for disjunction only")

(** [fact_description fmt prop_body] print the body of a "Fact" Coq construction
 with datas contains in an assertion AST.**)
let fact_description fmt =
  let rec aux fmt = function
    | ASTAtom cnt ->
        fprintf fmt "%s" cnt
    | ASTAssert (bop, left, right, _) ->
        fprintf fmt "@[%a %s %a@]" aux left (string_of_bop bop) aux right
  in
  aux fmt

(** [in_assertion fmt prop_body axioms] determine what kind of proof we have to generate,
    and use the hints if there is some.**)
let in_assertion fmt a hints =
  pp_print_list hint_rewrite fmt hints ;
  fprintf fmt "\n" ;
  let rec aux = function
    | ASTAtom _ ->
        straight_tactic fmt
    | ASTAssert (Disjunction, left, _, Left) ->
        standalone_proof fmt Disjunction Left ;
        aux left
    | ASTAssert (Disjunction, _, right, Right) ->
        standalone_proof fmt Disjunction Right ;
        aux right
    | ASTAssert (bop, ASTAtom _, ASTAtom _, helper) ->
        standalone_proof fmt bop helper
    | ASTAssert (bop, left, right, helper) ->
        standalone_proof fmt bop helper ;
        aux left ;
        aux right
  in
  aux a

(** [in_property fmt prop] is the function that show the pipeline of an entire property translation**)
let in_property fmt = function
  | ASTProp
      { assert_name= assert_name'
      ; qtf= Some Forall
      ; args= Some args'
      ; assertt= assertt'
      ; hints } ->
      fprintf fmt "Fact %s : forall" assert_name' ;
      pp_print_list arg fmt args' ;
      fprintf fmt "@[, %a.@]@." fact_description assertt' ;
      in_assertion fmt assertt' hints ;
      qed fmt
  | ASTProp
      {assert_name= assert_name'; qtf= _; args= None; assertt= assertt'; hints}
    ->
      fprintf fmt "Fact %s : " assert_name' ;
      fprintf fmt "@[%a.@]@." fact_description assertt' ;
      in_assertion fmt assertt' hints ;
      qed fmt
  | _ ->
      raise Not_Supported_Yet

let in_block fmt = function
  | ASTBlock (blockName, props) ->
      fprintf fmt "@[<v>(* Proofs for %s *)@,@]" blockName ;
      pp_print_list in_property fmt props

let in_blocks fmt = function
  | ASTBlocks properties_blocks ->
      fprintf fmt
        "\n\n@[<v>(* ---- Proofs generated by easier-proofs ---- *)@]\n" ;
      fprintf fmt "@.@[<v>From Test Require Import CpdtTactics.@,@]" ;
      pp_print_list in_block fmt properties_blocks

let generate_proof fmt program =
  fprintf fmt "%a" in_blocks program ;
  fprintf fmt "@[<v> (**END OF PROOFS**)@]@."
