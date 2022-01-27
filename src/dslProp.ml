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
open GenerateProofs
open Format

let args_ l = Some (List.map (fun arg -> ASTArg (fst arg, snd arg)) l)

let forall args = (Some Forall, args_ args)

let case target = Case target

let induction target = Induction target

let straight = Straight

let atom str = ASTAtom str

let prop name ?(context = (None, None)) ?(hints = []) assertt =
  ASTProp
    { assert_name= name
    ; qtf= fst context
    ; args= snd context
    ; assertt
    ; hints= hints }

let run program =
  let fmt = formatter_of_out_channel stdout in
  generate_proof fmt program

let to_proofs blocks = ASTBlocks blocks

let block name asserts = ASTBlock (name, asserts)

let ( =.= ) l r h = ASTAssert (Equality, l, r, h)

let ( =!= ) l r h = ASTAssert (Inequality, l, r, h)

let ( &^ ) l r = ASTAssert (Conjunction, l, r, Straight)

let ( |^ ) l r h = ASTAssert (Disjunction, l, r, h)

let (|->) l r h = ASTAssert (Implication, l,r,h)

let ( >> ) l h = l h
