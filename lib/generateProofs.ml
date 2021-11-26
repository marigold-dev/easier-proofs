open Ast
open Format

exception NotSupportedYet
exception IncoherentHelper of string 
let string_of_bop (b : bop) : string = match b with
| Equality -> "="
| Inequality -> "<>"
| Conjonction -> "/\\"
| Disjonction -> "\\/"

let straight_tactic (fmt : formatter) : unit = fprintf fmt "@[<v 0>crush.@,@]"

let split_tactic (fmt : formatter) : unit = fprintf fmt "@[split.@]@."

let destruct_tactic (fmt : formatter) (var : string): unit = fprintf fmt "@[destruct %s.@]@." var
let induction_tactic (fmt : formatter) (var : string) : unit = fprintf fmt "@[induction %s.@]@." var

let nothing (fmt : formatter) : unit = fprintf fmt ""
let qed (fmt : formatter) : unit = fprintf fmt "@[Qed.@]"

let arg (fmt : formatter) (a : arg) : unit = match a with
  | ASTArg (id,typ) -> fprintf fmt " (%s:%s) " id typ

let case_tactic (fmt : formatter) (n : int) : unit =
  let rec case_aux n_ = match n_ with
    | 0 -> ()
    | v -> straight_tactic fmt; case_aux (v-1)
  in case_aux n

let resolve_proof_style (fmt : formatter) (b : bop) (h : helper) : unit = match b,h with
  | Conjonction,Straight -> split_tactic fmt
  | Disjonction,Left -> fprintf fmt "@[left.@]@."
  | Disjonction,Right -> fprintf fmt "@[right.@]@."
  | (Conjonction | Disjonction),_ -> raise (IncoherentHelper "Unusable helper for conjonction/disjonction")
  | _,h' -> (match h' with
              | Straight -> straight_tactic fmt
              | Case (n,target) -> destruct_tactic fmt target; case_tactic fmt n
              | Induction target -> induction_tactic fmt target; straight_tactic fmt;straight_tactic fmt
              | _ -> raise (IncoherentHelper "left and right are helpers for disjonction only"))

let fact_description (fmt : formatter) (a : assertion) : unit =
  let rec aux fmt' a' = match a' with
    | ASTAtom (cnt) -> fprintf fmt "%s" cnt
    | ASTAssert (bop,left,right,_) -> fprintf fmt' "@[<v 1>%a %s %a@]" aux left (string_of_bop bop) aux right
  in aux fmt a

let in_assertion (fmt : formatter) (a: assertion) : unit =
  let rec aux a' = match a' with
    | ASTAtom (_) -> straight_tactic fmt
    | ASTAssert(Disjonction,left,_,Left) -> resolve_proof_style fmt Disjonction Left; aux left
    | ASTAssert(Disjonction,_,right,Right) -> resolve_proof_style fmt Disjonction Right; aux right
    | ASTAssert (bop,ASTAtom(_),ASTAtom(_),helper) -> resolve_proof_style fmt bop helper
    | ASTAssert (bop,left,right,helper) -> resolve_proof_style fmt bop helper; aux left;aux right
  in aux a

let in_property (fmt : formatter) (aa : prop) : unit = match aa with
  | ASTProp ({assert_name=assert_name';qtf=Some(Forall);args=Some(args');assertt=assertt'}) ->
    fprintf fmt "Fact %s : forall " assert_name';
    pp_print_list arg fmt args';
    fprintf fmt "@[, %a.@]@." fact_description assertt';
    in_assertion fmt assertt'
  | ASTProp ({assert_name=assert_name';qtf=_;args=None;assertt=assertt'}) ->
    fprintf fmt "Fact %s : " assert_name';
    fprintf fmt "@[%a.@]@." fact_description assertt';
    in_assertion fmt assertt'
  | _ -> raise NotSupportedYet

let in_block (fmt : formatter) (pb : block) : unit = match pb with
  | ASTBlock (blockName,props) ->
    fprintf fmt "@[<v 0>(* Proofs for %s *)@,@]" blockName;
    pp_print_list in_property fmt props

let in_blocks (fmt : formatter) (b : blocks ): unit = match b with
  | ASTBlocks (properties_blocks) ->
    fprintf fmt "@[<v 0>From Test Require Import CpdtTactics.@,@]";
    fprintf fmt "@[<v 0>(* ----PROOFS---- *)@,@]";
    pp_print_list in_block fmt properties_blocks; qed fmt

let generate_proof (fmt : formatter ) (program : blocks) : unit =
  fprintf fmt "%a" in_blocks program
