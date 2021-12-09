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

let nothing (fmt : formatter) : unit = fprintf fmt "@."
let qed (fmt : formatter) : unit = fprintf fmt "@[Qed.@]@."

let arg fmt = function
  | ASTArg (id,typ) -> fprintf fmt " (%s:%s) " id typ

let case_tactic fmt =
  let rec case_aux = function
    | 0 -> ()
    | v -> straight_tactic fmt; case_aux (v-1)
  in case_aux

let reduce_axiom fmt axiom = fprintf fmt "@[crush. rewrite %s. crush.@]" axiom

(** [standalone_proof fmt binOp helper] handle the "standalone" proofs 
    which dont need auxiliar lemmas to be written, takes a binary operator and a proof helper to determine
    how print the right coq code.**)
let standalone_proof fmt b h = match b,h with
  | Conjonction,Straight -> split_tactic fmt
  | Disjonction,Left -> fprintf fmt "@[left.@]@."
  | Disjonction,Right -> fprintf fmt "@[right.@]@."
  | (Conjonction | Disjonction),_ -> raise (IncoherentHelper "Unusable helper for conjonction/disjonction")
  | _, Straight -> straight_tactic fmt
  | _, Case (n,target) -> destruct_tactic fmt target; case_tactic fmt n
  | _, Induction target -> induction_tactic fmt target; straight_tactic fmt;straight_tactic fmt
  | _ -> raise (IncoherentHelper "left and right are helpers for disjonction only")

(** [with_aux_lemmas_proof fmt lemmas binOp helper] handle the proofs 
    which need auxiliar lemmas to be written, takes a list of lemmas (axioms), a binary operator and a proof helper to determine
    how print the right coq code.**)
let with_aux_lemmas_proof fmt axioms b h = match b,h with
  | _, Induction target -> induction_tactic fmt target; pp_print_list reduce_axiom fmt axioms
  | _,_ -> raise NotSupportedYet

(** [fact_description fmt prop_body] print the body of a "Fact" coq construction with datas contains in a assertion AST.**)
let fact_description fmt =
  let rec aux fmt = function
    | ASTAtom (cnt) -> fprintf fmt "%s" cnt
    | ASTAssert (bop,left,right,_) -> fprintf fmt "@[<v 1>%a %s %a@]" aux left (string_of_bop bop) aux right
  in aux fmt

(** [in_assertion fmt prop_body axioms] determine what kind of proof we have to generate, from if we need auxiliars lemmas
    or not .**)
let in_assertion fmt a axioms =
  let target = if List.length axioms = 0 then standalone_proof fmt else with_aux_lemmas_proof fmt axioms in
  let rec aux = function
    | ASTAtom (_) -> straight_tactic fmt
    | ASTAssert(Disjonction,left,_,Left) -> target Disjonction Left; aux left
    | ASTAssert(Disjonction,_,right,Right) -> target Disjonction Right; aux right
    | ASTAssert (bop,ASTAtom(_),ASTAtom(_),helper) -> target bop helper
    | ASTAssert (bop,left,right,helper) -> target bop helper; aux left;aux right
  in aux a


(** [in_property fmt prop] is the function that show the pipeline of an entire property translation**)
let in_property fmt = function
  | ASTProp ({assert_name=assert_name';qtf=Some(Forall);args=Some(args');assertt=assertt';lemmas_aux=axioms}) ->
    fprintf fmt "Fact %s : forall " assert_name';
    pp_print_list arg fmt args';
    fprintf fmt "@[, %a.@]@." fact_description assertt';
    in_assertion fmt assertt' axioms; qed fmt
  | ASTProp ({assert_name=assert_name';qtf=_;args=None;assertt=assertt';lemmas_aux=axioms}) ->
    fprintf fmt "Fact %s : " assert_name';
    fprintf fmt "@[%a.@]@." fact_description assertt';
    in_assertion fmt assertt' axioms; qed fmt
  | _ -> raise NotSupportedYet

let in_block fmt = function
  | ASTBlock (blockName,props) ->
    fprintf fmt "@[<v 0>(* Proofs for %s *)@,@]" blockName;
    pp_print_list in_property fmt props

let in_blocks fmt = function
  | ASTBlocks (properties_blocks) ->
    fprintf fmt "@[<v 0>From Test Require Import CpdtTactics.@,@]";
    fprintf fmt "@[<v 0>(* ----PROOFS---- *)@,@]";
    pp_print_list in_block fmt properties_blocks

let generate_proof fmt program  =
  fprintf fmt "%a" in_blocks program;fprintf fmt "@[<v 0> (**END OF PROOFS**)@]@."
