open Ast
open Format

module GenProof = struct
  exception NotSupportedYet
  exception IncoherentHelper of string 
  let bopToString (b : bop) : string = match b with
  | Equality -> "="
  | Inequality -> "<>"
  | Conjonction -> "/\\"
  | Disjonction -> "\\/"

  let straightTactic (fmt : formatter) : unit = fprintf fmt "@[<v 0>crush.@,@]"

  let splitTactic (fmt : formatter) : unit = fprintf fmt "@[split.@]@."

  let destruct (fmt : formatter) (var : string): unit = fprintf fmt "@[destruct %s.@]@." var
  let induction (fmt : formatter) (var : string) : unit = fprintf fmt "@[induction %s.@]@." var

  let nothing (fmt : formatter) : unit = fprintf fmt ""
  let endOfproof (fmt : formatter) : unit = fprintf fmt "@[Qed.@]"

  let arg_handle (fmt : formatter) (a : arg) : unit = match a with
    | ASTArg (id,typ) -> fprintf fmt " (%s:%s) " id typ

  let case_handle (fmt : formatter) (n : int) : unit =
    let rec case_aux n_ = match n_ with
      | 0 -> ()
      | v -> straightTactic fmt; case_aux (v-1)
    in case_aux n

  let induction_handle (fmt : formatter) : unit = straightTactic fmt;straightTactic fmt

  let resolveKindProof (fmt : formatter) (b : bop) (h : helper) : unit = match b,h with
    | Conjonction,Straight -> splitTactic fmt
    | Disjonction,Left -> fprintf fmt "@[left.@]@."
    | Disjonction,Right -> fprintf fmt "@[right.@]@."
    | (Conjonction | Disjonction),_ -> raise (IncoherentHelper "Unusable helper for conjonction/disjonction")
    | _,h' -> (match h' with
                | Straight -> straightTactic fmt
                | Case (n,target) -> destruct fmt target; case_handle fmt n
                | Induction target -> induction fmt target; induction_handle fmt
                | _ -> raise (IncoherentHelper "left and right are helpers for disjonction only"))

  let factName (fmt : formatter) (a : assertion) : unit =
    let rec aux fmt' a' = match a' with
      | ASTAtom (cnt) -> fprintf fmt "%s" cnt
      | ASTAssert (bop,left,right,_) -> fprintf fmt' "@[<v 1>%a %s %a@]" aux left (bopToString bop) aux right
    in aux fmt a
  
  let assertion_handle (fmt : formatter) (a: assertion) : unit =
    let rec aux a' = match a' with
      | ASTAtom (_) -> straightTactic fmt
      | ASTAssert(Disjonction,left,_,Left) -> resolveKindProof fmt Disjonction Left; aux left
      | ASTAssert(Disjonction,_,right,Right) -> resolveKindProof fmt Disjonction Right; aux right
      | ASTAssert (bop,ASTAtom(_),ASTAtom(_),helper) -> resolveKindProof fmt bop helper
      | ASTAssert (bop,left,right,helper) -> resolveKindProof fmt bop helper; aux left;aux right
    in aux a

  let property_handle (fmt : formatter) (aa : prop) : unit = match aa with
    | ASTProp ({assertName=assertionName;qtf=Some(Forall);args=Some(args);assertt=assertt}) ->
      fprintf fmt "Fact %s : forall " assertionName;
      pp_print_list arg_handle fmt args;
      fprintf fmt "@[, %a.@]@." factName assertt;
      assertion_handle fmt assertt
    | ASTProp ({assertName=assertionName;qtf=_;args=None;assertt=assertt}) ->
      fprintf fmt "Fact %s : " assertionName;
      fprintf fmt "@[%a.@]@." factName assertt;
      assertion_handle fmt assertt
    | _ -> raise NotSupportedYet

  (* blockName -> the name of the thing concerned by the proofs (functions etc) *)
  let block_handle (fmt : formatter) (pb : block) : unit = match pb with
    | ASTBlock (blockName,props) ->
      fprintf fmt "@[<v 0>(* Proofs for %s *)@,@]" blockName;
      pp_print_list property_handle fmt props

  let blocks_handle (fmt : formatter) (b : blocks ): unit = match b with
    | ASTBlocks (properties_blocks) ->
      fprintf fmt "@[<v 0>From Test Require Import CpdtTactics.@,@]";
      fprintf fmt "@[<v 0>(* ----PROOFS---- *)@,@]";
      pp_print_list block_handle fmt properties_blocks; endOfproof fmt

  (* all this process is parametrize by the formatter, very elegant*)
  let compile (fmt : formatter ) (program : blocks) : unit =
    fprintf fmt "%a" blocks_handle program
end




