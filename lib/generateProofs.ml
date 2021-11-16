open Ast
open Format

module GenProof = struct
  exception NotSupportedYet
  exception IncoherentHelper of string 
  let bopToString (b : bop) : string = match b with
  | Equality -> "="
  | Inequality -> "<>"

  let arg_handle (fmt : formatter) (a : arg) : unit = match a with
    | ASTArg (id,typ) -> fprintf fmt " (%s:%s) " id typ

  let case_handle (fmt : formatter) (n : int) (b : bop) : unit =
    let rec case_aux n_ = match n_,b with
      | 0,_ -> ()
      | v,_ -> fprintf fmt "@[<v 0>crush.@,@]"; case_aux (v-1)
    in case_aux n

  let straightTactics (fmt : formatter) : unit = fprintf fmt "@[<v 0>crush.@,@]"

  (* The most "atomic" proofs without variables *)
  let noVarProof (fmt : formatter) (h: helper) : unit = match h with
    | Straight -> straightTactics fmt; fprintf fmt "@[Qed.@]"
    | _ -> raise (IncoherentHelper "Can't use a case tactic without variable to case on")

  (* Simple proofs with one variable *)
  let oneVarProof (fmt : formatter ) (h : helper) (b : bop) (arg : arg)  : unit = match h with
    | Straight -> straightTactics fmt; fprintf fmt "@[Qed.@]"
    | Case n -> match arg with
                | ASTArg (name,_) -> fprintf fmt "@[destruct %s@]@." name;case_handle fmt n b; fprintf fmt "@[Qed.@]"
  (*
    proof_helper -> the annotation which help the generator to find 
    the proper proof style for the assertion

    for now I can generate proof with 0 or 1 variable.
  *)
  let property_handle (fmt : formatter) (aa : prop) : unit = match aa with
    | ASTProp ({assertName=assertionName;qtf=Some(Forall);args=Some(args);assertt=ASTAssert(bop,left,right);h=proof_helper}) ->
      fprintf fmt "Fact %s : forall " assertionName;
      pp_print_list arg_handle fmt args;
      fprintf fmt "@[<v 1>, %s %s %s.@]@." left (bopToString bop) right;
      (match args with
        | [var] -> oneVarProof fmt proof_helper bop var
        | _ -> raise (NotSupportedYet))
    | ASTProp ({assertName=assertionName;qtf=_;args=None;assertt=ASTAssert(bop,left,right);h=proof_helper}) ->
      fprintf fmt "Fact %s : " assertionName;
      fprintf fmt "@[<v 1> %s %s %s.@]@." left (bopToString bop) right;
      noVarProof fmt proof_helper
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
      pp_print_list block_handle fmt properties_blocks

  (* all this process is parametrize by the formatter, very elegant*)
  let compile (fmt : formatter ) (program : blocks) : unit =
    program |> blocks_handle fmt
end




