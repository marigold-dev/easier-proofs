open Ast
open Format


exception NotSupportedYet
exception IncoherentHelper of string 

let parse (lexbuf : Lexing.lexbuf) : program =
  let ast = Parser.prog Lexer.read lexbuf in
  ast

let bopToString (b : bop) : string = match b with
  | Equal -> "="
  | Diff -> "<>"

let arg_handle (fmt : formatter) (a : arg) : unit = match a with
  | ASTArg (id,typ) -> fprintf fmt " (%s:%s) " id typ

let case (fmt : formatter) (n : int) (b : bop) : unit =
  let rec case_aux n_ = match n_,b with
    | 0,_ -> ()
    | v,Equal -> fprintf fmt "@[-auto.@]"; case_aux (v-1)
    | v,Diff -> fprintf fmt "@[-discriminate.@]"; case_aux (v-1)
  in case_aux n

let straightTactics (fmt : formatter) (b : bop) : unit = match b with
  | Equal -> fprintf fmt "@[<v 0>auto.@,@]"
  | Diff -> fprintf fmt "@[<v 0>discriminate.@,@]"

(* The most "atomic" proofs without variables *)
let noVarProof (fmt : formatter) (h: proofs_helper) (b : bop) : unit = match h with
  | Straight -> straightTactics fmt b; fprintf fmt "@[Qed.@]"
  | _ -> raise (IncoherentHelper "Can't use a case tactic without variable to case on")

(* Simple proofs with one variable *)
let oneVarProof (fmt : formatter ) (h : proofs_helper) (b : bop) (arg : arg)  : unit = match h with
  | Straight -> straightTactics fmt b; fprintf fmt "@[Qed.@]"
  | Case n -> match arg with
              | ASTArg (name,_) -> fprintf fmt "@[destruct %s@]" name;case fmt n b; fprintf fmt "@[Qed.@]"
(*
  proof_helper -> the annotation which help the generator to find 
  the proper proof style for the assertion

  for now I can generate proof with 0 or 1 variable.
*)
let assertion_annoted_handle (fmt : formatter) (aa : assertion_annoted) : unit = match aa with
  | ASTAssertAn ({assertName=assertionName;args=Some(args);assertt=ASTAssert(left,bop,right);ph=proof_helper}) ->
    fprintf fmt "Fact %s : forall " assertionName;
    pp_print_list arg_handle fmt args;
    fprintf fmt "@[<v>, %s %s %s.@,@]" left (bopToString bop) right;
    (match args with
      | [var] -> oneVarProof fmt proof_helper bop var
      | _ -> raise (NotSupportedYet))
  | ASTAssertAn ({assertName=assertionName;args=_;assertt=ASTAssert(left,bop,right);ph=proof_helper}) ->
    fprintf fmt "Fact %s : " assertionName;
    fprintf fmt "@[<v>, %s %s %s.@,@]" left (bopToString bop) right;
    noVarProof fmt proof_helper bop

(* blockName -> the name of the thing concerned by the proofs (functions etc) *)
let properties_block_handle (fmt : formatter) (pb : properties_block) : unit = match pb with
  | ASTPropsBlock (blockName,assertions_annoted) ->
    fprintf fmt "@[<v 0>(* Proofs for %s *)@,@]" blockName;
    pp_print_list assertion_annoted_handle fmt assertions_annoted

let program_handle (fmt : formatter) (b : program ): unit = match b with
  | ASTProg (properties_blocks) ->
    fprintf fmt "@[<v 0>(* ----PROOFS---- *)@,@]";
    pp_print_list properties_block_handle fmt properties_blocks

(* all this process is parametrize by the formatter, very elegant*)
let compile (fmt : formatter ) (lexbuf : Lexing.lexbuf) : unit =
  lexbuf |> parse |> program_handle fmt