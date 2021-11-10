open Ast


exception NotSupportedYet
exception IncoherentHelper of string 

let parse (lexbuf : Lexing.lexbuf) : program =
  let ast = Parser.prog Lexer.read lexbuf in
  ast

let turnToComment (s : string) : string =
  "(* "^s^" *)\n"

let bopToString (b : bop) : string = match b with
  | Equal -> "="
  | Diff -> "<>"

let arg_handle (a : arg) : string = match a with
  | ASTArg (id,typ) -> " ("^id^":"^typ^") "

let case (n : int) (b : bop) : string =
  let rec case_aux n_ acc = match n_,b with
    | 0,_ -> acc
    | v,Equal -> case_aux (v-1) (acc ^ "-auto.\n")
    | v,Diff -> case_aux (v-1) (acc ^ "-discriminate.\n")
  in case_aux n ""

let generateTactics (h : proofs_helper) (b : bop) : string = match h,b with
  | Straight, Equal -> "auto."
  | Straight, Diff -> "discriminate."
  | Case n, b -> "destruct.\n"^(case n b)

let straightTactics (b : bop) : string = match b with
  | Equal -> "auto."
  | Diff -> "discriminate."

(* The most "atomic" proofs without variables *)
let noVarProof (h: proofs_helper) (b : bop) : string = match h with
  | Straight -> straightTactics b ^ "\n" ^ "Qed." ^ "\n"
  | _ -> raise (IncoherentHelper "Can't use a case tactic without variable to case on")

(* Simple proofs with one variable *)
let oneVarProof (h : proofs_helper) (b : bop) (arg : arg) = match h with
  | Straight -> straightTactics b ^ "\n" ^ "Qed." ^ "\n"
  | Case n -> match arg with
              | ASTArg (name,_) -> "destruct "^name^"."^"\n"^(case n b) ^ "Qed." ^ "\n"
(*
  proof_helper -> the annotation which help the generator to find 
  the proper proof style for the assertion

  for now i can generate proof with 0 or 1 variable.
*)
let assertion_annoted_handle (aa : assertion_annoted) : string = match aa with
  | ASTAssertAn (assertionName, Some(args), ASTAssert(left,bop,right), proof_helper) ->
    let headerFact = "Fact "^assertionName^" : forall " in
    let argsCompiled = String.concat "" (headerFact :: (List.map arg_handle args)) in
    let assertCompiled = argsCompiled ^ "," ^ left ^ (bopToString bop) ^ right ^ "." ^ "\n" in
    let proof = match args with
                | [var] -> oneVarProof proof_helper bop var
                | _ -> raise (NotSupportedYet)
    in assertCompiled ^ proof
  | ASTAssertAn (assertionName, None, ASTAssert(left,bop,right), proof_helper) -> 
    let headerFact = "Fact "^assertionName^" : " in
    let assertCompiled = headerFact ^ left ^ (bopToString bop) ^ right ^ "." ^ "\n" in
    assertCompiled ^ (noVarProof proof_helper bop)

(* blockName -> the name of the thing concerned by the proofs (functions etc) *)
let properties_block_handle (pb : properties_block) : string = match pb with
  | ASTPropsBlock (blockName,assertions_annoted) ->
    let headerBlock = turnToComment ("Proofs for "^blockName) in
    let proofs_block = List.map assertion_annoted_handle assertions_annoted in
    String.concat "\n" (headerBlock :: proofs_block)

let program_handle (p : program) : string = match p with
  | ASTProg (properties_blocks) ->
    let header = turnToComment "----PROOFS----" in
    let proofs_blocks = List.map properties_block_handle properties_blocks in
    String.concat "" (header :: proofs_blocks)

let compile (lexbuf : Lexing.lexbuf) : string =
  lexbuf |> parse |> program_handle