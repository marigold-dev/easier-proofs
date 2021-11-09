open Ast

let parse (lexbuf : Lexing.lexbuf) : program =
  let ast = Parser.prog Lexer.read lexbuf in
  ast

let turnToComment (s : string) : string =
  "(* Proofs for "^s^" *)\n"

let case (n : int) (b : bop) : string =
  let rec case_aux n_ acc = match n_,b with
    | 0,_ -> acc
    | v,Equal -> case_aux (v-1) (acc ^ "-auto.\n")
    | v,Diff -> case_aux (v-1) (acc ^ "-discriminate.\n")
  in case_aux n ""

let determineProperStyle (h : proofs_helper) (b : bop) : string = match h,b with
  | Straight, Equal -> "auto."
  | Straight, Diff -> "discriminate."
  | Case n, b -> "destruct.\n"^(case n b)

let bopToString (b : bop) : string = match b with
  | Equal -> "="
  | Diff -> "<>"

let assertion (a : assertion) : string = match a with
  | ASTAssert (left,b,right) -> left ^" "^ (bopToString b)^ " " ^ right ^".\n"

let arg (a : arg) : string = match a with
  | ASTArg (id,typ) -> " ("^id^":"^typ^") "

let assertion_descr (ad : assertion_descr): string = match ad with
  | ASTAssertD (factName, Some(args), asser) ->
    let args_ = List.map arg args in
    factName ^ ": forall" ^ (String.concat "" args_) ^ ", " ^ (assertion asser)
  | ASTAssertD (factName,_,asser) -> factName^" : "^(assertion asser)


let property (p : property) : string = match p with
  | ASTProp (ass_dec, proofs_helper) -> match ass_dec with
    | ASTAssertD(_,_,ASTAssert(_,b,_)) -> 
      let render = "Fact " ^ assertion_descr ass_dec  in 
      render ^ determineProperStyle proofs_helper b ^ "\nQed."
    

(* nameTarget = the name of the function/thing we want to prove some properties *)
let generatedProofs (p : program) : string = match p with
  | ASTProg (nameTarget, properties) -> 
    let proofs = List.map property properties in
    String.concat "" ((turnToComment nameTarget) :: proofs)

let compile (lexbuf : Lexing.lexbuf) : string =
  lexbuf |> parse |> generatedProofs