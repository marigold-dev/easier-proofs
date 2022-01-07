
(** The core of easier-proof, the file containing all the functions for generating proof from a program written in our DSL

    In easier proof, we represente assertion with a DSL, a program in this DSL is a list of blocks, each block concern a precise subject, and in
    each block we have one of several property we want to prove. We can express an assertion, and we have to give "helpers" with a property
    for helping easier-proof to determine how to generate the proof of the assertion.

    Watch ast.ml and dslProp.ml for more information about the DSL, the helpers etc....
**)

exception Not_Supported_Yet
exception Incoherent_Helper of string

val string_of_bop : Ast.bop -> string

(**[straight_tactic fmt] the most basic helper in easier-proof, we use straight when we are sure that the assertion we
    want to prove is solvable with one chlipala's crush.*)
val straight_tactic : Format.formatter -> unit

(**[split_tactic fmt]*)
val split_tactic : Format.formatter -> unit

(**[destruct_tactic fmt var]**)
val destruct_tactic : Format.formatter -> string -> unit

(**[induction_tactic fmt var] print the induction tactic on var*)
val induction_tactic : Format.formatter -> string -> unit

(**[qed fmt] print the end of a proof, named "Qed".*)
val qed : Format.formatter -> unit

(**[arg a] print an argument.*)
val arg : Format.formatter -> Ast.arg -> unit

(**[semicolon] print the ltac command ";"*)
val semicolon : Format.formatter -> unit

(**[dot fmt] print a '.', we don't necesseraly use the dot after a coq tactic since we can use the ltac command ";" 
    in order to automate a part of the proof*)
val dot : Format.formatter -> unit

(**[hint_rewrite fmt name]*)
val hint_rewrite : Format.formatter -> string -> unit

(** [standalone_proof fmt binOp helper] handle the "standalone" proofs 
which don't need auxiliary lemmas to be written. 
It takes a binary operator and a proof helper to determine
how to print the correct Coq code.*)
val standalone_proof : Format.formatter -> Ast.bop -> Ast.helper -> unit

(** [fact_description fmt prop_body] print the body of a "Fact" Coq construction
with datas contains in an assertion AST.*)
val fact_description : Format.formatter -> Ast.prop_body -> unit

(** [in_assertion fmt prop_body hints] determine what kind of proof we have to generate,
    and use the hints if there is some.*)
val in_assertion :
    Format.formatter -> Ast.prop_body -> string list -> unit

(** [in_property fmt prop] is the function that show the pipeline of an entire property translation*)
val in_property : Format.formatter -> Ast.prop -> unit

val in_block : Format.formatter -> Ast.block -> unit

(**[in_blocks fmt blocks]*)
val in_blocks : Format.formatter -> Ast.blocks -> unit

(**[generate_proof fmt program]*)
val generate_proof : Format.formatter -> Ast.blocks -> unit


