(**
    The AST of the DSL we use for express assertion to prove.
    The most important thing to understand are the helpers. A helper in, as its name suggests,
    a way to help easier proof to generate the right proof for a given assertion.

    In our DSL, a program is in a list of blocks, each block is a piece of context where we want to prove things, a block contains one or several assertion we want to prove
    and for each assertion we must give one helper to .. help easier-proof.

*)
type quant = Forall

type bop = Equality | Inequality | Conjunction | Disjunction | Implication

(**
    - Straight -> the easiest way to generate a proof in easier proof, we use this when we know that our assertion can be proved with
                 chlipala's "crush" tactic.
    - Case -> this helper is the case reasoning, the string is the name on the var we want to use the case reasoning. After that, easier proof will
            use "crush" on all cases.
    - Induction -> this helper is the induction reasoning, the string is the name on the var we want to use the case reasoning. After that, easier proof will
            use "crush" on the two cases.
    - Left -> when we have a disjunction we have to choose which part we will prove, in this case it is the left one.
    - Right -> it is the same as "Left", but for the right one.

*)
type helper = Straight | Case of string | Induction of string | Left | Right

type prop_body =
  | ASTAtom of string
  | ASTAssert of bop * prop_body * prop_body * helper

type arg = ASTArg of string * string

type prop_context =
  { assert_name: string
  ; qtf: quant option
  ; args: arg list option
  ; assertt: prop_body
  ; hints: string list }

type prop = ASTProp of prop_context

type block = ASTBlock of string * prop list

type blocks = ASTBlocks of block list
