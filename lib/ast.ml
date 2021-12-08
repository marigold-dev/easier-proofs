type quant = Forall
type bop =
  | Equality
  | Inequality
  | Conjonction
  | Disjonction

type helper = 
  | Straight 
  | Case of int * string
  | Induction of string
  | Left | Right

type prop_body = 
  | ASTAtom of string
  | ASTAssert of bop * prop_body * prop_body * helper

type arg = ASTArg of string * string

type prop_context = {
  assert_name : string;
  qtf : quant option;
  args : arg list option;
  assertt : prop_body;
  lemmas_aux : string list;
}

type prop =
  ASTProp of prop_context

type block =
  ASTBlock of string * prop list

type blocks =
  ASTBlocks of block list