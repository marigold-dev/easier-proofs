type quant = Forall
type bop =
  | Equality
  | Inequality

type assertion = ASTAssert of bop * string * string
type helper = 
  | Straight 
  | Case of int * string option (** si y'a plusieurs variables on précise sur laquelle on va case **)
  | Induction of string
type arg = ASTArg of string * string

type prop_aux = {
  assertName : string;
  qtf : quant option;
  args : arg list option;
  assertt : assertion;
  h : helper
}

type prop =
  ASTProp of prop_aux

type block =
  ASTBlock of string * prop list

type blocks =
  ASTBlocks of block list