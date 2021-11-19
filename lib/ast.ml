type quant = Forall
type bop =
  | Equality
  | Inequality
  | Conjonction
  | Disjonction

type assertion = 
  | ASTAtom of string (** i can prove just True or False in coq**)
  | ASTAssert of bop * assertion * assertion

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