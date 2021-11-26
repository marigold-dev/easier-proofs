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
  | Left | Right (**pour la disjonction**)
type assertion = 
  | ASTAtom of string (** i can prove just True or False in coq, straight by default**)
  | ASTAssert of bop * assertion * assertion * helper


type arg = ASTArg of string * string

type prop_aux = {
  assert_name : string;
  qtf : quant option;
  args : arg list option;
  assertt : assertion;
}

type prop =
  ASTProp of prop_aux

type block =
  ASTBlock of string * prop list

type blocks =
  ASTBlocks of block list