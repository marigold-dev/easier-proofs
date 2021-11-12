type bop =
  | Equal
  | Diff

type arg = ASTArg of string * string
type proofs_helper = Straight | Case of int
type assertion = ASTAssert of string * bop * string
type assertion_aux = {
  assertName : string;
  args : arg list option;
  assertt : assertion;
  ph : proofs_helper
}
type assertion_annoted = ASTAssertAn of assertion_aux
type properties_block = ASTPropsBlock of string * assertion_annoted list
type program = ASTProg of properties_block list