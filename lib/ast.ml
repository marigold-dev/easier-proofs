type bop =
  | Equal
  | Diff

type arg = ASTArg of string * string
type proofs_helper = Straight | Case of int
type assertion = ASTAssert of string * bop * string
type assertion_annoted = ASTAssertAn of string * arg list option * assertion * proofs_helper
type properties_block = ASTPropsBlock of string * assertion_annoted list
type program = ASTProg of properties_block list