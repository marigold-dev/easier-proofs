type bop =
  | Equal
  | Diff

type arg = ASTArg of string * string
type proofs_helper = Straight | Case of int
type assertion = ASTAssert of string * bop * string
type assertion_descr = ASTAssertD of string * arg list option * assertion
type property = ASTProp of assertion_descr * proofs_helper
type program = ASTProg of string * property list