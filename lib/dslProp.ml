open Ast

let forall = Some(Forall)
let case ?(target=None) n = Case (n,target)
let induction target = Induction target
let straight = Straight

let atom str = ASTAtom str

let prop_case name ?(quantif=None) ?(args=None) assertt helper =
  ASTProp ({
    assertName = name;
    qtf = quantif;
    args = args;
    assertt = assertt;
    h = helper
    }
  )

let args_ l = Some (List.map (fun arg -> ASTArg(fst arg,snd arg)) l)
let toProofs blocks = ASTBlocks blocks
let block name asserts = ASTBlock (name,asserts)

let (=.=) l r = ASTAssert (Equality,l,r)
let (=!=) l r = ASTAssert (Inequality,l,r)

let (&^) l r = ASTAssert (Conjonction,l,r)
let (|^) l r = ASTAssert (Disjonction,l,r)