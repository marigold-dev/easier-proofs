open Ast

let forall = Some(Forall)
let case n target = Case (n,target)
let induction target = Induction target
let straight = Straight

let atom str = ASTAtom str

let prop_case name ?(quantif=None) ?(args=None) assertt =
  ASTProp ({
    assert_name = name;
    qtf = quantif;
    args = args;
    assertt = assertt;
    }
  )

let args_ l = Some (List.map (fun arg -> ASTArg(fst arg,snd arg)) l)
let to_proofs blocks = ASTBlocks blocks
let block name asserts = ASTBlock (name,asserts)

let (=.=) l r = fun h -> ASTAssert (Equality,l,r,h)
let (=!=) l r = fun h -> ASTAssert (Inequality,l,r,h)

let (&^) l r = ASTAssert (Conjonction,l,r,Straight)
let (|^) l r = fun h -> ASTAssert (Disjonction,l,r,h)

let (>>) (l : helper -> assertion) h = l h