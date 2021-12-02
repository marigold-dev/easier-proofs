open Ast


let args_ l = Some (List.map (fun arg -> ASTArg(fst arg,snd arg)) l)
let forall args = (Some(Forall),args_ args)
let case n target = Case (n,target)
let induction target = Induction target
let straight = Straight

let atom str = ASTAtom str

let prop name ?(context=(None,None)) assertt =
  ASTProp ({
    assert_name = name;
    qtf = fst context;
    args = snd context;
    assertt = assertt;
    }
  )
let to_proofs blocks = ASTBlocks blocks
let block name asserts = ASTBlock (name,asserts)

let (=.=) l r = fun h -> ASTAssert (Equality,l,r,h)
let (=!=) l r = fun h -> ASTAssert (Inequality,l,r,h)

let (&^) l r = ASTAssert (Conjonction,l,r,Straight)
let (|^) l r = fun h -> ASTAssert (Disjonction,l,r,h)

let (>>) (l : helper -> assertion) h = l h