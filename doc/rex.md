---
tags: easier-proofs
title: First review on easier proofs
status: Draft
author: Marigold
type:
created: 2022-Jan-17
version: 1
---
# Easier-proofs

This is an overview of the project easier-proofs. 

## The current state of easier-proofs

Easier-proofs is a tool that is written in OCaml. The purpose of this project is to generate proofs automatically. It is currently using the Coq proof assistants for proving.

The workflow of easier-proofs is as follow:

- A project is written in an OCaml programming language, define all the types and function definitions that one wants to use for proving.
- Using the tool named [`coq-of-ocaml`](https://foobar-land.github.io/coq-of-ocaml/) convert this OCaml program into a Coq program.
- This is the part where one can use easier-proofs to write proofs: write an OCaml program, where it contains all the proofs properties that one want to proof, and then using the helpers provided from easier-proofs to prove those properties. 

### Propositional logics in easier-proofs 
<!-- https://www.cs.cornell.edu/courses/cs3110/2017fa/l/20-coq-logic/notes.html#:~:text=Implication%20is%20so%20primitive%20that,always%20and%20never%20hold%2C%20respectively.-->
- Implication: $P \rightarrow Q$
- Conjunction: $P \wedge Q$
- Disjunction: $P \vee Q$
- Equality: $P = Q$
- Inequality: $P \neq Q$

### Universal quantification
- Forall: $\forall$

### Helpers provide by easier-proofs
Notice that, these proofs are standalone proofs which mean that they do not need to have auxiliary lemmas to solve theirs proof.

Currently, easier-proofs provides some cases for proofs is as follow:

#### Straightforward proof
These are the proofs that can be solved by using the `crush` tactic.
The keyword of this helper is `straight`.

#### Case analysis 
`case`, it uses to solve the case analysis, the helper will first called the `destruct` tactic and then the `crush` tactic.

#### Induction 
It uses to solve the case of induction by using the `induction` tactic and then the `crush` tactic.

#### Conjunction
It uses to solve the conjunction propositional logic. It uses the `split` tactic. 

#### Disjunction - left
It uses to solve the case of disjunction on the left with the `left` tactic.

#### Disjunction - right
It uses to solve the case of disjunction on the right with the `right` tactic.

### Syntax in easier-proofs

- `forall args`
- `case target`
- `induction target`
- `straight`
- `atom ""`
- `prop "" ~context:() ~hints:[] assert`
- `to_proofs blocks`
- `block name asserts`

- `=`: `=.=`
- `!=`: `=!=`
- `&`: `&^`
- `|`: `|^`
- `->`: `|->`

#### Structure of a proof 

```
to_proofs [
    block "comments line of the proof" [
        prop 
        "proof_name" 
        ~context:(forall [("arg","type")])
        (atom "left proof statement" =.= atom "right proof statement" >> helpers)
        ~hints:[]
    ]
]
```


## What easier-proofs does not have at the moment

## Projects trial
