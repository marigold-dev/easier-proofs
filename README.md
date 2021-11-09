# easier-proves
A project which aim to help engineers to make proofs easily

## HOW TO USE IT

## RUN TESTS

"dune build" and "dune exec test/<test_you_want>.exe" or "make", the Makefile will clean, build and run the tests.

## EXAMPLES

In "examples" dir we have an ocaml file, a coq file (generated with coq-of-ocaml) and a dir named "prop" with ".properties" files with properties of functions of the ocaml file, written in my DSL syntax, for generated coq proofs.

run "./run_examples.sh" will run the proof generator on the files contained in the "props" dir.

## TODO/REPORT
1. Fow now, left and right part of the assertion are string, change that and refine.
2. For now, we specify the number of case at hand for "case" kind of proof. Maybe analyse myself the sum types ?
3. Add tests for existing kind of proofs handled.
4. Add more kind of proofs and properties to handle (Monoid, Monad, etc).
5. ugly code actually.
6. "case" simple proofs doesn't work as i treat the assertion as a string for now, because i have to know the variable i want to "case". 

## Kind of proofs possible
1. [DONE] "one shot" proofs for equality and inequality are made (solvable with auto/discriminate).
2. [WIP] "case" simple proofs for equality and inequality assertions (solvable with as many auto/discriminate as cases).
