# Build examples

## Generate 
- First, we need to generate `Coq` file(s) by using the [coq-of-ocaml](https://github.com/foobar-land/coq-of-ocaml/tree/master), for example for `OCaml` file(s) inside the folder `bool` do:

    `ruby generate.rb ~/easier-proofs examples bool`

- Then, run the script `./configure.sh` to generate the `_CoqProject` and `Makefile` automatically.

- Finally, compile `Coq` file(s) do: `make`

## To clean up

- The `Coq` compiled file(s) do: `make clean`
  
- The generated `Coq` file(s) `*.v`, `_CoqProject`, `Makefile` and `Makefile.conf` do:
  
    `ruby cleanup.rb ~/easier-proofs examples bool`


