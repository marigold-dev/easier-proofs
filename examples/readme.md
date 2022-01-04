# Build examples

- Run the script `./configure.sh` to generate the `_CoqProject` and `Makefile` automatically.

- Generate `Coq` file(s) by using the [coq-of-ocaml](https://github.com/foobar-land/coq-of-ocaml/tree/master), for example for `OCaml` file(s) inside the folder `bool` do:

    `ruby generate.rb ~/easier-proofs examples bool`

- To clean up the generated `Coq` file(s) do:
  
    `ruby cleanup.rb ~/easier-proofs examples bool`

- To compile `Coq` file(s) do: `make`

- To clean up `Coq` file(s) do: `make clean`

