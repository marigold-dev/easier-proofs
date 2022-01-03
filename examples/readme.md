# Build examples

- Run the script `./configure.sh` to generate the `_CoqProject` and `Makefile` automatically.

- Generate `Coq` file(s) by using the [coq-of-ocaml](https://github.com/foobar-land/coq-of-ocaml/tree/master), for example for `OCaml` file(s) inside the folder `bool` do:

    `ruby generate.rb ~/easier-proofs examples bool`

- To compile the `Coq` files do: `make`

- To clean up `Coq` do: `make clean`

