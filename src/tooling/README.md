# Shell script `lint.sh`

This shell script helps to automatically generate the `.ocamlformat` if it does not exists and easily to modify the contents version in `.ocamformat`. 

To be able to run this script, the git repository must be clean, you can check it by using the `git diff`.

To run the script there are two ways:
- From the directory `src/tooling/` do:
  
  `./lint.sh --update-ocamlformat`: to update or generate `.ocamlformat` if it does not exists.

  `./lint.sh --check-ocamlformat`: to check whether the git repository is clean or not and call the `ocamlformat` to formatting all the OCaml files.

- Or using the Makefile command:
  
  `make check-linting` for calling the `lint.sh --check-ocamlformat`

  `make update-ocamlformat` for calling the `lint.sh --update-ocamlformat`

