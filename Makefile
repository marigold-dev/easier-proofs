build: clean
	dune build
    dune build @fmt --auto-promote
clean:
	dune clean
test:
    dune exec src/tests/dslprop_test.exe