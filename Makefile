build: clean
	dune build
	dune exec tests/dslprop_test.exe
	dune build @fmt --auto-promote
clean:
	dune clean
