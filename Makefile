build: clean
	dune build
	dune exec test/dslprop_test.exe
	dune build @fmt --auto-promote
clean:
	dune clean
