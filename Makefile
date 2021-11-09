build: clean
	dune build
	dune exec test/dslprop_test.exe
clean:
	dune clean
