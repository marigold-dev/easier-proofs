build: 
	dune build
	clean
	fmt
    
clean:
	dune clean

fmt: 
    dune build @fmt 

test:
    dune exec src/tests/dslprop_test.exe