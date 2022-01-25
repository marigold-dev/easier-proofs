.DEFAULT_GOAL := all

.PHONY: all
all: 
	dune build @all

.PHONY: check
check:
	dune build @check  

.PHONY: test
test: # Run the unit tests
	dune build @src/tests/runtest
  
.PHONY: clean 
clean: # Clean build artifacts and other generated files
	dune clean

.PHONY: fmt 
fmt: # Format the codebase with ocamlformat 
	dune build @fmt --auto-promote

.PHONY: watch 
watch: # Watch for the filesyste, and rebuild on every change 
	dune build --watch

.PHONY: doc
doc: # Generate odoc 
	dune build @doc-private

.PHONE: update-ocamlformat
update-ocamlformat:
	@src/tooling/lint.sh --update-ocamlformat

.PHONY: check-linting
check-linting:	
	@src/tooling/lint.sh --check-ocamlformat
	@dune build @fmt