(lang dune 2.9)
(using menhir 2.1)
(name easier_proof)
(generate_opam_files true)

(source
 (github marigold-dev/easier-proofs))

(authors "Hakim Baaloudj <hakim@marigold.dev")
(maintainers "Marigold Team")

(package
 (name easier_proof)
 (synopsis "Easier proof generate Coq proof from a DSL embedded in OCaml")
 (depends
  (alcotest :with-test)
  (dune (>= 2.9.1))
  (coq (>= 8.14.0))
  (coq-of-ocaml (>= 2.5.1))
  (odoc (>= 2.0.0))
  (ocamlformat (>= 0.20.1))))