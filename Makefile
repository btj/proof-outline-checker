all: proof_checker.js

COQ_OPTS=-R . proofchecker

proof_outlines.vo: proof_outlines.v
	coqc $(COQ_OPTS) proof_outlines.v

normalizer.vo: proof_outlines.vo normalizer.v
	coqc $(COQ_OPTS) normalizer.v

type_checker.vo: type_checker.v proof_outlines.vo
	coqc $(COQ_OPTS) type_checker.v

proof_checker.vo: proof_checker.v normalizer.vo
	coqc $(COQ_OPTS) proof_checker.v

proof_checker.ml: type_checker.vo proof_checker.vo
	echo 'Require Import type_checker proof_checker. Require Extraction. Extraction "proof_checker.ml" post_env_of_stmt check_proof_outline.' | coqtop $(COQ_OPTS)

proof_checker.byte: proof_checker.ml proof_checker_main.ml
	ocamlfind ocamlc -g -verbose -package js_of_ocaml -package js_of_ocaml-ppx -linkpkg proof_checker.mli proof_checker.ml proof_checker_main.ml -o proof_checker.byte

proof_checker.js: proof_checker.byte
	js_of_ocaml --pretty --no-inline proof_checker.byte
