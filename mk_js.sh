ocamlfind ocamlc -g -verbose -package js_of_ocaml -package js_of_ocaml-ppx -linkpkg proof_checker.mli proof_checker.ml proof_checker_main.ml -o proof_checker.byte
js_of_ocaml --pretty --no-inline proof_checker.byte
