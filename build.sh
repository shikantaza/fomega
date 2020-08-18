#!/bin/sh
ocamlfind ocamlopt -o fomega -linkpkg -package str fomega.ml main.ml
ocamlfind ocamlopt -o test_fomega -linkpkg -package ounit2 -package str fomega.ml fomega_test.ml
