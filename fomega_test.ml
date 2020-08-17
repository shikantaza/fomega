(*
  Copyright 2020 Rajesh Jayaprakash <rajesh.jayaprakash@gmail.com>

  This file is part of fomega.

  fomega is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  fomega is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with fomega.  If not, see <http://www.gnu.org/licenses/>.
*)

(*
 * command to compile: 'ocamlfind ocamlopt -o test_fomega -linkpkg -package ounit2 -package str fomega.ml fomega_test.ml'
*)

open OUnit2

open Fomega

let test_get_1 test_ctxt =
  assert_equal None (get (empty_env ()) "x")

let test_get_2 test_ctxt =
  let env = update_term_env (empty_env ()) "x" (TypeVariable "Integer") in
  match (get env "x") with
  | Some x -> assert_equal x (TypeVariable "Integer")
  | None   -> failwith "test_get_2 failed"
 
let test_get_3 test_ctxt =
  let env1 = update_term_env (empty_env ()) "x" (TypeVariable "Integer") in
  let env2 = update_term_env env1 "y" (TypeVariable "Float") in
  match (get env2 "x") with
  | Some x -> assert_equal x (TypeVariable "Integer")
  | None   -> failwith "test_get_3 failed"

let test_get_4 test_ctxt =
  let env1 = update_term_env (empty_env ()) "x" (TypeVariable "Integer") in
  let env2 = update_term_env env1 "y" (TypeVariable "Float") in
  match (get env2 "y") with
  | Some x -> assert_equal x (TypeVariable "Float")
  | None   -> failwith "test_get_4 failed"

let test_get_5 test_ctxt =
  let env1 = update_term_env (empty_env ()) "x" (TypeVariable "Integer") in
  let env2 = update_term_env env1 "y" (TypeVariable "Float") in
    assert_equal None (get env2 "z")

let test_get_6 test_ctxt =
  let env = update_type_env (empty_env ()) "Integer" TypeKind  in
  match (get env "Integer") with
  | Some x -> assert_equal x TypeKind
  | None   -> failwith "test_get_6 failed"

let test_get_7 test_ctxt =
  let env1 = update_type_env (empty_env ()) "Integer" TypeKind in
  let env2 = update_type_env env1 "Float" TypeKind in
  match (get env2 "Integer") with
  | Some x -> assert_equal x TypeKind
  | None   -> failwith "test_get_7 failed"

let test_get_8 test_ctxt =
  let env1 = update_type_env (empty_env ()) "Integer" TypeKind in
  let env2 = update_type_env env1 "Float" TypeKind in
  match (get env2 "Float") with
  | Some x -> assert_equal x TypeKind
  | None   -> failwith "test_get_8 failed"

let test_get_9 test_ctxt =
  let env1 = update_type_env (empty_env ()) "Integer" TypeKind in
  let env2 = update_type_env env1 "Float" TypeKind in
    assert_equal None (get env2 "Char")

let test_equiv_kinds_1 test_ctxt =
  assert_equal (equiv_kinds (Some TypeKind) (Some TypeKind)) true

let test_equiv_kinds_2 test_ctxt =
  assert_equal (equiv_kinds (Some (ArrowKind (TypeKind, TypeKind)))
                            (Some (ArrowKind (TypeKind, TypeKind)))) true

let test_equiv_kinds_3 test_ctxt =
  assert_equal (equiv_kinds (Some (ArrowKind (TypeKind, TypeKind)))
                            (Some TypeKind)) false

let test_replace_type_var_1 test_ctxt =
  assert_equal (replace_type_var (TypeVariable "a") "a" (TypeVariable "b")) (TypeVariable "b")

let test_replace_type_var_2 test_ctxt =
  let type1 = ArrowType (TypeVariable "Integer", TypeVariable "Float") in
    assert_equal (replace_type_var type1 "Integer" (TypeVariable "Float"))
                 (ArrowType (TypeVariable "Float", TypeVariable "Float"))

let test_replace_type_var_3 test_ctxt =
  let type1 = Forall (("a", TypeKind), ArrowType(TypeVariable "b", TypeVariable "c")) in
    assert_equal (replace_type_var type1 "b" (TypeVariable "x"))
                 (Forall (("a", TypeKind), ArrowType(TypeVariable "x", TypeVariable "c")))

let test_replace_type_var_4 test_ctxt =
  let type1 = TAbs (("a", TypeKind), ArrowType(TypeVariable "b", TypeVariable "c")) in
    assert_equal (replace_type_var type1 "b" (TypeVariable "x"))
                 (TAbs (("a", TypeKind), ArrowType(TypeVariable "x", TypeVariable "c")))

let test_replace_type_var_5 test_ctxt =
  let type1 = TApp(TypeVariable "x", TypeVariable "y") in
    assert_equal (replace_type_var type1 "x" (TypeVariable "z"))
                 (TApp(TypeVariable "z", TypeVariable "y"))

let test_replace_type_var_6 test_ctxt =
  assert_bool "test_replace_type_var_6 failure"
              (not ((replace_type_var (TypeVariable "a") "a" (TypeVariable "b")) = (TypeVariable "x")))

let test_replace_type_var_7 test_ctxt =
  let type1 = ArrowType (TypeVariable "Integer", TypeVariable "Float") in
    assert_bool "test_replace_type_var_7 failure"
                (not ((replace_type_var type1 "Integer" (TypeVariable "Float")) =
                      (ArrowType (TypeVariable "Char", TypeVariable "Float"))))

let test_replace_type_var_8 test_ctxt =
  let type1 = Forall (("a", TypeKind), ArrowType(TypeVariable "b", TypeVariable "c")) in
    assert_bool "test_replace_type_var_8 failure"
                (not ((replace_type_var type1 "b" (TypeVariable "x")) =
                      (Forall (("a", TypeKind), ArrowType(TypeVariable "b", TypeVariable "c")))))

let test_replace_type_var_9 test_ctxt =
  let type1 = TAbs (("a", TypeKind), ArrowType(TypeVariable "b", TypeVariable "c")) in
    assert_bool "test_replace_type_var_9 failure"
                (not ((replace_type_var type1 "b" (TypeVariable "x")) =
                      (TAbs (("a", TypeKind), ArrowType(TypeVariable "b", TypeVariable "c")))))

let test_replace_type_var_10 test_ctxt =
  let type1 = TApp(TypeVariable "x", TypeVariable "y") in
    assert_bool "test_replace_type_var_10 failure"
                (not ((replace_type_var type1 "x" (TypeVariable "z")) =
                      (TApp(TypeVariable "x", TypeVariable "y"))))

let test_get_kind_1 test_ctxt =
  let env = update_type_env (empty_env ()) "x" TypeKind in
    assert_equal (get_kind (TypeVariable "x") env) (Some TypeKind)

let test_get_kind_2 test_ctxt =
  let env1 = update_type_env (empty_env ()) "x" TypeKind in
  let env2 = update_type_env env1 "y" TypeKind in
    assert_equal (get_kind (ArrowType(TypeVariable "x", TypeVariable "y")) env2) (Some TypeKind)

let test_get_kind_3 test_ctxt =
  let env1 = update_type_env (empty_env ()) "x" TypeKind in
  let env2 = update_type_env env1 "y" TypeKind in
    assert_equal (get_kind (Forall(("x", TypeKind), TypeVariable "y")) env2) (Some TypeKind)

let test_get_kind_4 test_ctxt =
  let env1 = update_type_env (empty_env ()) "x" TypeKind in
  let env2 = update_type_env env1 "y" TypeKind in
    assert_equal (get_kind (TAbs(("x", TypeKind), TypeVariable "y")) env2) (Some (ArrowKind(TypeKind, TypeKind)))

let test_get_kind_5 test_ctxt =
  let env1 = update_type_env (empty_env ()) "x" (ArrowKind(TypeKind, TypeKind)) in
  let env2 = update_type_env env1 "y" TypeKind in
    assert_equal (get_kind (TApp(TypeVariable "x", TypeVariable "y")) env2) (Some TypeKind)

let test_get_kind_6 test_ctxt =
  let env1 = update_type_env (empty_env ()) "x" (ArrowKind(TypeKind, ArrowKind(TypeKind, TypeKind))) in
  let env2 = update_type_env env1 "y" TypeKind in
    assert_equal (get_kind (TApp(TypeVariable "x", TypeVariable "y")) env2) (Some (ArrowKind(TypeKind, TypeKind)))

let test_get_kind_7 test_ctxt =
  let env = update_type_env (empty_env ()) "x" TypeKind in
    assert_bool "test_get_kind_7 failure" (not ((get_kind (TypeVariable "x") env) = (Some (ArrowKind(TypeKind, TypeKind)))))

let test_get_kind_8 test_ctxt =
  let env1 = update_type_env (empty_env ()) "x" TypeKind in
  let env2 = update_type_env env1 "y" TypeKind in
    assert_bool "test_get_kind_8 failure"
                (not ((get_kind (ArrowType(TypeVariable "x", TypeVariable "y")) env2) = (Some (ArrowKind(TypeKind, TypeKind)))))

let test_get_kind_9 test_ctxt =
  let env1 = update_type_env (empty_env ()) "x" TypeKind in
  let env2 = update_type_env env1 "y" TypeKind in
    assert_bool "test_get_kind_9 failure"
                (not ((get_kind (Forall(("x", TypeKind), TypeVariable "y")) env2) = (Some (ArrowKind(TypeKind, TypeKind)))))

let test_get_kind_10 test_ctxt =
  let env1 = update_type_env (empty_env ()) "x" TypeKind in
  let env2 = update_type_env env1 "y" TypeKind in
    assert_bool "test_get_kind_10 failure"
                (not ((get_kind (TAbs(("x", TypeKind), TypeVariable "y")) env2) = (Some TypeKind)))

let test_get_kind_11 test_ctxt =
  let env1 = update_type_env (empty_env ()) "x" (ArrowKind(TypeKind, TypeKind)) in
  let env2 = update_type_env env1 "y" TypeKind in
    assert_bool "test_get_kind_11 failure"
                (not ((get_kind (TApp(TypeVariable "x", TypeVariable "y")) env2) = (Some (ArrowKind(TypeKind, TypeKind)))))

let test_get_kind_12 test_ctxt =
  let env1 = update_type_env (empty_env ()) "x" (ArrowKind(TypeKind, ArrowKind(TypeKind, TypeKind))) in
  let env2 = update_type_env env1 "y" TypeKind in
    assert_bool "test_get_kind_12 failure"
                (not ((get_kind (TApp(TypeVariable "x", TypeVariable "y")) env2)  = (Some TypeKind)))

let test_equiv_types_1 test_ctxt =
  assert_equal (equiv_types (TypeVariable "x") (TypeVariable "x")) true

let test_equiv_types_2 test_ctxt =
  assert_equal (equiv_types (ArrowType(TypeVariable "x", TypeVariable "y"))
                            (ArrowType(TypeVariable "x", TypeVariable "y")))
               true

let test_equiv_types_3 test_ctxt =
  assert_equal (equiv_types (Forall(("x", TypeKind), TypeVariable "y"))
                            (Forall(("x", TypeKind), TypeVariable "y")))
               true

let test_equiv_types_4 test_ctxt =
  assert_equal (equiv_types (Forall(("x", TypeKind), TApp(TypeVariable "a", TypeVariable "x")))
                            (Forall(("y", TypeKind), TApp(TypeVariable "a", TypeVariable "y"))))
               true 

let test_equiv_types_5 test_ctxt =
  assert_equal (equiv_types (TAbs(("x", TypeKind), TypeVariable "y"))
                            (TAbs(("x", TypeKind), TypeVariable "y")))
               true

let test_equiv_types_6 test_ctxt =
  assert_equal (equiv_types (TAbs(("x", TypeKind), TApp(TypeVariable "a", TypeVariable "x")))
                            (TAbs(("y", TypeKind), TApp(TypeVariable "a", TypeVariable "y"))))
               true 

let test_equiv_types_7 test_ctxt =
  assert_equal (equiv_types (TApp(TypeVariable "x", TypeVariable "y"))
                            (TApp(TypeVariable "x", TypeVariable "y")))
               true

let test_equiv_types_8 test_ctxt =
  assert_equal (equiv_types (TApp(TAbs(("alpha", TypeKind), TApp(TypeVariable "tau", TypeVariable "alpha")),
                                  TypeVariable "sigma"))
                            (TApp(TypeVariable "tau", TypeVariable "sigma")))
               true

let test_equiv_types_9 test_ctxt =
  assert_equal (equiv_types (TypeVariable "a") (TypeVariable "b")) false

let test_equiv_types_10 test_ctxt =
  assert_equal (equiv_types (ArrowType(TypeVariable "a", TypeVariable "b"))
                            (ArrowType(TypeVariable "c", TypeVariable "d")))
               false

let test_equiv_types_11 test_ctxt =
  assert_equal (equiv_types (Forall(("x", TypeKind), TypeVariable "y"))
                            (Forall(("p", TypeKind), TypeVariable "q")))
               false

let test_equiv_types_12 test_ctxt =
  assert_equal (equiv_types (TAbs(("x", TypeKind), TypeVariable "y"))
                            (TAbs(("p", TypeKind), TypeVariable "q")))
               false

let test_equiv_types_13 test_ctxt =
  assert_equal (equiv_types (TApp(TypeVariable "x", TypeVariable "y"))
                            (TApp(TypeVariable "p", TypeVariable "q")))
               false

let test_get_type_1 test_ctxt =
  let env = update_term_env (empty_env ()) "x" (TypeVariable "Integer") in
    assert_equal (get_type (TermVariable "x") env (empty_env ()))
                 (Some (TypeVariable "Integer"))

let test_get_type_2 test_ctxt =
  let type_env = update_type_env (empty_env ()) "Float" TypeKind in
  let term_env = update_term_env (empty_env ()) "x" (TypeVariable "Integer") in
    assert_equal (get_type (Abs(("a", TypeVariable "Float"), TermVariable "x")) term_env type_env)
                 (Some (ArrowType(TypeVariable "Float", TypeVariable "Integer")))

let test_get_type_3 test_ctxt =
  let type_env = update_type_env (empty_env ()) "Integer" TypeKind in
  let term_env1 = update_term_env (empty_env ()) "e1" (ArrowType(TypeVariable "Integer", TypeVariable "Float")) in
  let term_env2 = update_term_env term_env1 "e2" (TypeVariable "Integer") in
    assert_equal (get_type (App(TermVariable "e1", TermVariable "e2")) term_env2 type_env)
                 (Some (TypeVariable "Float"))

let test_get_type_4 test_ctxt =
  let term_env = update_term_env (empty_env ()) "e" (TypeVariable "Float") in
    assert_equal (get_type (PAbs(("alpha", TypeKind), TermVariable "e")) term_env (empty_env()))
                 (Some (Forall(("alpha", TypeKind), TypeVariable "Float")))

let test_get_type_5 test_ctxt =
  let term_env = update_term_env (empty_env ()) "e" (Forall(("alpha", TypeKind), TApp(TypeVariable  "tau", TypeVariable "alpha"))) in
  let type_env = update_type_env (empty_env ()) "sigma" (TypeKind) in
    assert_equal (get_type (PApp(TermVariable "e", TypeVariable "sigma")) term_env type_env)
                 (Some (TApp(TypeVariable "tau", TypeVariable "sigma")))

let test_get_type_6 test_ctxt =
  let e1 = PAbs(("X", TypeKind),
                PAbs(("Y", TypeKind),
                     PAbs(("R", TypeKind),
                          Abs(("x", TypeVariable "X"),
                              Abs(("y", TypeVariable "Y"),
                                  Abs(("f", ArrowType(TypeVariable "X", ArrowType(TypeVariable "Y", TypeVariable "R"))),
                                      App(App(TermVariable "f", TermVariable "x"), TermVariable "y"))))))) in
  let t1 = Forall(("X", TypeKind),
                  Forall(("Y", TypeKind),
                         Forall(("R", TypeKind),
                                ArrowType(TypeVariable "X",
                                          ArrowType(TypeVariable "Y",
                                                    ArrowType(ArrowType(TypeVariable "X",
                                                                        ArrowType(TypeVariable "Y",TypeVariable "R")),
                                                              TypeVariable "R")))))) in 
    assert_equal (get_type e1 (empty_env ()) (empty_env())) (Some t1)

let test_is_type_1 test_ctxt =
  let term_env = update_term_env (empty_env ()) "e" (Forall(("alpha", TypeKind), TApp(TypeVariable  "tau", TypeVariable "alpha"))) in
  let type_env1 = update_type_env (empty_env ()) "alpha" TypeKind in
  let type_env2 = update_type_env type_env1 "tau" (ArrowKind(TypeKind, TypeKind)) in
    assert_bool "test_is_type_1 failure"
                (is_type (TermVariable "e")
                         (Forall(("alpha", TypeKind), TApp(TypeVariable  "tau", TypeVariable "alpha")))
                         term_env
                         type_env2)

let test_is_type_2 test_ctxt =
  let term_env = update_term_env (empty_env ()) "e" (Forall(("alpha", TypeKind), TApp(TypeVariable  "tau", TypeVariable "alpha"))) in
  let type_env1 = update_type_env (empty_env ()) "alpha" TypeKind in
  let type_env2 = update_type_env type_env1 "beta" TypeKind in
  let type_env3 = update_type_env type_env2 "tau" (ArrowKind(TypeKind, TypeKind)) in
    assert_bool "test_is_type_1 failure"
                (is_type (TermVariable "e")
                         (Forall(("beta", TypeKind), TApp(TypeVariable  "tau", TypeVariable "beta")))
                         term_env
                         type_env3)

let test_replace_term_var_1 test_ctxt =
  assert_equal (replace_term_var (TermVariable "a") "a" (TermVariable "b")) (TermVariable "b")

let test_replace_term_var_2 test_ctxt =
  let term1 = App (TermVariable "a", TermVariable "b") in
    assert_equal (replace_term_var term1 "a" (TermVariable "b"))
                 (App (TermVariable "b", TermVariable "b"))

let test_replace_term_var_3 test_ctxt =
  let term1 = Abs (("a", TypeVariable "Integer"), App(TermVariable "b", TermVariable "c")) in
    assert_equal (replace_term_var term1 "b" (TermVariable "x"))
                 (Abs (("a", TypeVariable "Integer"), App(TermVariable "x", TermVariable "c")))

let test_replace_term_var_4 test_ctxt =
  let term1 = PAbs (("a", TypeKind), App(TermVariable "b", TermVariable "c")) in
    assert_equal (replace_term_var term1 "b" (TermVariable "x"))
                 (PAbs (("a", TypeKind), App(TermVariable "x", TermVariable "c")))

let test_replace_term_var_5 test_ctxt =
  let term1 = PApp(TermVariable "x", TypeVariable "y") in
    assert_equal (replace_term_var term1 "x" (TermVariable "z"))
                 (PApp(TermVariable "z", TypeVariable "y"))

let test_replace_term_var_6 test_ctxt =
  assert_bool "test_replace_term_var_6 failure"
              (not ((replace_term_var (TermVariable "a") "a" (TermVariable "b")) = (TermVariable "x")))

let test_replace_term_var_7 test_ctxt =
  let term1 = App (TermVariable "a", TermVariable "b") in
    assert_bool "test_replace_term_var_7 failure"
                (not ((replace_term_var term1 "a" (TermVariable "b")) =
                      (App (TermVariable "Char", TermVariable "b"))))

let test_replace_term_var_8 test_ctxt =
  let term1 = Abs (("a", TypeVariable "Integer"), App(TermVariable "b", TermVariable "c")) in
    assert_bool "test_replace_term_var_8 failure"
                (not ((replace_term_var term1 "b" (TermVariable "x")) =
                      (Abs (("a", TypeVariable "Integer"), App(TermVariable "b", TermVariable "c")))))

let test_replace_term_var_9 test_ctxt =
  let term1 = PAbs (("a", TypeKind), App(TermVariable "b", TermVariable "c")) in
    assert_bool "test_replace_term_var_9 failure"
                (not ((replace_term_var term1 "b" (TermVariable "x")) =
                      (PAbs (("a", TypeKind), App(TermVariable "b", TermVariable "c")))))

let test_replace_term_var_10 test_ctxt =
  let term1 = PApp(TermVariable "x", TypeVariable "y") in
    assert_bool "test_replace_term_var_10 failure"
                (not ((replace_term_var term1 "x" (TermVariable "z")) =
                      (PApp(TermVariable "x", TypeVariable "y"))))

let test_replace_type_var_in_term_1 test_ctxt =
  assert_equal (replace_type_var_in_term (TermVariable "x") "x" (TypeVariable "y")) (TermVariable "x")

let test_replace_type_var_in_term_2 test_ctxt =
  assert_equal (replace_type_var_in_term (Abs(("a", TypeVariable "Integer"), TermVariable "x")) "x" (TypeVariable "y"))
               (Abs(("a", TypeVariable "Integer"), TermVariable "x"))

let test_replace_type_var_in_term_3 test_ctxt =
  assert_equal (replace_type_var_in_term (App(TermVariable "a", TermVariable "b")) "a" (TypeVariable "x"))
               (App(TermVariable "a", TermVariable "b"))

let test_replace_type_var_in_term_4 test_ctxt =
  assert_equal (replace_type_var_in_term (PAbs(("a", TypeKind), TermVariable "x")) "b" (TypeVariable "y"))
               (PAbs(("a", TypeKind), TermVariable "x"))

let test_replace_type_var_in_term_5 test_ctxt =
  assert_equal (replace_type_var_in_term (PApp(TermVariable "a", TypeVariable "b")) "b" (TypeVariable "y"))
               (PApp(TermVariable "a", TypeVariable "y"))

let test_reduce_1 test_ctxt =
  assert_equal (reduce (TermVariable "x") (empty_env()) (empty_env())) (TermVariable "x")

let test_reduce_2 test_ctxt =
  assert_equal (reduce (Abs(("x", TypeVariable "Integer"), TermVariable "y")) (empty_env()) (empty_env())) (Abs(("x", TypeVariable "Integer"), TermVariable "y")) 

let test_reduce_3 test_ctxt =
  let term_env = update_term_env (empty_env()) "y" (TypeVariable "Integer") in
    assert_equal (reduce (App(Abs(("x", TypeVariable "Integer"), App(TermVariable "a", TermVariable "x")), (TermVariable "y"))) term_env (empty_env()))
                 (App(TermVariable "a", TermVariable "y"))

let test_reduce_4 test_ctxt =
  assert_equal (reduce (App(TermVariable "x", TermVariable "y")) (empty_env()) (empty_env())) (App(TermVariable "x", TermVariable "y"))

let test_reduce_5 test_ctxt =
  assert_equal (reduce (PAbs(("x", TypeKind), TermVariable "y")) (empty_env()) (empty_env())) (PAbs(("x", TypeKind), TermVariable "y")) 

let test_reduce_6 test_ctxt =
  let type_env = update_type_env (empty_env ()) "beta" TypeKind in
  assert_equal (reduce (PApp(PAbs(("alpha", TypeKind), PApp(TermVariable "e", TypeVariable "alpha")), TypeVariable "beta")) (empty_env()) type_env)
               (PApp(TermVariable "e", TypeVariable "beta"))

let test_reduce_7 test_ctxt =
  assert_equal (reduce (PApp(TermVariable "e", TypeVariable "tau")) (empty_env()) (empty_env())) (PApp(TermVariable "e", TypeVariable "tau"))

let test_reduce_8 test_ctxt =
  let term_env = update_term_env (empty_env()) "y" (TypeVariable "Integer") in
  let e1 = (App(Abs(("x", TypeVariable "Integer"), App(TermVariable "a", TermVariable "x")), (TermVariable "y"))) in
  let e2 = (App(TermVariable "a", TermVariable "y")) in
    assert_equal (reduce (Abs(("x", TypeVariable "Integer"), e1)) term_env (empty_env())) (Abs(("x", TypeVariable "Integer"), e2))

let test_reduce_9 test_ctxt =
  let term_env = update_term_env (empty_env()) "y" (TypeVariable "Integer") in
  let e1 = (App(Abs(("x", TypeVariable "Integer"), App(TermVariable "a", TermVariable "x")), (TermVariable "y"))) in
  let e2 = (App(TermVariable "a", TermVariable "y")) in
    assert_equal (reduce (App(TermVariable "x", e1)) term_env (empty_env())) (App(TermVariable "x", e2))

let test_reduce_10 test_ctxt =
  let term_env = update_term_env (empty_env()) "y" (TypeVariable "Integer") in
  let e1 = (App(Abs(("x", TypeVariable "Integer"), App(TermVariable "a", TermVariable "x")), (TermVariable "y"))) in
  let e2 = (App(TermVariable "a", TermVariable "y")) in
    assert_equal (reduce (App(e1, TermVariable "x")) term_env (empty_env())) (App(e2, TermVariable "x"))

let test_reduce_11 test_ctxt =
  let term_env = update_term_env (empty_env()) "y" (TypeVariable "Integer") in
  let e1 = (App(Abs(("x", TypeVariable "Integer"), App(TermVariable "a", TermVariable "x")), (TermVariable "y"))) in
  let e2 = (App(TermVariable "a", TermVariable "y")) in
    assert_equal (reduce (PAbs(("p", TypeKind), e1)) term_env (empty_env())) (PAbs(("p", TypeKind), e2))

let test_reduce_12 test_ctxt =
  let term_env = update_term_env (empty_env()) "y" (TypeVariable "Integer") in
  let e1 = (App(Abs(("x", TypeVariable "Integer"), App(TermVariable "a", TermVariable "x")), (TermVariable "y"))) in
  let e2 = (App(TermVariable "a", TermVariable "y")) in
    assert_equal (reduce (PApp(e1, TypeVariable "tau")) term_env (empty_env()))
                 (PApp(e2, TypeVariable "tau"))                 

(*
 * /\X:*./\Y:*.\x:X.\y:Y.x A B a b -> a
*)
let test_evaluate_1 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
  let e1 = Abs(("y", TypeVariable "Y"), TermVariable "x") in
  let e2 = Abs(("x", TypeVariable "X"), e1) in
  let e3 = PAbs(("Y", TypeKind), e2) in
  let e4 = PAbs(("X", TypeKind), e3) in
  let e5 = PApp(e4, TypeVariable "A") in
  let e6 = PApp(e5, TypeVariable "B") in
  let e7 = App(e6, TermVariable "a") in
  let e8 = App(e7, TermVariable "b") in
    assert_equal (evaluate e8 term_env type_env) (TermVariable "a")

(*
 * Same expression as above, in single-expression form
 * /\X:*./\Y:*.\x:X.\y:Y.x A B a b -> a
*)
let test_evaluate_2 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
  let e1 = App(App(PApp(PApp(PAbs(("X", TypeKind),
                                  PAbs(("Y", TypeKind),
                                       Abs(("x", TypeVariable "X"),
                                           Abs(("y", TypeVariable "Y"),
                                               TermVariable "x")))),
                             TypeVariable "A"),
                        TypeVariable "B"),
                   TermVariable "a"),
               TermVariable "b") in
    assert_equal (evaluate e1 term_env type_env) (TermVariable "a")

(*
 * /\X:*./\Y:*.\x:X.\y:Y.y A B a b -> b
*)
let test_evaluate_3 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
  let e1 = Abs(("y", TypeVariable "Y"), TermVariable "y") in
  let e2 = Abs(("x", TypeVariable "X"), e1) in
  let e3 = PAbs(("Y", TypeKind), e2) in
  let e4 = PAbs(("X", TypeKind), e3) in
  let e5 = PApp(e4, TypeVariable "A") in
  let e6 = PApp(e5, TypeVariable "B") in
  let e7 = App(e6, TermVariable "a") in
  let e8 = App(e7, TermVariable "b") in
    assert_equal (evaluate e8 term_env type_env) (TermVariable "b")

(*
 * Same expression as above, in single-expression form
 * /\X:*./\Y:*.\x:X.\y:Y.y A B a b -> b
*)
let test_evaluate_4 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
  let e1 = App(App(PApp(PApp(PAbs(("X", TypeKind),
                                  PAbs(("Y", TypeKind),
                                       Abs(("x", TypeVariable "X"),
                                           Abs(("y", TypeVariable "Y"),
                                               TermVariable "y")))),
                             TypeVariable "A"),
                        TypeVariable "B"),
                   TermVariable "a"),
               TermVariable "b") in
    assert_equal (evaluate e1 term_env type_env) (TermVariable "b")

(*
 * /\R:*.\p:A->(B->R).(p a b) A \x:A.\y:B.x -> a
*)
let test_evaluate_5 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
  let e1 = Abs(("p", ArrowType(TypeVariable "A",
                               ArrowType(TypeVariable "B",
                                         TypeVariable "R"))),
               App(App(TermVariable "p", TermVariable "a"),
                   TermVariable "b")) in
  let e2 = PAbs(("R", TypeKind), e1) in
  let e3 = PApp(e2, TypeVariable "A") in
  let e4 = Abs(("y", TypeVariable "B"), TermVariable "x") in
  let e5 = Abs(("x", TypeVariable "A"), e4) in
  let e6 = App(e3, e5) in
    assert_equal (evaluate e6 term_env type_env) (TermVariable "a")

(*
 * /\R:*.\p:A->(B->R).(p a b) B \x:A.\y:B.y -> b
*)
let test_evaluate_6 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
  let e1 = Abs(("p", ArrowType(TypeVariable "A",
                               ArrowType(TypeVariable "B",
                                         TypeVariable "R"))),
               App(App(TermVariable "p", TermVariable "a"),
                   TermVariable "b")) in
  let e2 = PAbs(("R", TypeKind), e1) in
  let e3 = PApp(e2, TypeVariable "B") in
  let e4 = Abs(("y", TypeVariable "B"), TermVariable "y") in
  let e5 = Abs(("x", TypeVariable "A"), e4) in
  let e6 = App(e3, e5) in
    assert_equal (evaluate e6 term_env type_env) (TermVariable "b")

(*
 *   \q:(\/B:*.B->B)->P.(q /\C:*.\y:C.y) \id:\/D:*.(D->D).p -> p
*)
let test_evaluate_7 test_ctxt =
  let term_env = update_term_env (empty_env ()) "p" (TypeVariable "P") in
  let type_env = update_type_env (empty_env ()) "P" TypeKind in
  let e = App(Abs(("q", ArrowType(Forall(("B", TypeKind),
                                         ArrowType(TypeVariable "B", TypeVariable "B")),
                                  TypeVariable "P")),
                  App(TermVariable "q", PAbs(("C", TypeKind), Abs(("y", TypeVariable "C"), TermVariable "y")))),
              Abs(("id", Forall(("D", TypeKind), ArrowType(TypeVariable "D", TypeVariable "D"))),
                  TermVariable "p")) in
    assert_equal (evaluate e term_env type_env) (TermVariable "p")

(*
 * /\A:*.\q:(\/B:*.(B->B))->A.(q /\C:*.\y:C.y) P \id:\/D:*.(D->D).p -> p
*)
let test_evaluate_8 test_ctxt =
  let term_env = update_term_env (empty_env ()) "p" (TypeVariable "P") in
  let type_env = update_type_env (empty_env ()) "P" TypeKind in
  let e1 = PAbs(("A", TypeKind),
                Abs(("q", ArrowType(Forall(("B", TypeKind),
                                           ArrowType(TypeVariable "B", TypeVariable "B")),
                                          TypeVariable "A")),
                    App(TermVariable "q", PAbs(("C", TypeKind), Abs(("y", TypeVariable "C"), TermVariable "y"))))) in
  let e2 = Abs(("id", Forall(("D", TypeKind), ArrowType(TypeVariable "D", TypeVariable "D"))),
               TermVariable "p") in
  let e3 = App(PApp(e1, TypeVariable "P"), e2) in
    assert_equal (evaluate e3 term_env type_env) (TermVariable "p")

(*
 * \p:\/R:*.(A->B->R)->R.(p A \x:A.\y:B.x) /\R:*.\p:A->B->R.(p a b) -> a
*)
let test_evaluate_9 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
  let t1 = ArrowType(TypeVariable "A",
                     ArrowType(TypeVariable "B", TypeVariable "R")) in
  let e1 = Abs(("x", TypeVariable "A"),
               Abs(("y", TypeVariable "B"), TermVariable "x")) in
  let e2 = Abs(("p", Forall(("R", TypeKind), ArrowType(t1, TypeVariable "R"))),
               App(PApp(TermVariable "p", TypeVariable "A"), e1)) in
  let e3 = PAbs(("R", TypeKind),
                Abs(("p", t1), App(App(TermVariable "p",TermVariable "a"), TermVariable "b"))) in
    assert_equal (evaluate (App(e2, e3)) term_env type_env) (TermVariable "a")

(*
 * /\X:*./\Y:*.\p:\/R:*.(X->Y->R)->R.(p X \x:X.\y:Y.x) A B (/\X:*./\Y:*.\x:X.\y:Y./\R:*.\p:X->Y->R.(p x y) A B a b) -> a
*)
let test_evaluate_10 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
  let t1 = ArrowType(TypeVariable "X", ArrowType(TypeVariable "Y", TypeVariable "R")) in
  let e1 = Abs(("x", TypeVariable "X"), Abs(("y", TypeVariable "Y"), TermVariable "x")) in
  let e2 = PAbs(("X", TypeKind),
                PAbs(("Y", TypeKind),
                     Abs(("p", Forall(("R", TypeKind), ArrowType(t1, TypeVariable "R"))),
                         App(PApp(TermVariable "p", TypeVariable "X"), e1)))) in
  let e3 = PAbs(("X", TypeKind),
                PAbs(("Y", TypeKind),
                     Abs(("x", TypeVariable "X"),
                         Abs(("y", TypeVariable "Y"),
                             PAbs(("R", TypeKind),
                                  Abs(("p", t1), App(App(TermVariable "p", TermVariable "x"), TermVariable "y"))))))) in
  let e4 = App(App(PApp(PApp(e3, TypeVariable "A"), TypeVariable "B"), TermVariable "a"), TermVariable "b") in
  let e5 = App(PApp(PApp(e2, TypeVariable "A"), TypeVariable "B"), e4) in
    assert_equal (evaluate e5 term_env type_env) (TermVariable "a")

(*
 * /\X:*./\Y:*.\p:\/R:*.(X->Y->R)->R.(p Y \x:X.\y:Y.y) A B (/\X:*./\Y:*.\x:X.\y:Y./\R:*.\p:X->Y->R.(p x y) A B a b) -> b
*)
let test_evaluate_11 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
  let t1 = ArrowType(TypeVariable "X", ArrowType(TypeVariable "Y", TypeVariable "R")) in
  let e1 = Abs(("x", TypeVariable "X"), Abs(("y", TypeVariable "Y"), TermVariable "y")) in
  let e2 = PAbs(("X", TypeKind),
                PAbs(("Y", TypeKind),
                     Abs(("p", Forall(("R", TypeKind), ArrowType(t1, TypeVariable "R"))),
                         App(PApp(TermVariable "p", TypeVariable "Y"), e1)))) in
  let e3 = PAbs(("X", TypeKind),
                PAbs(("Y", TypeKind),
                     Abs(("x", TypeVariable "X"),
                         Abs(("y", TypeVariable "Y"),
                             PAbs(("R", TypeKind),
                                  Abs(("p", t1), App(App(TermVariable "p", TermVariable "x"), TermVariable "y"))))))) in
  let e4 = App(App(PApp(PApp(e3, TypeVariable "A"), TypeVariable "B"), TermVariable "a"), TermVariable "b") in
  let e5 = App(PApp(PApp(e2, TypeVariable "A"), TypeVariable "B"), e4) in
    assert_equal (evaluate e5 term_env type_env) (TermVariable "b")

(*
 *       first=/\X:*./\Y:*.\p:\/R:*.(X->Y->R)->R.(p X \x:X.\y:Y.x)
 *       tapp=/\A:*.\e:A./\B:*.\inst:A->B.(inst e)
 *       F=\/X:*.\/Y:*.(\/R:*.(X->Y->R)->R)->X
 *       T=\/Y:*.(\/R:*.(A->Y->R)->R)->A
 *       tapp F first T \x:F.(x A)
 *
 *       => this should produce the same result as 'first A' 
*)
let test_evaluate_12 test_ctxt =
  let term_env = update_term_env (empty_env ()) "a" (TypeVariable "A") in
  let type_env = update_type_env (empty_env ()) "A" TypeKind in
  let first = PAbs(("X", TypeKind),
                   PAbs(("Y", TypeKind),
                        Abs(("p", Forall(("R", TypeKind),
                                         ArrowType(ArrowType(TypeVariable "X",
                                                             ArrowType(TypeVariable "Y",
                                                                       TypeVariable "R")),                          
                                                   TypeVariable "R"))),
                            App(PApp(TermVariable "p", TypeVariable "X"),
                                Abs(("x", TypeVariable "X"),
                                    Abs(("y", TypeVariable "Y"), TermVariable "x")))))) in
  let tapp = PAbs(("A", TypeKind),
                  Abs(("e", TypeVariable "A"),
                      PAbs(("B", TypeKind),
                           Abs(("inst", ArrowType(TypeVariable "A", TypeVariable "B")),
                               App(TermVariable "inst", TermVariable "e"))))) in
  let _F = Forall(("X", TypeKind),
                  Forall(("Y", TypeKind),
                         ArrowType(Forall(("R", TypeKind),
                                          ArrowType(ArrowType(TypeVariable "X", ArrowType(TypeVariable "Y", TypeVariable "R")),
                                                    TypeVariable "R")),
                                   TypeVariable "X"))) in
  let _T = Forall(("Y", TypeKind),
                  ArrowType(Forall(("R", TypeKind),
                                   ArrowType(ArrowType(TypeVariable "A",
                                                       ArrowType(TypeVariable "Y", TypeVariable "R")),
                                             TypeVariable "R")),
                            TypeVariable "A")) in
  let e = App(PApp(App(PApp(tapp, _F), first), _T), Abs(("x", _F), PApp(TermVariable "x", TypeVariable "A"))) in
    assert_equal (evaluate e term_env type_env) (evaluate (PApp(first, TypeVariable "A")) term_env type_env)

let test_split_1 test_ctxt =
  assert_equal (split "abc") ["abc"]

let test_split_2 test_ctxt =
  assert_equal (split "abc def ghi") ["abc"; "def"; "ghi"]

let test_split_3 test_ctxt =
  assert_equal (split "abc    def     ghi") ["abc"; "def"; "ghi"]

let test_split_4 test_ctxt =
  assert_equal (split "()()()(  ) abc") ["()()()(  )"; "abc"]

let test_split_5 test_ctxt =
  assert_equal (split "") [""]

let test_split_6 test_ctxt =
  assert_equal (split "(abc") ["(abc"]

let test_split_7 test_ctxt =
  assert_equal (split "abc\t def\nghi") ["abc"; "def"; "ghi"]

let test_split_8 test_ctxt =
  assert_equal (split "abc  \r  def  \n   ghi") ["abc"; "def"; "ghi"]

let test_split_9 test_ctxt =
  assert_equal (split "()()()(\n\r\t  ) abc") ["()()()(\n\r\t  )"; "abc"]

let test_split_10 test_ctxt =
  assert_equal (split "") [""]

let test_split_11 test_ctxt =
  assert_equal (split "\t\r\n abc") ["abc"]

let test_split_12 test_ctxt =
  assert_equal (split "abc \t\r\n") ["abc"]

let test_split_13 test_ctxt =
  assert_equal (split "\t\r\n abc\t\r\n ") ["abc"]

let test_parse_1 test_ctxt =
  assert_equal (parse "x") (TermEntity (TermVariable "x"))

let test_parse_2 test_ctxt =
  assert_equal (parse "(x)") (TermEntity (TermVariable "x"))

let test_parse_3 test_ctxt =
  assert_equal (parse "x y") (TermEntity (App(TermVariable "x", TermVariable "y")))

let test_parse_4 test_ctxt =
  assert_equal (parse "x Y") (TermEntity (PApp(TermVariable "x", TypeVariable "Y")))

let test_parse_5 test_ctxt =
  assert_equal (parse "\\x:X.x") (TermEntity (Abs(("x",TypeVariable "X"), TermVariable "x")))

let test_parse_6 test_ctxt =
  assert_equal (parse "/\\X:*.(a X)") (TermEntity (PAbs(("X",TypeKind), PApp(TermVariable "a", TypeVariable "X"))))

let test_parse_7 test_ctxt =
  assert_equal (parse "/\\X:*.a X") (TermEntity (PApp(PAbs(("X",TypeKind), TermVariable "a"), TypeVariable "X")))

let test_parse_8 test_ctxt =
  assert_equal (parse "X") (TypeEntity (TypeVariable "X"))

let test_parse_9 test_ctxt =
  assert_equal (parse "(X)") (TypeEntity (TypeVariable "X"))

let test_parse_10 test_ctxt =
  assert_equal (parse "X Y") (TypeEntity (TApp(TypeVariable "X", TypeVariable "Y")))

let test_parse_11 test_ctxt =
  assert_equal (parse "\\X:*.Y") (TypeEntity (TAbs(("X",TypeKind), TypeVariable "Y")))

let test_parse_12 test_ctxt =
  assert_equal (parse "\\/X:*.Y") (TypeEntity (Forall(("X",TypeKind), TypeVariable "Y")))

let test_parse_13 test_ctxt =
  assert_equal (parse "A->B") (TypeEntity (ArrowType(TypeVariable "A", TypeVariable "B")))

let test_parse_14 test_ctxt =
  assert_equal (parse "(A->B)") (TypeEntity (ArrowType(TypeVariable "A", TypeVariable "B")))

let test_parse_15 test_ctxt =
  assert_equal (parse "A->(B)") (TypeEntity (ArrowType(TypeVariable "A", TypeVariable "B")))

let test_parse_16 test_ctxt =
  assert_equal (parse "(A)->B") (TypeEntity (ArrowType(TypeVariable "A", TypeVariable "B")))

let test_parse_17 test_ctxt =
  assert_equal (parse "(A->B)->(C->D)") (TypeEntity (ArrowType(ArrowType(TypeVariable "A", TypeVariable "B"),
                                                               ArrowType(TypeVariable "C", TypeVariable "D"))))

let test_parse_18 test_ctxt =
  assert_equal (parse "A->B->C->D") (TypeEntity (ArrowType(TypeVariable "A",
                                                           ArrowType(TypeVariable "B",
                                                                     ArrowType(TypeVariable "C", TypeVariable "D")))))                          
let test_parse_19 test_ctxt =
  assert_equal (parse "A->(B)->C") (TypeEntity (ArrowType(TypeVariable "A", ArrowType(TypeVariable "B", TypeVariable "C"))))

let test_parse_20 test_ctxt =
  let t1 = ArrowType(TypeVariable "A", TypeVariable "B") in
  let t2 = ArrowType(TypeVariable "C", TypeVariable "D") in
  let t3 = ArrowType(TypeVariable "E", TypeVariable "F") in
    assert_equal (parse "(A->B)->(C->D)->(E->F)") (TypeEntity (ArrowType(t1, ArrowType(t2, t3))))

let test_parse_21 test_ctxt =
  assert_equal (parse_kind "*" 0) (1, TypeKind)

let test_parse_22 test_ctxt =
  assert_equal (parse_kind "*->*" 0) (4, (ArrowKind(TypeKind, TypeKind)))

let test_parse_23 test_ctxt =
  assert_equal (parse_kind "(*->*)" 0) (6, (ArrowKind(TypeKind, TypeKind)))

let test_parse_24 test_ctxt =
  assert_equal (parse_kind "*->(*)" 0) (6, (ArrowKind(TypeKind, TypeKind)))

let test_parse_25 test_ctxt =
  assert_equal (parse_kind "(*)->*" 0) (6, (ArrowKind(TypeKind, TypeKind)))

let test_parse_26 test_ctxt =
  assert_equal (parse_kind "(*->*)->(*->*)" 0) (14, (ArrowKind(ArrowKind(TypeKind, TypeKind),
                                                             ArrowKind(TypeKind, TypeKind))))

let test_parse_27 test_ctxt =
  assert_equal (parse_kind "*->*->*->*" 0) (10, (ArrowKind(TypeKind,
                                                         ArrowKind(TypeKind,
                                                                   ArrowKind(TypeKind, TypeKind)))))                          
let test_parse_28 test_ctxt =
  assert_equal (parse_kind "*->(*)->*" 0) (9, (ArrowKind(TypeKind, ArrowKind(TypeKind, TypeKind))))

let test_parse_29 test_ctxt =
  let k1 = ArrowKind(TypeKind, TypeKind) in
  let k2 = ArrowKind(TypeKind, TypeKind) in
  let k3 = ArrowKind(TypeKind, TypeKind) in
    assert_equal (parse_kind "(*->*)->(*->*)->(*->*)" 0) (22, (ArrowKind(k1, ArrowKind(k2, k3))))

let test_parse_30 test_ctxt =
  assert_equal (parse "\\x:(A->B).(x y)") (TermEntity (Abs(("x", ArrowType(TypeVariable "A", TypeVariable "B")),
                                                           App(TermVariable "x", TermVariable "y"))))

(*
 * /\X:*./\Y:*.\x:X.\y:Y.x A B a b -> a
*)
let test_parse_and_evaluate_1 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
    assert_equal (parse_and_evaluate "/\\X:*./\\Y:*.\\x:X.\\y:Y.x A B a b" term_env type_env) (TermVariable "a")

(*
 * /\X:*./\Y:*.\x:X.\y:Y.y A B a b -> b
*)
let test_parse_and_evaluate_2 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
    assert_equal (parse_and_evaluate "/\\X:*./\\Y:*.\\x:X.\\y:Y.y A B a b" term_env type_env) (TermVariable "b")

(*
 * /\R:*.\p:A->(B->R).(p a b) A \x:A.\y:B.x -> a
*)
let test_parse_and_evaluate_3 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
    assert_equal (parse_and_evaluate "/\\R:*.\\p:A->(B->R).(p a b) A \\x:A.\\y:B.x" term_env type_env) (TermVariable "a")

(*
 * /\R:*.\p:A->(B->R).(p a b) B \x:A.\y:B.y -> b
*)
let test_parse_and_evaluate_4 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
    assert_equal (parse_and_evaluate "/\\R:*.\\p:A->(B->R).(p a b) B \\x:A.\\y:B.y" term_env type_env) (TermVariable "b")

(*
 *   \q:(\/B:*.B->B)->P.(q /\C:*.\y:C.y) \id:\/D:*.(D->D).p -> p
*)
let test_parse_and_evaluate_5 test_ctxt =
  let term_env = update_term_env (empty_env ()) "p" (TypeVariable "P") in
  let type_env = update_type_env (empty_env ()) "P" TypeKind in
    assert_equal (parse_and_evaluate "\\q:(\\/B:*.B->B)->P.(q /\\C:*.\\y:C.y) \\id:\\/D:*.(D->D).p" term_env type_env) (TermVariable "p")

(*
 * /\A:*.\q:(\/B:*.(B->B))->A.(q /\C:*.\y:C.y) P \id:\/D:*.(D->D).p -> p
*)
let test_parse_and_evaluate_6 test_ctxt =
  let term_env = update_term_env (empty_env ()) "p" (TypeVariable "P") in
  let type_env = update_type_env (empty_env ()) "P" TypeKind in
    assert_equal (parse_and_evaluate "/\\A:*.\\q:(\\/B:*.(B->B))->A.(q /\\C:*.\\y:C.y) P \\id:\\/D:*.(D->D).p" term_env type_env) (TermVariable "p")

(*
 * \p:\/R:*.(A->B->R)->R.(p A \x:A.\y:B.x) /\R:*.\p:A->B->R.(p a b) -> a
*)
let test_parse_and_evaluate_7 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
    assert_equal (parse_and_evaluate "\\p:\\/R:*.(A->B->R)->R.(p A \\x:A.\\y:B.x) /\\R:*.\\p:A->B->R.(p a b)" term_env type_env) (TermVariable "a")

(*
 * /\X:*./\Y:*.\p:\/R:*.(X->Y->R)->R.(p X \x:X.\y:Y.x) A B (/\X:*./\Y:*.\x:X.\y:Y./\R:*.\p:X->Y->R.(p x y) A B a b) -> a
*)
let test_parse_and_evaluate_8 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
    assert_equal (parse_and_evaluate "/\\X:*./\\Y:*.\\p:\\/R:*.(X->Y->R)->R.(p X \\x:X.\\y:Y.x) A B (/\\X:*./\\Y:*.\\x:X.\\y:Y./\\R:*.\\p:X->Y->R.(p x y) A B a b)"
                                     term_env type_env)
                 (TermVariable "a")

(*
 * /\X:*./\Y:*.\p:\/R:*.(X->Y->R)->R.(p Y \x:X.\y:Y.y) A B (/\X:*./\Y:*.\x:X.\y:Y./\R:*.\p:X->Y->R.(p x y) A B a b) -> b
*)
let test_parse_and_evaluate_9 test_ctxt =
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "B" TypeKind in
    assert_equal (parse_and_evaluate "/\\X:*./\\Y:*.\\p:\\/R:*.(X->Y->R)->R.(p Y \\x:X.\\y:Y.y) A B (/\\X:*./\\Y:*.\\x:X.\\y:Y./\\R:*.\\p:X->Y->R.(p x y) A B a b)"
                                     term_env type_env)
                 (TermVariable "b")

(*
 *       first=/\X:*./\Y:*.\p:\/R:*.(X->Y->R)->R.(p X \x:X.\y:Y.x)
 *       tapp=/\A:*.\e:A./\B:*.\inst:A->B.(inst e)
 *       F=\/X:*.\/Y:*.(\/R:*.(X->Y->R)->R)->X
 *       T=\/Y:*.(\/R:*.(A->Y->R)->R)->A
 *       tapp F first T \x:F.(x A)
 *
 *       => this should produce the same result as 'first A' 
*)
let test_parse_and_evaluate_10 test_ctxt =
  let term_env = update_term_env (empty_env ()) "a" (TypeVariable "A") in
  let type_env = update_type_env (empty_env ()) "A" TypeKind in
  let first = "/\\X:*./\\Y:*.\\p:\\/R:*.(X->Y->R)->R.(p X \\x:X.\\y:Y.x)" in
  let tapp  = "/\\A:*.\\e:A./\\B:*.\\inst:A->B.(inst e)" in
  let _F    = "\\/X:*.\\/Y:*.(\\/R:*.(X->Y->R)->R)->X" in
  let _T    = "\\/Y:*.(\\/R:*.(A->Y->R)->R)->A" in
    assert_equal (parse_and_evaluate (tapp ^ " " ^ _F ^ " " ^ first ^ " " ^ _T ^ " \\x:" ^ _F ^ ".(x A)") term_env type_env)
                 (parse_and_evaluate (first ^ " A") term_env type_env)

let test_parse_and_evaluate_11 test_ctxt =
  let zero = parse_and_evaluate "/\\A:*.\\z:A.\\s:A->A.z" (empty_env ()) (empty_env ()) in
  let succ = parse_and_evaluate "\\n:\\/A:*.(A->((A->A)->A))./\\A:*.\\z:A.\\s:A->A.(s (n A z s))" (empty_env ()) (empty_env ()) in
  let result = parse_and_evaluate "/\\A:*.\\z:A.\\s:(A->A).(s z)" (empty_env ()) (empty_env ()) in
    assert_equal (evaluate (App(succ, zero)) (empty_env ()) (empty_env ()))
                 result
  
let test_get_free_term_variables_1 test_ctxt =                 
  assert_equal (get_free_term_variables (parse_and_evaluate "x" (empty_env()) (empty_env()))) ["x"]

let test_get_free_term_variables_2 test_ctxt =                 
  assert_equal (get_free_term_variables (parse_and_evaluate "x y" (empty_env()) (empty_env()))) ["x"; "y"]

let test_get_free_term_variables_3 test_ctxt =                 
  assert_equal (get_free_term_variables (parse_and_evaluate "\\x:X.(a b c d x)" (empty_env()) (empty_env()))) ["a"; "b"; "c"; "d"]

let test_get_free_term_variables_4 test_ctxt =                 
  assert_equal (get_free_term_variables (parse_and_evaluate "/\\X:*.(a X)" (empty_env()) (empty_env()))) ["a"]

let test_get_free_term_variables_5 test_ctxt =                 
  assert_equal (get_free_term_variables (parse_and_evaluate "x Y" (empty_env()) (empty_env()))) ["x"]

let test_get_free_type_variables_in_type_1 test_ctxt =
  let (l1, t1) = (parse_type "X" 0) in
    assert_equal (get_free_type_variables_in_type t1) ["X"]

let test_get_free_type_variables_in_type_2 test_ctxt =
  let (l1, t1) = (parse_type "(X Y)" 0) in
    assert_equal (get_free_type_variables_in_type t1) ["X"; "Y"]

let test_get_free_type_variables_in_type_3 test_ctxt =
  let (l1, t1) = (parse_type "\\X:*.(X A B C D)" 0) in
    assert_equal (get_free_type_variables_in_type t1) ["A"; "B"; "C"; "D"]

let test_get_free_type_variables_in_type_4 test_ctxt =
  let (l1, t1) = (parse_type "\\/X:*.(X A B C D)" 0) in
    assert_equal (get_free_type_variables_in_type t1) ["A"; "B"; "C"; "D"]

let test_get_free_type_variables_in_type_5 test_ctxt =
  let (l1, t1) = (parse_type "X->Y" 0) in
    assert_equal (get_free_type_variables_in_type t1) ["X"; "Y"]

let test_get_free_type_variables_1 test_ctxt =                 
  assert_equal (get_free_type_variables (parse_and_evaluate "x" (empty_env()) (empty_env()))) []

let test_get_free_type_variables_2 test_ctxt =                 
  assert_equal (get_free_type_variables (parse_and_evaluate "x Y" (empty_env()) (empty_env()))) ["Y"]

let test_get_free_type_variables_3 test_ctxt =                 
  assert_equal (get_free_type_variables (parse_and_evaluate "\\x:X.(a X Y d x)" (empty_env()) (empty_env()))) ["X"; "Y"]

let test_get_free_type_variables_4 test_ctxt =                 
  assert_equal (get_free_type_variables (parse_and_evaluate "\\x:X.(a Y d x)" (empty_env()) (empty_env()))) ["X"; "Y"]
  
let test_get_free_type_variables_5 test_ctxt =                 
  assert_equal (get_free_type_variables (parse_and_evaluate "/\\X:*.(a X Y)" (empty_env()) (empty_env()))) ["Y"]

let test_replace_free_vars_1 test_ctxt =
  let term1 = TermVariable "a" in
  let terms = empty_env () in
  let _ = Hashtbl.add terms "a" (Abs(("x", TypeVariable "X"), TermVariable "x")) in
    assert_equal (replace_free_vars term1 terms) (Abs(("x", TypeVariable "X"), TermVariable "x"))

let test_replace_free_vars_2 test_ctxt =
  let term1 = Abs(("x", TypeVariable "X"), TermVariable "a") in
  let terms = empty_env () in
  let _ = Hashtbl.add terms "a" (Abs(("p", TypeVariable "P"), TermVariable "p")) in
    assert_equal (replace_free_vars term1 terms) (Abs(("x", TypeVariable "X"), Abs(("p", TypeVariable "P"), TermVariable "p")))
  
let test_replace_free_vars_3 test_ctxt =
  let term1 = App(TermVariable "a", TermVariable "b") in
  let terms = empty_env () in
  let _ = Hashtbl.add terms "a" (Abs(("p", TypeVariable "P"), TermVariable "p")) in
    assert_equal (replace_free_vars term1 terms) (App(Abs(("p", TypeVariable "P"), TermVariable "p"), TermVariable "b"))

(* this will fail type-checking, but passes muster for unit testing *)  
let test_replace_free_vars_4 test_ctxt =
  let term1 = PApp(TermVariable "a", TypeVariable "B") in
  let terms = empty_env () in
  let _ = Hashtbl.add terms "a" (Abs(("p", TypeVariable "P"), TermVariable "p")) in
  assert_equal (replace_free_vars term1 terms) (PApp(Abs(("p", TypeVariable "P"), TermVariable "p"), TypeVariable "B"))
  
let test_replace_free_vars_5 test_ctxt =
  let term1 = PAbs(("X", TypeKind), TermVariable "a") in
  let terms = empty_env () in
  let _ = Hashtbl.add terms "a" (Abs(("p", TypeVariable "P"), TermVariable "p")) in
    assert_equal (replace_free_vars term1 terms) (PAbs(("X", TypeKind), Abs(("p", TypeVariable "P"), TermVariable "p")))

let test_replace_free_types_1 test_ctxt =
  let term1 = TermVariable "p" in
  let types = empty_env () in
  let _ = Hashtbl.add types "A" (TAbs(("X", TypeKind), TypeVariable "X")) in
    assert_equal (replace_free_types term1 types) term1

let test_replace_free_types_2 test_ctxt =
  let term1 =  Abs(("x", TypeVariable "X"), TermVariable "a") in
  let types = empty_env () in
  let _ = Hashtbl.add types "X" (TAbs(("D", TypeKind), TypeVariable "D")) in
    assert_equal (replace_free_types term1 types) (Abs(("x", TAbs(("D", TypeKind), TypeVariable "D")), TermVariable "a"))
  
let test_replace_free_types_3 test_ctxt =
  let term1 = PApp(TermVariable "p", TypeVariable "A") in
  let types = empty_env () in
  let _ = Hashtbl.add types "A" (TAbs(("X", TypeKind), TypeVariable "X")) in
    assert_equal (replace_free_types term1 types) (PApp(TermVariable "p", TAbs(("X", TypeKind), TypeVariable "X")))

let test_replace_free_types_4 test_ctxt =
  let term1 = App(TermVariable "a", TermVariable "b") in
  let types = empty_env () in
  let _ = Hashtbl.add types "A" (TAbs(("X", TypeKind), TypeVariable "X")) in
  assert_equal (replace_free_types term1 types) term1
  
let test_replace_free_types_5 test_ctxt =
  let term1 =  PAbs(("Y", TypeKind), Abs(("x", TypeVariable "X"), Abs(("p", TypeVariable "P"), TermVariable "p"))) in
  let types = empty_env () in
  let _ = Hashtbl.add types "X" (TAbs(("D", TypeKind), TypeVariable "D")) in
    assert_equal (replace_free_types term1 types)
                 (PAbs(("Y", TypeKind), Abs(("x", TAbs(("D", TypeKind), TypeVariable "D")), Abs(("p", TypeVariable "P"), TermVariable "p")))) 

let test_expand_1 test_ctxt =
  let terms = empty_env () in
  let types = empty_env () in
  let term_env = update_term_env (update_term_env (empty_env ()) "a" (TypeVariable "A")) "b" (TypeVariable "B") in
  let type_env = update_type_env (update_type_env (empty_env ()) "A" TypeKind) "b" TypeKind in
  let _ = Hashtbl.add terms "pair" (parse_and_evaluate "/\\X:*./\\Y:*.\\x:X.\\y:Y./\\R:*.\\p:X->Y->R.(p x y)" (empty_env()) (empty_env())) in
  let _ = Hashtbl.add terms "first" (parse_and_evaluate "/\\X:*./\\Y:*.\\p:\\/R:*.(X->Y->R)->R.(p X \\x:X.\\y:Y.x)" (empty_env()) (empty_env())) in
  let _ = Hashtbl.add terms "pab" (parse_and_evaluate "pair A B" term_env type_env) in
  let _ = Hashtbl.add terms "fab" (parse_and_evaluate "first A B" term_env type_env) in
  let pe = (parse "/\\X:*./\\Y:*.\\p:\\/R:*.(X->Y->R)->R.(p X \\x:X.\\y:Y.x) A B (/\\X:*./\\Y:*.\\x:X.\\y:Y./\\R:*.\\p:X->Y->R.(p x y) A B a b)") in
    match pe with
    | TermEntity term1 -> assert_equal (expand (App(TermVariable "fab", App((App(TermVariable "pab", TermVariable "a"), TermVariable "b")))) terms types)
                          term1
                       
    | _                -> failwith "Parsing resulted in a type when a term was expected"              
  
let tests = "Test suite for FOmega" >:::  [
  "test_get_1" >:: test_get_1;
  "test_get_2" >:: test_get_2;
  "test_get_3" >:: test_get_3;
  "test_get_4" >:: test_get_4;
  "test_get_5" >:: test_get_5;
  "test_get_6" >:: test_get_6;
  "test_get_7" >:: test_get_7;
  "test_get_8" >:: test_get_8;
  "test_get_9" >:: test_get_9;

  "test_equiv_kinds_1" >:: test_equiv_kinds_1;
  "test_equiv_kinds_2" >:: test_equiv_kinds_2;
  "test_equiv_kinds_3" >:: test_equiv_kinds_3;

  "test_replace_type_var_1" >:: test_replace_type_var_1;
  "test_replace_type_var_2" >:: test_replace_type_var_2;
  "test_replace_type_var_3" >:: test_replace_type_var_3;
  "test_replace_type_var_4" >:: test_replace_type_var_4;
  "test_replace_type_var_5" >:: test_replace_type_var_5;
  "test_replace_type_var_6" >:: test_replace_type_var_6;
  "test_replace_type_var_7" >:: test_replace_type_var_7;
  "test_replace_type_var_8" >:: test_replace_type_var_8;
  "test_replace_type_var_9" >:: test_replace_type_var_9;
  "test_replace_type_var_10" >:: test_replace_type_var_10;

  "test_get_kind_1" >:: test_get_kind_1;
  "test_get_kind_2" >:: test_get_kind_2;
  "test_get_kind_3" >:: test_get_kind_3;
  "test_get_kind_4" >:: test_get_kind_4;
  "test_get_kind_5" >:: test_get_kind_5;
  "test_get_kind_6" >:: test_get_kind_6;
  "test_get_kind_7" >:: test_get_kind_7;
  "test_get_kind_8" >:: test_get_kind_8;
  "test_get_kind_9" >:: test_get_kind_9;
  "test_get_kind_10" >:: test_get_kind_10;
  "test_get_kind_11" >:: test_get_kind_11;
  "test_get_kind_12" >:: test_get_kind_12;

  "test_equiv_types_1" >:: test_equiv_types_1;
  "test_equiv_types_2" >:: test_equiv_types_2;
  "test_equiv_types_3" >:: test_equiv_types_3;
  "test_equiv_types_4" >:: test_equiv_types_4;
  "test_equiv_types_5" >:: test_equiv_types_5;
  "test_equiv_types_6" >:: test_equiv_types_6;
  "test_equiv_types_7" >:: test_equiv_types_7;
  "test_equiv_types_8" >:: test_equiv_types_8;
  "test_equiv_types_9" >:: test_equiv_types_9;
  "test_equiv_types_10" >:: test_equiv_types_10;
  "test_equiv_types_11" >:: test_equiv_types_11;
  "test_equiv_types_12" >:: test_equiv_types_12;
  "test_equiv_types_13" >:: test_equiv_types_13;

  "test_get_type_1" >:: test_get_type_1;
  "test_get_type_2" >:: test_get_type_2;
  "test_get_type_3" >:: test_get_type_3;
  "test_get_type_4" >:: test_get_type_4;
  "test_get_type_5" >:: test_get_type_5;
  "test_get_type_6" >:: test_get_type_6;

  "test_is_type_1" >:: test_is_type_1;
  "test_is_type_2" >:: test_is_type_2;

  "test_replace_term_var_1" >:: test_replace_term_var_1;
  "test_replace_term_var_2" >:: test_replace_term_var_2;
  "test_replace_term_var_3" >:: test_replace_term_var_3;
  "test_replace_term_var_4" >:: test_replace_term_var_4;
  "test_replace_term_var_5" >:: test_replace_term_var_5;
  "test_replace_term_var_6" >:: test_replace_term_var_6;
  "test_replace_term_var_7" >:: test_replace_term_var_7;
  "test_replace_term_var_8" >:: test_replace_term_var_8;
  "test_replace_term_var_9" >:: test_replace_term_var_9;
  "test_replace_term_var_10" >:: test_replace_term_var_10;

  "test_replace_type_var_in_term_1" >:: test_replace_type_var_in_term_1;
  "test_replace_type_var_in_term_2" >:: test_replace_type_var_in_term_2;
  "test_replace_type_var_in_term_3" >:: test_replace_type_var_in_term_3;
  "test_replace_type_var_in_term_4" >:: test_replace_type_var_in_term_4;
  "test_replace_type_var_in_term_5" >:: test_replace_type_var_in_term_5;

  "test_reduce_1" >:: test_reduce_1;
  "test_reduce_2" >:: test_reduce_2;
  "test_reduce_3" >:: test_reduce_3;
  "test_reduce_4" >:: test_reduce_4;
  "test_reduce_5" >:: test_reduce_5;
  "test_reduce_6" >:: test_reduce_6;
  "test_reduce_7" >:: test_reduce_7;
  "test_reduce_8" >:: test_reduce_8;
  "test_reduce_9" >:: test_reduce_9;
  "test_reduce_10" >:: test_reduce_10;
  "test_reduce_11" >:: test_reduce_11;
  "test_reduce_12" >:: test_reduce_12;

  "test_evaluate_1" >:: test_evaluate_1;
  "test_evaluate_2" >:: test_evaluate_2;
  "test_evaluate_3" >:: test_evaluate_3;
  "test_evaluate_4" >:: test_evaluate_4;
  "test_evaluate_5" >:: test_evaluate_5;
  "test_evaluate_6" >:: test_evaluate_6;
  "test_evaluate_7" >:: test_evaluate_7;
  "test_evaluate_8" >:: test_evaluate_8;
  "test_evaluate_9" >:: test_evaluate_9;
  "test_evaluate_10" >:: test_evaluate_10;
  "test_evaluate_11" >:: test_evaluate_11;
  "test_evaluate_12" >:: test_evaluate_12;

  "test_split_1" >:: test_split_1;
  "test_split_2" >:: test_split_2;
  "test_split_3" >:: test_split_3;
  "test_split_4" >:: test_split_4;
  "test_split_5" >:: test_split_5;
  "test_split_6" >:: test_split_6;
  "test_split_7" >:: test_split_7;
  "test_split_8" >:: test_split_8;
  "test_split_9" >:: test_split_9;
  "test_split_10" >:: test_split_10;
  "test_split_11" >:: test_split_11;
  "test_split_12" >:: test_split_12;
  "test_split_13" >:: test_split_13;

  "test_parse_1" >:: test_parse_1;
  "test_parse_2" >:: test_parse_2;
  "test_parse_3" >:: test_parse_3;
  "test_parse_4" >:: test_parse_4;
  "test_parse_5" >:: test_parse_5;
  "test_parse_6" >:: test_parse_6;
  "test_parse_7" >:: test_parse_7;
  "test_parse_8" >:: test_parse_8;
  "test_parse_9" >:: test_parse_9;
  "test_parse_10" >:: test_parse_10;
  "test_parse_11" >:: test_parse_11;
  "test_parse_12" >:: test_parse_12;
  "test_parse_13" >:: test_parse_13;
  "test_parse_14" >:: test_parse_14;
  "test_parse_15" >:: test_parse_15;
  "test_parse_16" >:: test_parse_16;
  "test_parse_17" >:: test_parse_17;
  "test_parse_18" >:: test_parse_18;
  "test_parse_19" >:: test_parse_19;
  "test_parse_20" >:: test_parse_20;
  "test_parse_21" >:: test_parse_21;
  "test_parse_22" >:: test_parse_22;
  "test_parse_23" >:: test_parse_23;
  "test_parse_24" >:: test_parse_24;
  "test_parse_25" >:: test_parse_25;
  "test_parse_26" >:: test_parse_26;
  "test_parse_27" >:: test_parse_27;
  "test_parse_28" >:: test_parse_28;
  "test_parse_29" >:: test_parse_29;
  "test_parse_30" >:: test_parse_30;

  "test_parse_and_evaluate_1" >:: test_parse_and_evaluate_1;
  "test_parse_and_evaluate_2" >:: test_parse_and_evaluate_2;
  "test_parse_and_evaluate_3" >:: test_parse_and_evaluate_3;
  "test_parse_and_evaluate_4" >:: test_parse_and_evaluate_4;
  "test_parse_and_evaluate_5" >:: test_parse_and_evaluate_5;
  "test_parse_and_evaluate_6" >:: test_parse_and_evaluate_6;
  "test_parse_and_evaluate_7" >:: test_parse_and_evaluate_7;
  "test_parse_and_evaluate_8" >:: test_parse_and_evaluate_8;
  "test_parse_and_evaluate_9" >:: test_parse_and_evaluate_9;
  "test_parse_and_evaluate_10" >:: test_parse_and_evaluate_10;
  "test_parse_and_evaluate_11" >:: test_parse_and_evaluate_11;

  "test_get_free_term_variables_1" >:: test_get_free_term_variables_1;
  "test_get_free_term_variables_2" >:: test_get_free_term_variables_2;
  "test_get_free_term_variables_3" >:: test_get_free_term_variables_3;
  "test_get_free_term_variables_4" >:: test_get_free_term_variables_4;
  "test_get_free_term_variables_5" >:: test_get_free_term_variables_5;

  "test_get_free_type_variables_in_type_1" >:: test_get_free_type_variables_in_type_1;
  "test_get_free_type_variables_in_type_2" >:: test_get_free_type_variables_in_type_2;
  "test_get_free_type_variables_in_type_3" >:: test_get_free_type_variables_in_type_3;
  "test_get_free_type_variables_in_type_4" >:: test_get_free_type_variables_in_type_4;
  "test_get_free_type_variables_in_type_5" >:: test_get_free_type_variables_in_type_5;
  
  "test_get_free_type_variables_1" >:: test_get_free_type_variables_1;
  "test_get_free_type_variables_2" >:: test_get_free_type_variables_2;
  "test_get_free_type_variables_3" >:: test_get_free_type_variables_3;
  "test_get_free_type_variables_4" >:: test_get_free_type_variables_4;
  "test_get_free_type_variables_5" >:: test_get_free_type_variables_5;

  "test_replace_free_vars_1" >:: test_replace_free_vars_1;
  "test_replace_free_vars_2" >:: test_replace_free_vars_2;
  "test_replace_free_vars_3" >:: test_replace_free_vars_3;
  "test_replace_free_vars_4" >:: test_replace_free_vars_4;
  "test_replace_free_vars_5" >:: test_replace_free_vars_5;

  "test_replace_free_types_1" >:: test_replace_free_types_1;
  "test_replace_free_types_2" >:: test_replace_free_types_2;
  "test_replace_free_types_3" >:: test_replace_free_types_3;
  "test_replace_free_types_4" >:: test_replace_free_types_4;
  "test_replace_free_types_5" >:: test_replace_free_types_5;
  
  "test_expand_1" >:: test_expand_1;
]

let _ = run_test_tt_main tests
