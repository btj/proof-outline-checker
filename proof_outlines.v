Require Export ZArith.
Require Export String.

(*

assert True
assert 0 == n - n # Z
i = n
assert 0 == n - i
r = 0
assert r == n - i
while i != 0:
  assert r == n - i and i != 0
  assert r + 1 == n - (i - 1) # Z op 1
  i = i - 1
  assert r + 1 == n - i
  r = r + 1
  assert r == n - i
assert r == n - i and not i != 0
assert r == n - i and i == 0 # Z op 2
assert r == n - 0 # Herschrijven met 2 in 1
assert r == n # Z op 1

*)

Definition var := string.

Inductive binop := Add | Sub | Eq | And.
Inductive term :=
| Val(z: Z)
| Var(x: var)
| BinOp(op: binop)(t1 t2: term)
| Not(t: term)
.
Inductive justif :=
| JZ
| JZ_at(k: nat)
| JRewrite(k1 k2: nat)
.
Inductive stmt :=
| Assert(t: term)(j: option justif)
| Assign(x: var)(t: term)
| If(t: term)(s1 s2: stmt)
| While(t: term)(s: stmt)
| Seq(s1 s2: stmt)
| Pass
.

Definition True_term := BinOp Eq (Val 0) (Val 0).

Infix ";;" := Seq (at level 60, right associativity).

Local Open Scope string_scope.

Definition outline1: stmt :=
  Assert True_term None;;
  Assert (BinOp Eq (Val 0) (BinOp Sub (Var "n") (Var "n"))) (Some JZ);;
  Assign "i" (Var "n");;
  Assert (BinOp Eq (Val 0) (BinOp Sub (Var "n") (Var "i"))) None;;
  Assign "r" (Val 0);;
  Assert (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i"))) None;;
  While (Not (BinOp Eq (Var "i") (Val 0))) (
    Assert (BinOp And (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i"))) (Not (BinOp Eq (Var "i") (Val 0)))) None;;
    Assert (BinOp Eq (BinOp Add (Var "r") (Val 1)) (BinOp Sub (Var "n") (BinOp Sub (Var "i") (Val 1)))) (Some (JZ_at 0));;
    Assign "i" (BinOp Sub (Var "i") (Val 1));;
    Assert (BinOp Eq (BinOp Add (Var "r") (Val 1)) (BinOp Sub (Var "n") (Var "i"))) None;;
    Assign "r" (BinOp Add (Var "r") (Val 1));;
    Assert (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i"))) None;;
    Pass
  );;
  Assert (BinOp And (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i"))) (Not (Not (BinOp Eq (Var "i") (Val 0))))) None;;
  Assert (BinOp And (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i"))) (BinOp Eq (Var "i") (Val 0))) (Some (JZ_at 1));;
  Assert (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Val 0))) (Some (JRewrite 1 0));;
  Assert (BinOp Eq (Var "r") (Var "n")) (Some (JZ_at 0));;
  Pass
.
