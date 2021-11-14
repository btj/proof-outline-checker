Require Export ZArith.
Require Export String.
Require Extraction.

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

Parameter loc: Set.
Extract Constant loc => "Js.Unsafe.any".
Parameter loc_eq_dec: forall (l1 l2: loc), {l1 = l2} + {l1 <> l2}.
Extract Constant loc_eq_dec => "(fun l1 l2 => failwith ""Not implemented"")".
Parameter locN: Z -> loc. (* Used only in examples in Coq. *)
Extract Constant locN => "(fun _ -> failwith ""Not implemented"")".

Definition var := string.

Inductive binop := Add | Sub | Eq | And.
Inductive term :=
| Val(l: loc)(z: Z)
| Var(l: loc)(x: var)
| BinOp(l: loc)(op: binop)(t1 t2: term)
| Not(l: loc)(t: term)
.
Inductive justif :=
| JZ(l: loc)
| JZ_at(l: loc)(kl: loc)(k: nat)
| JRewrite(l: loc)(k1l: loc)(k1: nat)(k2l: loc)(k2: nat)
.
Inductive stmt :=
| Assert(l: loc)(t: term)(j: option justif)
| Assign(l: loc)(x: var)(t: term)
| If(l: loc)(t: term)(s1 s2: stmt)
| While(l: loc)(t: term)(s: stmt)
| Seq(s1 s2: stmt)
| Pass(l: loc)
.

Definition True_term l := BinOp l Eq (Val l 0) (Val l 0).

Infix ";;" := Seq (at level 60, right associativity).

Local Open Scope string_scope.

Definition outline1: stmt :=
  Assert (locN 0) (True_term (locN 1)) None;;
  Assert (locN 2) (BinOp (locN 3) Eq (Val (locN 4) 0) (BinOp (locN 5) Sub (Var (locN 6) "n") (Var (locN 7) "n"))) (Some (JZ (locN 8)));;
  Assign (locN 9) "i" (Var (locN 10) "n");;
  Assert (locN 11) (BinOp (locN 12) Eq (Val (locN 13) 0) (BinOp (locN 14) Sub (Var (locN 15) "n") (Var (locN 16) "i"))) None;;
  Assign (locN 17) "r" (Val (locN 18) 0);;
  Assert (locN 19) (BinOp (locN 20) Eq (Var (locN 21) "r") (BinOp (locN 22) Sub (Var (locN 23) "n") (Var (locN 24) "i"))) None;;
  While (locN 25) (Not (locN 26) (BinOp (locN 27) Eq (Var (locN 28) "i") (Val (locN 29) 0))) (
    Assert (locN 30) (BinOp (locN 31) And (BinOp (locN 32) Eq (Var (locN 33) "r") (BinOp (locN 34) Sub (Var (locN 35) "n") (Var (locN 36) "i"))) (Not (locN 37) (BinOp (locN 38) Eq (Var (locN 39) "i") (Val (locN 40) 0)))) None;;
    Assert (locN 41) (BinOp (locN 42) Eq (BinOp (locN 43) Add (Var (locN 44) "r") (Val (locN 45) 1)) (BinOp (locN 46) Sub (Var (locN 47) "n") (BinOp (locN 48) Sub (Var (locN 49) "i") (Val (locN 50) 1)))) (Some (JZ_at (locN 51) (locN 52) 0));;
    Assign (locN 53) "i" (BinOp (locN 54) Sub (Var (locN 55) "i") (Val (locN 56) 1));;
    Assert (locN 57) (BinOp (locN 58) Eq (BinOp (locN 59) Add (Var (locN 60) "r") (Val (locN 61) 1)) (BinOp (locN 62) Sub (Var (locN 63) "n") (Var (locN 64) "i"))) None;;
    Assign (locN 65) "r" (BinOp (locN 66) Add (Var (locN 67) "r") (Val (locN 68) 1));;
    Assert (locN 69) (BinOp (locN 70) Eq (Var (locN 71) "r") (BinOp (locN 72) Sub (Var (locN 73) "n") (Var (locN 74) "i"))) None;;
    Pass (locN 75)
  );;
  Assert (locN 76) (BinOp (locN 77) And (BinOp (locN 78) Eq (Var (locN 79) "r") (BinOp (locN 80) Sub (Var (locN 81) "n") (Var (locN 82) "i"))) (Not (locN 83) (Not (locN 84) (BinOp (locN 85) Eq (Var (locN 86) "i") (Val (locN 87) 0))))) None;;
  Assert (locN 88) (BinOp (locN 89) And (BinOp (locN 90) Eq (Var (locN 91) "r") (BinOp (locN 92) Sub (Var (locN 93) "n") (Var (locN 94) "i"))) (BinOp (locN 95) Eq (Var (locN 96) "i") (Val (locN 97) 0))) (Some (JZ_at (locN 98) (locN 99) 1));;
  Assert (locN 100) (BinOp (locN 101) Eq (Var (locN 102) "r") (BinOp (locN 103) Sub (Var (locN 104) "n") (Val (locN 105) 0))) (Some (JRewrite (locN 106) (locN 107) 1 (locN 108) 0));;
  Assert (locN 109) (BinOp (locN 110) Eq (Var (locN 111) "r") (Var (locN 112) "n")) (Some (JZ_at (locN 113) (locN 114) 0));;
  Pass (locN 115)
.

