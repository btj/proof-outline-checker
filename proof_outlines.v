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
Extract Constant loc => "Js_of_ocaml.Js.Unsafe.any".
Parameter loc_eq_dec: forall (l1 l2: loc), {l1 = l2} + {l1 <> l2}.
Extract Constant loc_eq_dec => "(fun l1 l2 => failwith ""Not implemented"")".
Parameter locN: Z -> loc. (* Used only in examples in Coq. *)
Extract Constant locN => "(fun _ -> failwith ""Not implemented"")".

Definition sort := string.

Inductive type := TInt | TBool | TFun(argType resultType: type) | TSort(s: sort).

Definition type_eq_dec(t1 t2: type): {t1 = t2} + {t1 <> t2}.
decide equality.
apply string_dec.
Defined.

Definition type_eqb(t1 t2: type): bool :=
  if type_eq_dec t1 t2 then true else false.

Local Open Scope string_scope.

Fixpoint string_of_type tp :=
  match tp with
    TInt => "TInt"
  | TBool => "TBool"
  | TFun tpa tpr => "TFun (" ++ string_of_type tpa ++ ") (" ++ string_of_type tpr ++ ")"
  | TSort s => s
  end.

Definition var_name := string.
Definition var: Set := var_name * type.

Definition var_eq_dec(x1 x2: var): {x1 = x2} + {x1 <> x2}.
decide equality.
- apply type_eq_dec.
- apply string_dec.
Defined.

Definition var_eqb x1 x2 := if var_eq_dec x1 x2 then true else false.

Definition const_name := string.
Definition const: Set := const_name * type.

Inductive binop := Add | Sub | Eq(tp: type) | Le | And.

Fixpoint string_of_binop op :=
  match op with
    Add => "+"
  | Sub => "-"
  | Eq tp => "==(" ++ string_of_type tp ++ ")"
  | Le => "<="
  | And => "&&"
  end.

Inductive term :=
| Val(l: loc)(z: Z)
| Var(l: loc)(x: var)
| BinOp(l: loc)(op: binop)(t1 t2: term)
| Not(l: loc)(t: term)
| Const(l: loc)(c: const)
| App(l: loc)(f arg: term)
.

Require HexString.

Fixpoint string_of_term t :=
  match t with
    Val l z => HexString.of_Z z
  | Var l (x, tp) => x ++ ":(" ++ string_of_type tp ++ ")"
  | BinOp l op t1 t2 => "(" ++ string_of_term t1 ++ " " ++ string_of_binop op ++ " " ++ string_of_term t2 ++ ")"
  | Not l t => "!" ++ string_of_term t
  | App l f arg => "((" ++ string_of_term f ++ ")(" ++ string_of_term arg ++ "))"
  | Const l (cn, ct) => "[" ++ cn ++ "](" ++ string_of_type ct ++ ")"
  end.

Definition loc_of_term(t: term) :=
  match t with
    Val l z => l
  | Var l x => l
  | BinOp l op t1 t2 => l
  | Not l t => l
  | Const l c => l
  | App l f a => l
  end.

Inductive law := Law(ps: list term)(c: term).

Inductive justif :=
| JZ(l: loc)
| JZ_at(l: loc)(kl: loc)(k: nat)
| JRewrite(l: loc)(k1l: loc)(k1: nat)(k2l: loc)(k2: nat)
| JLaw(l: loc)(law_: law)(ks: list (loc * nat))
| JRewriteWithLaw(l: loc)(law_: law)(ks: list (loc * nat))(lk: loc)(k: nat)
.
Inductive stmt :=
| Assert(l: loc)(t: term)(j: list justif)
| Assign(l: loc)(x: var)(t: term)
| If(l: loc)(t: term)(s1 s2: stmt)
| While(l: loc)(t: term)(s: stmt)
| Seq(s1 s2: stmt)
| Pass(l: loc)
.

Fixpoint loc_of_stmt(s: stmt) :=
  match s with
    Assert l t j => l
  | Assign l x t => l
  | If l t s1 s2 => l
  | While l t s => l
  | Seq s1 s2 => loc_of_stmt s1
  | Pass l => l
  end.

Definition True_term l := BinOp l (Eq TInt) (Val l 0) (Val l 0).

Infix ";;" := Seq (at level 60, right associativity).
