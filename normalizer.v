Require Export proof_outlines.
Import List.ListNotations.

Open Scope list_scope.

Fixpoint normalize_eq(t: term): term :=
  match t with
    Not l1 (Not l2 t) => normalize_eq t
  | Not l1 (BinOp l2 Le t1 t2) => BinOp l2 Le (BinOp l2 Add t2 (Val l2 1)) t1
  | _ => t
  end.

Fixpoint conjuncts_of(P: term): list term :=
  match P with
    BinOp l And P1 P2 => conjuncts_of P1 ++ conjuncts_of P2
  | P => [P]
  end.

Fixpoint conjunction(l: loc)(ts: list term): term :=
  match ts with
    nil => True_term l
  | [t] => t
  | t::ts => BinOp l And t (conjunction l ts)
  end.

Definition normalize(t: term): term :=
  match t with
    BinOp l And _ _ => conjunction l (List.map normalize_eq (conjuncts_of t))
  | _ => t
  end.
