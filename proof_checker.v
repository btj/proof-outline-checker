Require Export List.
Require Export proof_outlines.

Export ListNotations.

Definition binop_eq_dec(o1 o2: binop): {o1 = o2} + {o1 <> o2}.
decide equality.
Defined.

Definition term_eq_dec(t1 t2: term): {t1 = t2} + {t1 <> t2}.
decide equality.
- apply Z.eq_dec.
- apply string_dec.
- apply binop_eq_dec.
Defined.

Definition term_eqb(t1 t2: term): bool := if term_eq_dec t1 t2 then true else false.

Fixpoint conjuncts_of(P: term): list term :=
  match P with
    BinOp And P1 P2 => conjuncts_of P1 ++ conjuncts_of P2
  | P => [P]
  end.

Definition poly := list (Z * term).

Fixpoint poly_add_term(z: Z)(t: term)(p: poly): poly :=
  match p with
    [] => [(z, t)]
  | (z0, t0)::p =>
    if term_eq_dec t t0 then
      let z1 := (z + z0)%Z in
      if Z.eq_dec z1 0 then
        p
      else
        (z1, t0)::p
    else
      (z0, t0)::poly_add_term z t p
  end.

Fixpoint poly_add(p1 p2: poly): poly :=
  match p1 with
    [] => p2
  | (z1, t1)::p1 => poly_add_term z1 t1 (poly_add p1 p2)
  end.

Definition poly_scale(z: Z)(p: poly): poly :=
  map (fun t: Z * term => let (z0, t0) := t in (z * z0, t0)%Z) p.

Definition poly_subtract(p1 p2: poly): poly :=
  poly_add p1 (poly_scale (-1) p2).

Fixpoint poly_lookup(t: term)(p: poly): option Z :=
  match p with
    [] => None
  | (z0, t0)::p =>
    if term_eq_dec t t0 then Some z0 else poly_lookup t p
  end.

Fixpoint poly_of(t: term): poly :=
  match t with
    Val z => if Z.eq_dec z 0 then [] else [(z, Val 1)]
  | BinOp proof_outlines.Add t1 t2 => poly_add (poly_of t1) (poly_of t2)
  | BinOp Sub t1 t2 => poly_subtract (poly_of t1) (poly_of t2)
  | t => [(1%Z, t)]
  end.

Definition is_Z_tautology(P: term): bool :=
  match P with
    BinOp Eq t1 t2 =>
    let p1 := poly_of t1 in
    let p2 := poly_of t2 in
    match poly_subtract p1 p2 with
      [] => true
    | _ => false
    end
  | _ => false
  end.

Local Open Scope string_scope.

Goal is_Z_tautology (BinOp Eq (Val 0) (BinOp Sub (Var "n") (Var "n"))) = true.
Proof.
  reflexivity.
Qed.

Definition is_Z_entailment0(H C: term): bool :=
  match C with
    BinOp Eq t1 t2 =>
    let pC := poly_subtract (poly_of t1) (poly_of t2) in
    match pC with
      [] => true
    | (zC0, tC0)::pC0 =>
      match H with
        BinOp Eq t1 t2 =>
        let pH := poly_subtract (poly_of t1) (poly_of t2) in
        match poly_lookup tC0 pH with
          None => false
        | Some zH0 =>
          match poly_subtract (poly_scale zH0 pC) (poly_scale zC0 pH) with
            [] => true
          | _ => false
          end
        end
      | _ => false
      end
    end
  | _ => false
  end.

Fixpoint is_Z_entailment1(H_negated: bool)(H C: term): bool :=
  match H with
  | Not H => is_Z_entailment1 (negb H_negated) H C
  | _ => if H_negated then false else is_Z_entailment0 H C
  end.

Definition is_Z_entailment(H C: term): bool := is_Z_entailment1 false H C.

Goal is_Z_entailment
  (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i")))
  (BinOp Eq (BinOp Add (Var "r") (Val 1)) (BinOp Sub (Var "n") (BinOp Sub (Var "i") (Val 1)))) = true.
Proof.
  reflexivity.
Qed.

Fixpoint rewrites(lhs rhs t: term): list term :=
  if term_eq_dec t lhs then
    [rhs; t]
  else if term_eq_dec t rhs then
    [lhs; t]
  else
    match t with
      BinOp op t1 t2 =>
      flat_map (fun t1' =>
        map (fun t2' => BinOp op t1' t2') (rewrites lhs rhs t2)
      ) (rewrites lhs rhs t1)
    | Not t => map (fun t' => Not t') (rewrites lhs rhs t)
    | t => [t]
    end.

Definition is_valid_conjunct_entailment(Hs: list term)(C: term)(j: justif): bool :=
  if in_dec term_eq_dec C Hs then true else
  match j with
    JZ => is_Z_tautology C
  | JZ_at k =>
    match nth_error Hs k with
      None => false
    | Some H => is_Z_entailment H C
    end
  | JRewrite k1 k2 =>
    match nth_error Hs k1 with
    | Some (BinOp Eq LHS RHS) =>
      match nth_error Hs k2 with
        None => false
      | Some H2 =>
        if in_dec term_eq_dec C (rewrites LHS RHS H2) then true else false
      end
    | _ => false
    end
  end.

Definition is_valid_entailment(P P': term)(j: justif): bool :=
  let P_conjuncts := conjuncts_of P in
  let P'_conjuncts := conjuncts_of P' in
  forallb (fun P0 => is_valid_conjunct_entailment P_conjuncts P0 j) P'_conjuncts .

Fixpoint subst(x: var)(t: term)(t0: term): term :=
  match t0 with
    Var y => if string_dec x y then t else t0
  | BinOp op t1 t2 => BinOp op (subst x t t1) (subst x t t2)
  | Not t0 => Not (subst x t t0)
  | _ => t0
  end.

Fixpoint ends_with_assert(s: stmt)(P: term): bool :=
  match s with
    Assert P' _ ;; Pass => term_eqb P' P
  | _ ;; s' => ends_with_assert s' P
  | _ => false
  end.

Fixpoint is_valid_proof_outline(s: stmt): bool :=
  match s with
    Assert P _ ;; (Assert P' (Some j) ;; _) as s =>
    is_valid_entailment P P' j && is_valid_proof_outline s
  | Assert P _ ;; Assign x t ;; (Assert Q _ ;; _) as s =>
    term_eqb P (subst x t Q) && is_valid_proof_outline s
  | Assert Inv _ ;; (While C ((Assert P _ ;; _) as body)) ;; ((Assert Q _ ;; _) as s) =>
    term_eqb P (BinOp And Inv C) && ends_with_assert body Inv &&
    is_valid_proof_outline body && term_eqb Q (BinOp And Inv (Not C)) &&
    is_valid_proof_outline s
  | Assert P _ ;; Pass => true
  | _ => false
  end.

Goal is_valid_proof_outline (
  Assert (BinOp Eq (Var "x") (Val 1)) None;;
  Assert (BinOp Eq (Var "x") (Val 1)) (Some JZ);;
  Pass
) = true.
Proof.
  reflexivity.
Qed.

Goal is_valid_proof_outline (
  Assert (BinOp And (BinOp Eq (Var "x") (Val 1)) (BinOp Eq (Var "y") (Val 1))) None;;
  Assert (BinOp And (BinOp Eq (Var "y") (Val 1)) (BinOp Eq (Var "x") (Val 1))) (Some JZ);;
  Pass
) = true.
Proof.
  reflexivity.
Qed.

Goal is_valid_proof_outline (
    Assert (BinOp And (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i"))) (Not (BinOp Eq (Var "i") (Val 0)))) None;;
    Assert (BinOp Eq (BinOp Add (Var "r") (Val 1)) (BinOp Sub (Var "n") (BinOp Sub (Var "i") (Val 1)))) (Some (JZ_at 0));;
    Assign "i" (BinOp Sub (Var "i") (Val 1));;
    Assert (BinOp Eq (BinOp Add (Var "r") (Val 1)) (BinOp Sub (Var "n") (Var "i"))) None;;
    Assign "r" (BinOp Add (Var "r") (Val 1));;
    Assert (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i"))) None;;
    Pass
) = true.
Proof.
  reflexivity.
Qed.

Goal ends_with_assert (
    Assert (BinOp And (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i"))) (Not (BinOp Eq (Var "i") (Val 0)))) None;;
    Assert (BinOp Eq (BinOp Add (Var "r") (Val 1)) (BinOp Sub (Var "n") (BinOp Sub (Var "i") (Val 1)))) (Some (JZ_at 0));;
    Assign "i" (BinOp Sub (Var "i") (Val 1));;
    Assert (BinOp Eq (BinOp Add (Var "r") (Val 1)) (BinOp Sub (Var "n") (Var "i"))) None;;
    Assign "r" (BinOp Add (Var "r") (Val 1));;
    Assert (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i"))) None;;
    Pass
) (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i"))) = true.
Proof.
  reflexivity.
Qed.

Goal is_valid_proof_outline outline1 = true.
Proof.
  reflexivity.
Qed.