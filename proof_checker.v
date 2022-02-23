Require Export List.
Require Export proof_outlines.

Export ListNotations.

Inductive term_equiv: term -> term -> Prop :=
| Val_equiv l1 l2 z:
  term_equiv (Val l1 z) (Val l2 z)
| Var_equiv l1 l2 x:
  term_equiv (Var l1 x) (Var l2 x)
| BinOp_equiv la lb op ta1 ta2 tb1 tb2:
  term_equiv ta1 tb1 ->
  term_equiv ta2 tb2 ->
  term_equiv (BinOp la op ta1 ta2) (BinOp lb op tb1 tb2)
| Not_equiv la lb ta tb:
  term_equiv ta tb ->
  term_equiv (Not la ta) (Not lb tb)
.

Definition binop_eq_dec(o1 o2: binop): {o1 = o2} + {o1 <> o2}.
decide equality.
Defined.

Fixpoint term_equivb(t1 t2: term){struct t1}: bool :=
  match t1, t2 with
    Val _ z1, Val _ z2 => Z.eqb z1 z2
  | Var _ x1, Var _ x2 => if string_dec x1 x2 then true else false
  | BinOp _ op1 ta1 tb1, BinOp _ op2 ta2 tb2 =>
    if binop_eq_dec op1 op2 then
      term_equivb ta1 ta2 && term_equivb tb1 tb2
    else
      false
  | Not _ t1, Not _ t2 => term_equivb t1 t2
  | _, _ => false
  end.

Lemma term_equivb_eq_true t1 t2:
  term_equivb t1 t2 = true ->
  term_equiv t1 t2.
Proof.
  revert t1 t2.
  induction t1; intros; simpl in H; destruct t2; try congruence.
  - apply Z.eqb_eq in H.
    subst.
    constructor.
  - destruct (string_dec x x0); try congruence.
    subst.
    constructor.
  - destruct (binop_eq_dec op op0); try congruence. subst.
    apply andb_prop in H.
    destruct H.
    apply IHt1_1 in H.
    apply IHt1_2 in H0.
    constructor; assumption.
  - apply IHt1 in H.
    constructor; assumption.
Qed.

Fixpoint conjuncts_of(P: term): list term :=
  match P with
    BinOp l And P1 P2 => conjuncts_of P1 ++ conjuncts_of P2
  | P => [P]
  end.

Definition poly := list (Z * term).

Fixpoint poly_add_term(z: Z)(t: term)(p: poly): poly :=
  match p with
    [] => [(z, t)]
  | (z0, t0)::p =>
    if term_equivb t t0 then
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
    if term_equivb t t0 then Some z0 else poly_lookup t p
  end.

Fixpoint poly_of(t: term): poly :=
  match t with
    Val l z => if Z.eq_dec z 0 then [] else [(z, Val l 1)]
  | BinOp l proof_outlines.Add t1 t2 => poly_add (poly_of t1) (poly_of t2)
  | BinOp l Sub t1 t2 => poly_subtract (poly_of t1) (poly_of t2)
  | t => [(1%Z, t)]
  end.

Definition is_Z_tautology(P: term): bool :=
  match P with
    BinOp l Eq t1 t2 =>
    let p1 := poly_of t1 in
    let p2 := poly_of t2 in
    match poly_subtract p1 p2 with
      [] => true
    | _ => false
    end
  | _ => false
  end.

Local Open Scope string_scope.

Goal is_Z_tautology (BinOp (locN 0) Eq (Val (locN 1) 0) (BinOp (locN 2) Sub (Var (locN 3) "n") (Var (locN 4) "n"))) = true.
Proof.
  reflexivity.
Qed.

Definition is_Z_entailment0(H C: term): bool :=
  match C with
    BinOp lC Eq t1 t2 =>
    let pC := poly_subtract (poly_of t1) (poly_of t2) in
    match pC with
      [] => true
    | (zC0, tC0)::pC0 =>
      match H with
        BinOp lH Eq t1 t2 =>
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
  | Not l H => is_Z_entailment1 (negb H_negated) H C
  | _ => if H_negated then false else is_Z_entailment0 H C
  end.

Definition is_Z_entailment(H C: term): bool := is_Z_entailment1 false H C.

Goal is_Z_entailment
  (BinOp (locN 0) Eq (Var (locN 1) "r") (BinOp (locN 2) Sub (Var (locN 3) "n") (Var (locN 4) "i")))
  (BinOp (locN 5) Eq (BinOp (locN 6) Add (Var (locN 7) "r") (Val (locN 8) 1)) (BinOp (locN 9) Sub (Var (locN 10) "n") (BinOp (locN 11) Sub (Var (locN 12) "i") (Val (locN 13) 1)))) = true.
Proof.
  reflexivity.
Qed.

Fixpoint rewrites(lhs rhs t: term): list term :=
  if term_equivb t lhs then
    [rhs; t]
  else if term_equivb t rhs then
    [lhs; t]
  else
    match t with
      BinOp l op t1 t2 =>
      flat_map (fun t1' =>
        map (fun t2' => BinOp l op t1' t2') (rewrites lhs rhs t2)
      ) (rewrites lhs rhs t1)
    | Not l t => map (fun t' => Not l t') (rewrites lhs rhs t)
    | t => [t]
    end.

Definition is_valid_conjunct_entailment(Hs: list term)(C: term)(j: justif): bool :=
  if existsb (term_equivb C) Hs then true else
  match j with
    JZ l => is_Z_tautology C
  | JZ_at l lk k =>
    match nth_error Hs k with
      None => false
    | Some H => is_Z_entailment H C
    end
  | JRewrite l lk1 k1 lk2 k2 =>
    match nth_error Hs k1 with
    | Some (BinOp leq Eq LHS RHS) =>
      match nth_error Hs k2 with
        None => false
      | Some H2 =>
        if existsb (term_equivb C) (rewrites LHS RHS H2) then true else false
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
    Var l y => if string_dec x y then t else t0
  | BinOp l op t1 t2 => BinOp l op (subst x t t1) (subst x t t2)
  | Not l t0 => Not l (subst x t t0)
  | _ => t0
  end.

Fixpoint ends_with_assert(s: stmt)(P: term): bool :=
  match s with
    Assert la P' _ ;; Pass lp => term_equivb P' P
  | _ ;; s' => ends_with_assert s' P
  | _ => false
  end.

Inductive result(A E: Type) :=
  ok(a: A)
| error(e: E)
.
Arguments ok {A E} _.
Arguments error {A E} _.

Fixpoint check_proof_outline(s: stmt): result unit (loc * string) :=
  match s with
    Assert laP P _ ;; (Assert laP' P' (Some j) ;; _) as s =>
    if is_valid_entailment P P' j then
      check_proof_outline s
    else
      error (laP', "Could not verify entailment")
  | Assert laP P _ ;; Assign lass x t ;; (Assert laQ Q _ ;; _) as s =>
    if term_equivb P (subst x t Q) then
      check_proof_outline s
    else
      error (laP, "Assignment precondition does not match postcondition with RHS substituted for LHS")
  | Assert laInv Inv _ ;; (While lw C ((Assert laP P _ ;; _) as body)) ;; ((Assert laQ Q _ ;; _) as s) =>
    if term_equivb P (BinOp laInv And Inv C) then
      if ends_with_assert body Inv then
        match check_proof_outline body with
          ok _ =>
          if term_equivb Q (BinOp laInv And Inv (Not laInv C)) then
            check_proof_outline s
          else
            error (laQ, "Loop postcondition does not match conjunction of invariant and negation of condition")
        | error e => error e
        end
      else
        error (lw, "Body of loop does not end with an assert statement that asserts the loop invariant")
    else
      error (laP, "Loop body precondition does not match conjunction of invariant and condition")
  | Assert laP P _ ;; Pass lp => ok tt
  | _ => error (loc_of_stmt s, "Malformed proof outline")
  end.

Goal check_proof_outline (
  Assert (locN 0) (BinOp (locN 1) Eq (Var (locN 2) "x") (Val (locN 3) 1)) None;;
  Assert (locN 4) (BinOp (locN 5) Eq (Var (locN 6) "x") (Val (locN 7) 1)) (Some (JZ (locN 8)));;
  Pass (locN 9)
) = ok tt.
Proof.
  reflexivity.
Qed.

Goal check_proof_outline (
  Assert (locN 0) (BinOp (locN 1) And (BinOp (locN 2) Eq (Var (locN 3) "x") (Val (locN 4) 1)) (BinOp (locN 5) Eq (Var (locN 6) "y") (Val (locN 7) 1))) None;;
  Assert (locN 8) (BinOp (locN 9) And (BinOp (locN 10) Eq (Var (locN 11) "y") (Val (locN 12) 1)) (BinOp (locN 13) Eq (Var (locN 14) "x") (Val (locN 15) 1))) (Some (JZ (locN 16)));;
  Pass (locN 17)
) = ok tt.
Proof.
  reflexivity.
Qed.

Goal check_proof_outline (
    Assert (locN 0) (BinOp (locN 1) And (BinOp (locN 2) Eq (Var (locN 14) "r") (BinOp (locN 3) Sub (Var (locN 4) "n") (Var (locN 5) "i"))) (Not (locN 6) (BinOp (locN 7) Eq (Var (locN 8) "i") (Val (locN 9) 0)))) None;;
    Assert (locN 10) (BinOp (locN 11) Eq (BinOp (locN 12) Add (Var (locN 13) "r") (Val (locN 15) 1)) (BinOp (locN 16) Sub (Var (locN 17) "n") (BinOp (locN 18) Sub (Var (locN 19) "i") (Val (locN 20) 1)))) (Some (JZ_at (locN 21) (locN 22) 0));;
    Assign (locN 23) "i" (BinOp (locN 24) Sub (Var (locN 25) "i") (Val (locN 26) 1));;
    Assert (locN 27) (BinOp (locN 28) Eq (BinOp (locN 29) Add (Var (locN 30) "r") (Val (locN 31) 1)) (BinOp (locN 32) Sub (Var (locN 33) "n") (Var (locN 34) "i"))) None;;
    Assign (locN 35) "r" (BinOp (locN 36) Add (Var (locN 37) "r") (Val (locN 38) 1));;
    Assert (locN 39) (BinOp (locN 40) Eq (Var (locN 41) "r") (BinOp (locN 42) Sub (Var (locN 43) "n") (Var (locN 44) "i"))) None;;
    Pass (locN 45)
) = ok tt.
Proof.
  reflexivity.
Qed.

(*
Goal ends_with_assert (
    Assert (BinOp And (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i"))) (Not (BinOp Eq (Var "i") (Val 0)))) None;;
    Assert (BinOp Eq (BinOp Add (Var "r") (Val 1)) (BinOp Sub (Var "n") (BinOp Sub (Var "i") (Val 1)))) (Some (JZ_at (locN 0) (locN 1) 0));;
    Assign "i" (BinOp Sub (Var "i") (Val 1));;
    Assert (BinOp Eq (BinOp Add (Var "r") (Val 1)) (BinOp Sub (Var "n") (Var "i"))) None;;
    Assign "r" (BinOp Add (Var "r") (Val 1));;
    Assert (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i"))) None;;
    Pass
) (BinOp Eq (Var "r") (BinOp Sub (Var "n") (Var "i"))) = true.
Proof.
  reflexivity.
Qed.
*)

Goal check_proof_outline outline1 = ok tt.
Proof.
  reflexivity.
Qed.