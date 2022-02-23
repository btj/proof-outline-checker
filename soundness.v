Require Import Lia.
Require Export semantics type_checker proof_checker.

(* This definition makes sense only if the semantics is deterministic. *)
Inductive is_safe(S: state)(s: stmt)(Q: state -> Prop): Prop :=
| terminates_is_safe S':
  terminates_in S s S' ->
  Q S' ->
  is_safe S s Q
| diverges_is_safe:
  diverges S s ->
  is_safe S s Q.

Definition int_of_value(v: value): Z :=
  match v with
    VInt z => z
  | VBool b => 0
  end.

Definition bool_of_value(v: value): bool :=
  match v with
    VInt z => false
  | VBool b => b
  end.

Section TypeChecking.

Context (E: env).

Notation type_of := (type_of E).

Section State.

Context (S: state)(HS: forall x, In x E -> S x <> None).

Fixpoint value_of(t: term): value :=
  match t with
    Val l z => VInt z
  | Var l x =>
    match S x with
      None => VInt 0
    | Some z => VInt z
    end
  | BinOp l op t1 t2 =>
    match op with
      Add => VInt (int_of_value (value_of t1) + int_of_value (value_of t2))
    | Sub => VInt (int_of_value (value_of t1) - int_of_value (value_of t2))
    | Eq => VBool (Z.eqb (int_of_value (value_of t1)) (int_of_value (value_of t2)))
    | And => VBool (bool_of_value (value_of t1) && bool_of_value (value_of t2))
    end
  | Not l t => VBool (negb (bool_of_value (value_of t)))
  end.

Definition type_of_value(v: value): type :=
  match v with
    VInt z => TInt
  | VBool b => TBool
  end.

Lemma type_of_value_of t τ:
  type_of t = Some τ ->
  type_of_value (value_of t) = τ.
Proof.
  revert τ.
  induction t; simpl; intros; try congruence.
  - destruct (in_dec string_dec x E); try discriminate.
    injection H; clear H; intros; subst.
    apply HS in i.
    destruct (S x); reflexivity.
  - destruct op.
    + case_eq (type_of t1); intros; rewrite H0 in H; try discriminate.
      destruct t; try discriminate.
      case_eq (type_of t2); intros; rewrite H1 in H; try discriminate.
      destruct t; try discriminate.
      simpl; congruence.
    + case_eq (type_of t1); intros; rewrite H0 in H; try discriminate.
      destruct t; try discriminate.
      case_eq (type_of t2); intros; rewrite H1 in H; try discriminate.
      destruct t; try discriminate.
      simpl; congruence.
    + case_eq (type_of t1); intros; rewrite H0 in H; try discriminate.
      destruct t; try discriminate.
      case_eq (type_of t2); intros; rewrite H1 in H; try discriminate.
      destruct t; try discriminate.
      simpl; congruence.
    + case_eq (type_of t1); intros; rewrite H0 in H; try discriminate.
      destruct t; try discriminate.
      case_eq (type_of t2); intros; rewrite H1 in H; try discriminate.
      destruct t; try discriminate.
      simpl; congruence.
  - destruct (type_of t); try discriminate.
    destruct t0; try discriminate.
    congruence.
Qed.

Lemma VInt_int_of_value_of t:
  type_of t = Some TInt ->
  VInt (int_of_value (value_of t)) = value_of t.
Proof.
  intros.
  apply type_of_value_of in H.
  destruct (value_of t); try discriminate.
  reflexivity.
Qed.

Lemma VBool_bool_of_value_of t:
  type_of t = Some TBool ->
  VBool (bool_of_value (value_of t)) = value_of t.
Proof.
  intros.
  apply type_of_value_of in H.
  destruct (value_of t); try discriminate.
  reflexivity.
Qed.

Lemma value_of_soundness t:
  type_of t <> None ->
  evaluates_to S t (value_of t).
Proof.
  intros.
  case_eq (type_of t); intros; try congruence.
  rename t0 into τ.
  pose proof (type_of_value_of t τ H0).
  clear H.
  revert τ H0 H1.
  induction t; simpl; intros.
  - constructor.
  - destruct (in_dec string_dec x E); try congruence.
    apply HS in i.
    case_eq (S x); intros; try congruence.
    constructor.
    assumption.
  - destruct op.
    + case_eq (type_of t1); intros; rewrite H in H0; try discriminate.
      destruct t; try discriminate.
      case_eq (type_of t2); intros; rewrite H2 in H0; try discriminate.
      destruct t; try discriminate.
      constructor.
      * rewrite VInt_int_of_value_of with (1:=H).
        apply IHt1 with (1:=H).
        apply type_of_value_of with (1:=H).
      * rewrite VInt_int_of_value_of with (1:=H2).
        apply IHt2 with (1:=H2).
        apply type_of_value_of with (1:=H2).
    + case_eq (type_of t1); intros; rewrite H in H0; try discriminate.
      destruct t; try discriminate.
      case_eq (type_of t2); intros; rewrite H2 in H0; try discriminate.
      destruct t; try discriminate.
      constructor.
      * rewrite VInt_int_of_value_of with (1:=H).
        apply IHt1 with (1:=H).
        apply type_of_value_of with (1:=H).
      * rewrite VInt_int_of_value_of with (1:=H2).
        apply IHt2 with (1:=H2).
        apply type_of_value_of with (1:=H2).
    + case_eq (type_of t1); intros; rewrite H in H0; try discriminate.
      destruct t; try discriminate.
      case_eq (type_of t2); intros; rewrite H2 in H0; try discriminate.
      destruct t; try discriminate.
      case_eq (int_of_value (value_of t1) =? int_of_value (value_of t2))%Z; intros.
      * apply Eq_evaluates_to_true with (v:=value_of t1).
        -- apply IHt1 with (1:=H); try assumption.
           apply type_of_value_of; assumption.
        -- assert (value_of t1 = value_of t2). {
             apply Z.eqb_eq in H3.
             pose proof (type_of_value_of t1 TInt H).
             pose proof (type_of_value_of t2 TInt H2).
             destruct (value_of t1); try discriminate.
             destruct (value_of t2); try discriminate.
             simpl in H3.
             congruence.
           }
           rewrite H4.
           apply IHt2 with (1:=H2); try assumption.
           apply type_of_value_of; assumption.
      * apply Eq_evaluates_to_false with (v1:=value_of t1) (v2:=value_of t2).
        -- apply IHt1 with (1:=H); try assumption.
           apply type_of_value_of; assumption.
        -- apply IHt2 with (1:=H2); try assumption.
           apply type_of_value_of; assumption.
        -- apply Z.eqb_neq in H3.
           congruence.
    + case_eq (type_of t1); intros; rewrite H in H0; try discriminate.
      destruct t; try discriminate.
      case_eq (type_of t2); intros; rewrite H2 in H0; try discriminate.
      destruct t; try discriminate.
      constructor.
      * rewrite VBool_bool_of_value_of with (1:=H).
        apply IHt1 with (1:=H).
        apply type_of_value_of; assumption.
      * rewrite VBool_bool_of_value_of with (1:=H2).
        apply IHt2 with (1:=H2).
        apply type_of_value_of with (1:=H2).
  - case_eq (type_of t); intros; rewrite H in H0; try discriminate.
    destruct t0; try discriminate.
    pose proof (type_of_value_of t TBool H).
    destruct (value_of t); try discriminate.
    simpl.
    constructor.
    eauto.
Qed.

Fixpoint value_of_poly(p: list (Z * term)): Z :=
  match p with
    [] => 0
  | (z, t)::p => z * int_of_value (value_of t) + value_of_poly p
  end.

Lemma value_of_poly_scale z p:
  value_of_poly (poly_scale z p) = (z * value_of_poly p)%Z.
Proof.
  induction p.
  - simpl.
    lia.
  - destruct a as [z0 t0].
    simpl.
    rewrite IHp.
    lia.
Qed.

Lemma term_equiv_type_of t1 t2:
  term_equiv t1 t2 ->
  type_of t1 = type_of t2.
Proof.
  induction 1.
  - reflexivity.
  - reflexivity.
  - destruct op; simpl; rewrite IHterm_equiv1; rewrite IHterm_equiv2; reflexivity.
  - simpl. rewrite IHterm_equiv. reflexivity.
Qed.

Lemma term_equivb_type_of t1 t2:
  term_equivb t1 t2 = true ->
  type_of t1 = type_of t2.
Proof.
  intro.
  apply term_equivb_eq_true in H.
  apply term_equiv_type_of; assumption.
Qed.

Lemma term_equiv_value_of t1 t2:
  term_equiv t1 t2 ->
  value_of t1 = value_of t2.
Proof.
  induction 1.
  - reflexivity.
  - reflexivity.
  - destruct op; simpl; congruence.
  - simpl; congruence.
Qed.

Lemma term_equivb_value_of t1 t2:
  term_equivb t1 t2 = true ->
  value_of t1 = value_of t2.
Proof.
  intros.
  apply term_equivb_eq_true in H.
  apply term_equiv_value_of; assumption.
Qed.

Lemma value_of_poly_add_term z t p:
  value_of_poly (poly_add_term z t p) = (z * int_of_value (value_of t) + value_of_poly p)%Z.
Proof.
  induction p.
  - reflexivity.
  - destruct a as [z0 t0].
    simpl.
    case_eq (term_equivb t t0); intro He.
    + apply term_equivb_value_of in He.
      rewrite He.
      destruct (Z.eq_dec (z + z0) 0); simpl; lia.
    + simpl; lia.
Qed.

Lemma value_of_poly_add p1 p2:
  value_of_poly (poly_add p1 p2) = (value_of_poly p1 + value_of_poly p2)%Z.
Proof.
  induction p1.
  - reflexivity.
  - destruct a as [z0 t0].
    simpl.
    rewrite value_of_poly_add_term.
    rewrite IHp1.
    lia.
Qed.

Lemma value_of_poly_subtract p1 p2:
  value_of_poly (poly_subtract p1 p2) = (value_of_poly p1 - value_of_poly p2)%Z.
Proof.
  unfold poly_subtract.
  rewrite value_of_poly_add.
  rewrite value_of_poly_scale.
  lia.
Qed.

Lemma value_of_poly_of t:
  type_of t = Some TInt ->
  value_of_poly (poly_of t) = int_of_value (value_of t).
Proof.
  induction t; cbn - [ Z.mul ]; intros.
  - destruct (Z.eq_dec z 0); simpl; lia.
  - destruct (in_dec string_dec x E); try discriminate.
    apply HS in i.
    destruct (S x); try congruence.
    lia.
  - destruct op.
    + case_eq (type_of t1); intros; rewrite H0 in H; try discriminate.
      destruct t; try discriminate.
      case_eq (type_of t2); intros; rewrite H1 in H; try discriminate.
      destruct t; try discriminate.
      rewrite value_of_poly_add.
      rewrite IHt1 with (1:=H0).
      rewrite IHt2 with (1:=H1).
      reflexivity.
    + case_eq (type_of t1); intros; rewrite H0 in H; try discriminate.
      destruct t; try discriminate.
      case_eq (type_of t2); intros; rewrite H1 in H; try discriminate.
      destruct t; try discriminate.
      rewrite value_of_poly_subtract.
      rewrite IHt1 with (1:=H0).
      rewrite IHt2 with (1:=H1).
      reflexivity.
    + destruct (type_of t1); try discriminate.
      destruct t; try discriminate.
      destruct (type_of t2); try discriminate.
      destruct t; discriminate.
    + destruct (type_of t1); try discriminate.
      destruct t; try discriminate.
      destruct (type_of t2); try discriminate.
      destruct t; discriminate.
  - destruct (type_of t); try discriminate.
    destruct t0; discriminate.
Qed.

Lemma is_Z_tautology_soundness C:
  type_of C = Some TBool ->
  is_Z_tautology C = true ->
  value_of C = VBool true.
Proof.
  intros.
  unfold is_Z_tautology in H0.
  destruct C; try discriminate.
  destruct op; try discriminate.
  simpl.
  case_eq (int_of_value (value_of C1) =? int_of_value (value_of C2))%Z; intros; try reflexivity.
  apply Z.eqb_neq in H1.
  pose proof (value_of_poly_subtract (poly_of C1) (poly_of C2)).
  destruct (poly_subtract (poly_of C1) (poly_of C2)); try discriminate.
  simpl in H2.
  simpl in H.
  case_eq (type_of C1); intros; rewrite H3 in H; try discriminate.
  destruct t; try discriminate.
  case_eq (type_of C2); intros; rewrite H4 in H; try discriminate.
  destruct t; try discriminate.
  rewrite value_of_poly_of with (1:=H3) in H2.
  rewrite value_of_poly_of with (1:=H4) in H2.
  lia.
Qed.

Definition poly_is_wellformed(p: list (Z * term)): Prop :=
  Forall (fun zt => fst zt <> 0%Z) p.

Lemma poly_scale_is_wellformed(z: Z)(p: list (Z * term)):
  z <> 0%Z ->
  poly_is_wellformed p ->
  poly_is_wellformed (poly_scale z p).
Proof.
  intros Hz Hp.
  apply Forall_forall.
  intros [z0 t0] Hz0t0.
  apply in_map_iff in Hz0t0.
  destruct Hz0t0 as [[z1 t1] [? ?]].
  injection H; clear H; intros; subst.
  simpl.
  apply (proj1 (Forall_forall _ _)) with (2:=H0) in Hp.
  intro.
  apply Z.mul_eq_0_r with (2:=Hz) in H.
  simpl in Hp.
  congruence.
Qed.

Lemma poly_add_term_is_wellformed z t p:
  z <> 0%Z ->
  poly_is_wellformed p ->
  poly_is_wellformed (poly_add_term z t p).
Proof.
  intro Hz.
  induction p.
  - intros.
    constructor.
    + assumption.
    + constructor.
  - intros.
    destruct a as [z0 t0].
    inversion H; clear H; subst.
    simpl in H2.
    simpl.
    case_eq (term_equivb t t0); intro He.
    + apply term_equivb_value_of in He.
      destruct (Z.eq_dec (z + z0) 0).
      * assumption.
      * constructor; assumption.
    + constructor.
      * assumption.
      * apply IHp.
        assumption.
Qed.

Lemma poly_add_is_wellformed p1 p2:
  poly_is_wellformed p1 ->
  poly_is_wellformed p2 ->
  poly_is_wellformed (poly_add p1 p2).
Proof.
  intros. revert p1 H.
  induction p1.
  - intros.
    assumption.
  - intros.
    destruct a as [z t].
    inversion H; clear H; subst.
    simpl in H3.
    simpl.
    apply poly_add_term_is_wellformed with (1:=H3).
    apply IHp1.
    assumption.
Qed.

Lemma poly_subtract_is_wellformed p1 p2:
  poly_is_wellformed p1 ->
  poly_is_wellformed p2 ->
  poly_is_wellformed (poly_subtract p1 p2).
Proof.
  intros.
  unfold poly_subtract.
  apply poly_add_is_wellformed; try assumption.
  apply poly_scale_is_wellformed; try lia.
  assumption.
Qed.

Lemma poly_of_is_wellformed t:
  poly_is_wellformed (poly_of t).
Proof.
  induction t; simpl.
  - destruct (Z.eq_dec z 0).
    + constructor.
    + constructor.
      * assumption.
      * constructor.
  - constructor.
    + simpl; lia.
    + constructor.
  - destruct op.
    + apply poly_add_is_wellformed; assumption.
    + apply poly_subtract_is_wellformed; assumption.
    + constructor.
      * simpl; lia.
      * constructor.
    + constructor.
      * simpl; lia.
      * constructor.
  - constructor.
    + simpl; lia.
    + constructor.
Qed.

Lemma poly_lookup_nonzero t p z:
  poly_is_wellformed p ->
  poly_lookup t p = Some z ->
  z <> 0%Z.
Proof.
  induction p.
  - simpl; intros; discriminate.
  - destruct a as [z0 t0].
    intros.
    inversion H; clear H; subst.
    simpl in H3.
    simpl in H0.
    case_eq (term_equivb t t0); intro He; rewrite He in H0; try congruence.
    apply IHp; assumption.
Qed.

Lemma is_Z_entailment0_soundness H C:
  type_of H = Some TBool ->
  type_of C = Some TBool ->
  is_Z_entailment0 H C = true ->
  value_of H = VBool true ->
  value_of C = VBool true.
Proof.
  intros.
  unfold is_Z_entailment0 in H2.
  destruct C; try discriminate.
  destruct op; try discriminate.
  simpl.
  case_eq (int_of_value (value_of C1) =? int_of_value (value_of C2))%Z; intros; try reflexivity.
  apply Z.eqb_neq in H4.
  simpl in H1.
  case_eq (type_of C1); intros; rewrite H5 in H1; try discriminate.
  destruct t; try discriminate.
  case_eq (type_of C2); intros; rewrite H6 in H1; try discriminate.
  destruct t; try discriminate.
  pose proof (value_of_poly_subtract (poly_of C1) (poly_of C2)).
  case_eq (poly_subtract (poly_of C1) (poly_of C2)); [intros H8|intros [z0 t0] pC H8]; rewrite H8 in H2; rewrite H8 in H7. {
    simpl in H7.
    rewrite value_of_poly_of with (1:=H5) in H7.
    rewrite value_of_poly_of with (1:=H6) in H7.
    lia.
  }
  destruct H; try discriminate.
  rename H into tH1.
  rename H9 into tH2.
  destruct op; try discriminate.
  case_eq (poly_lookup t0 (poly_subtract (poly_of tH1) (poly_of tH2))); intros; rewrite H in H2; try discriminate.
  case_eq (poly_subtract (poly_scale z ((z0, t0)::pC)) (poly_scale z0 (poly_subtract (poly_of tH1) (poly_of tH2)))); intros; rewrite H9 in H2; try discriminate.
  elim H4; clear H4.
  simpl in H3.
  injection H3; clear H3; intros.
  apply Z.eqb_eq in H3.
  assert (forall p1 p2, p1 = p2 -> value_of_poly p1 = value_of_poly p2). intros; congruence.
  apply H4 in H9.
  rewrite <- H8 in H9.
  simpl in H9.
  rewrite value_of_poly_subtract in H9.
  rewrite !value_of_poly_scale in H9.
  rewrite !value_of_poly_subtract in H9.
  simpl in H0.
  case_eq (type_of tH1); intros; rewrite H10 in H0; try discriminate.
  destruct t; try discriminate.
  case_eq (type_of tH2); intros; rewrite H11 in H0; try discriminate.
  destruct t; try discriminate.
  rewrite !value_of_poly_of in H9; try assumption.
  assert (int_of_value (value_of tH1) - int_of_value (value_of tH2) = 0)%Z. lia.
  rewrite H12 in H9.
  rewrite Z.mul_0_r in H9.
  apply poly_lookup_nonzero in H.
  rewrite Z.sub_0_r in H9.
  apply Z.mul_eq_0_r with (2:=H) in H9. {
    lia.
  }
  apply poly_subtract_is_wellformed; apply poly_of_is_wellformed.
Qed.

Lemma is_Z_entailment1_soundness H_negated H C:
  type_of H = Some TBool ->
  type_of C = Some TBool ->
  is_Z_entailment1 H_negated H C = true ->
  value_of H = VBool (negb H_negated) ->
  value_of C = VBool true.
Proof.
  revert H_negated.
  induction H; simpl.
  - destruct H_negated; try (intros; discriminate).
  - destruct (S x); intros; discriminate.
  - destruct H_negated; try (intros; discriminate); apply is_Z_entailment0_soundness with (H:=BinOp l op H H0).
  - intros; apply IHterm with (H_negated := negb H_negated); try assumption.
    + destruct (type_of H); try discriminate.
      destruct t; congruence.
    + rewrite Bool.negb_involutive.
      injection H3; clear H3; intros.
      assert (bool_of_value (value_of H) = H_negated). {
        destruct (bool_of_value (value_of H)); destruct H_negated; simpl in H3; congruence.
      }
      rewrite <- H4.
      rewrite VBool_bool_of_value_of. reflexivity.
      destruct (type_of H); try discriminate.
      destruct t; try discriminate.
      reflexivity.
Qed.

Lemma is_Z_entailment_soundness H C:
  type_of H = Some TBool ->
  type_of C = Some TBool ->
  is_Z_entailment H C = true ->
  value_of H = VBool true ->
  value_of C = VBool true.
Proof.
  unfold is_Z_entailment.
  apply is_Z_entailment1_soundness.
Qed.

Fixpoint term_size(t: term): nat :=
  match t with
  | BinOp l op t1 t2 => term_size t1 + term_size t2 + 1
  | Not l t => term_size t + 1
  | _ => 0
  end.

Lemma rewrites_unfold lhs rhs t:
  rewrites lhs rhs t =
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
Proof.
  destruct t; reflexivity.
Qed.

Lemma Forall_flat_map{A B} (P: A -> Prop) (f: B -> list A) (xs: list B):
  Forall (fun y => Forall P (f y)) xs ->
  Forall P (flat_map f xs).
Proof.
  induction 1.
  - constructor.
  - simpl.
    apply Forall_app.
    tauto.
Qed.

Lemma rewrites_soundness lhs rhs t:
  value_of lhs = value_of rhs ->
  Forall (fun t' => value_of t' = value_of t) (rewrites lhs rhs t).
Proof.
  intro.
  apply Wf_nat.induction_ltof1 with (f:=term_size) (a:=t).
  clear t; intros t IH.
  rewrite rewrites_unfold.
  case_eq (term_equivb t lhs); intro He.
  - apply term_equivb_value_of in He; rewrite He.
    constructor.
    + congruence.
    + constructor.
      * assumption.
      * constructor.
  - case_eq (term_equivb t rhs); intro He'.
    + apply term_equivb_value_of in He'; rewrite He'.
      constructor.
      * congruence.
      * constructor.
        -- assumption.
        -- constructor.
    + destruct t; try (constructor; trivial).
      * apply Forall_flat_map.
        apply Forall_forall.
        intros t1' ?.
        apply Forall_forall.
        intros t' ?.
        apply in_map_iff in H1.
        destruct H1 as [t2' [? ?]].
        subst.
        lapply (IH t1). 2:{
          unfold ltof.
          simpl.
          lia.
        }
        intros.
        apply (proj1 (Forall_forall _ _)) with (2:=H0) in H1.
        lapply (IH t2). 2:{
          unfold ltof.
          simpl.
          lia.
        }
        intros.
        apply (proj1 (Forall_forall _ _)) with (2:=H2) in H3.
        destruct op; simpl; congruence.
      * apply Forall_forall.
        intros t0 ?.
        apply in_map_iff in H0.
        destruct H0 as [t' [? ?]].
        subst.
        lapply (IH t). 2:{
          unfold ltof.
          simpl.
          lia.
        }
        intros.
        apply (proj1 (Forall_forall _ _)) with (2:=H1) in H0.
        simpl; congruence.
Qed.

Lemma is_valid_conjunct_entailment_soundness Hs C j:
  Forall (fun H => type_of H = Some TBool) Hs ->
  type_of C = Some TBool ->
  is_valid_conjunct_entailment Hs C j = true ->
  Forall (fun H => value_of H = VBool true) Hs ->
  value_of C = VBool true.
Proof.
  intros.
  unfold is_valid_conjunct_entailment in H1.
  case_eq (existsb (term_equivb C) Hs); intro He; rewrite He in H1. {
    apply existsb_exists in He.
    destruct He as [t [Ht Ht_]].
    apply (proj1 (Forall_forall _ _)) with (2:=Ht) in H2.
    apply term_equivb_value_of in Ht_.
    congruence.
  }
  destruct j as [l|l lk k|l lk1 k1 lk2 k2].
  - apply is_Z_tautology_soundness with (1:=H0) (2:=H1).
  - case_eq (nth_error Hs k); intros; rewrite H3 in H1; try discriminate.
    apply nth_error_In in H3.
    apply (proj1 (Forall_forall _ _)) with (2:=H3) in H.
    apply (proj1 (Forall_forall _ _)) with (2:=H3) in H2.
    apply is_Z_entailment_soundness with (2:=H0) (3:=H1); assumption.
  - case_eq (nth_error Hs k1); intros; rewrite H3 in H1; try discriminate.
    destruct t; try discriminate.
    destruct op; try discriminate.
    case_eq (nth_error Hs k2); intros; rewrite H4 in H1; try discriminate.
    case_eq (existsb (term_equivb C) (rewrites t1 t2 t)); intro He'; rewrite He' in H1; try discriminate.
    apply existsb_exists in He'. destruct He' as [t' [Ht'In Ht']].
    apply term_equivb_value_of in Ht'. rewrite Ht'.
    lapply (rewrites_soundness t1 t2 t). 2:{
      apply nth_error_In in H3.
      apply (proj1 (Forall_forall _ _)) with (2:=H3) in H2.
      simpl in H2.
      case_eq (int_of_value (value_of t1) =? int_of_value (value_of t2))%Z; intros; rewrite H5 in H2; try discriminate.
      apply Z.eqb_eq in H5.
      apply (proj1 (Forall_forall _ _)) with (2:=H3) in H.
      simpl in H.
      case_eq (type_of t1); intros; rewrite H6 in H; try discriminate.
      destruct t0; try discriminate.
      case_eq (type_of t2); intros; rewrite H7 in H; try discriminate.
      destruct t0; try discriminate.
      assert (VInt (int_of_value (value_of t1)) = VInt (int_of_value (value_of t2))). congruence.
      rewrite VInt_int_of_value_of with (1:=H6) in H8.
      rewrite VInt_int_of_value_of with (1:=H7) in H8.
      assumption.
    }
    intros.
    apply (proj1 (Forall_forall _ _)) with (2:=Ht'In) in H5.
    apply nth_error_In in H4.
    apply (proj1 (Forall_forall _ _)) with (2:=H4) in H2.
    congruence.
Qed.

Lemma Forall_nil_iff{A}(P: A -> Prop):
  Forall P [] <-> True.
Proof.
  split; intros.
  - constructor.
  - constructor.
Qed.

Lemma Forall_cons_iff{A}(P: A -> Prop)(x: A)(xs: list A):
  Forall P (x::xs) <-> P x /\ Forall P xs.
Proof.
  split; intros.
  - inversion H; auto.
  - constructor; tauto.
Qed.

Lemma type_of_conjuncts_of P:
  type_of P = Some TBool ->
  Forall (fun P => type_of P = Some TBool) (conjuncts_of P).
Proof.
  induction P; simpl; intros; try discriminate.
  - destruct (in_dec string_dec x E); discriminate.
  - destruct op; try discriminate.
    + destruct (type_of P1); try discriminate.
      destruct t; try discriminate.
      destruct (type_of P2); try discriminate.
      destruct t; discriminate.
    + destruct (type_of P1); try discriminate.
      destruct t; try discriminate.
      destruct (type_of P2); try discriminate.
      destruct t; discriminate.
    + constructor; trivial.
    + case_eq (type_of P1); intros; rewrite H0 in H; try discriminate.
      destruct t; try discriminate.
      case_eq (type_of P2); intros; rewrite H1 in H; try discriminate.
      destruct t; try discriminate.
      apply Forall_app.
      auto.
  - constructor; trivial.
Qed.

Lemma conjuncts_of_soundness P:
  type_of P = Some TBool ->
  value_of P = VBool true <-> Forall (fun C => value_of C = VBool true) (conjuncts_of P).
Proof.
  induction P; try destruct op; try (simpl; rewrite Forall_cons_iff; rewrite Forall_nil_iff; tauto).
  simpl.
  rewrite Forall_app.
  intros.
  case_eq (type_of P1); intros; rewrite H0 in H; try discriminate.
  destruct t; try discriminate.
  case_eq (type_of P2); intros; rewrite H1 in H; try discriminate.
  destruct t; try discriminate.
  assert (forall b1 b2, VBool b1 = VBool b2 <-> b1 = b2). {
    split; congruence.
  }
  rewrite H2.
  assert (forall b1 b2, b1 && b2 = true <-> b1 = true /\ b2 = true)%bool. {
    destruct b1; destruct b2; simpl; tauto.
  }
  rewrite H3.
  rewrite <- !H2.
  rewrite !VBool_bool_of_value_of; try assumption.
  rewrite IHP1; try assumption.
  rewrite IHP2; try assumption.
  reflexivity.
Qed.

Lemma is_valid_entailment_soundness P P' j:
  type_of P = Some TBool ->
  type_of P' = Some TBool ->
  is_valid_entailment P P' j = true ->
  value_of P = VBool true ->
  value_of P' = VBool true.
Proof.
  intros.
  unfold is_valid_entailment in H1.
  rewrite forallb_forall in H1.
  apply conjuncts_of_soundness; try assumption.
  apply Forall_forall.
  intros.
  pose proof H3.
  apply H1 in H3.
  apply is_valid_conjunct_entailment_soundness with (3:=H3).
  - apply type_of_conjuncts_of. assumption.
  - apply type_of_conjuncts_of in H0.
    rewrite Forall_forall in H0.
    apply H0 with (1:=H4).
  - apply conjuncts_of_soundness; assumption.
Qed.

Lemma evaluates_to_unique t v1:
  evaluates_to S t v1 ->
  forall v2,
  evaluates_to S t v2 ->
  v1 = v2.
Proof.
  induction 1; intros.
  - inversion H; clear H; subst; reflexivity.
  - inversion H0; clear H0; subst. congruence.
  - inversion H1; clear H1; subst.
    apply IHevaluates_to1 in H6.
    apply IHevaluates_to2 in H7.
    congruence.
  - inversion H1; clear H1; subst.
    apply IHevaluates_to1 in H6.
    apply IHevaluates_to2 in H7.
    congruence.
  - inversion H1; clear H1; subst.
    + apply IHevaluates_to1 in H6.
      apply IHevaluates_to2 in H7.
      congruence.
    + apply IHevaluates_to1 in H5.
      apply IHevaluates_to2 in H7.
      subst.
      congruence.
  - inversion H2; clear H2; subst.
    + apply IHevaluates_to1 in H7.
      apply IHevaluates_to2 in H8.
      congruence.
    + reflexivity.
  - inversion H1; clear H1; subst.
    apply IHevaluates_to1 in H6.
    apply IHevaluates_to2 in H7.
    congruence.
  - inversion H0; clear H0; subst.
    apply IHevaluates_to in H4.
    injection H4; clear H4; intros; subst.
    reflexivity.
Qed.

Lemma subst_soundness x tx t v:
  type_of tx = Some TInt ->
  evaluates_to S (subst x tx t) v ->
  evaluates_to (update x (int_of_value (value_of tx)) S) t v.
Proof.
  intro Htx.
  revert v.
  induction t; simpl; intros.
  - inversion H; clear H; subst.
    constructor.
  - destruct (string_dec x x0).
    + subst.
      assert (v = value_of tx). {
        apply evaluates_to_unique with (1:=H).
        apply value_of_soundness.
        congruence.
      }
      subst.
      rewrite <- VInt_int_of_value_of with (1:=Htx).
      constructor.
      simpl.
      unfold update.
      destruct (string_dec x0 x0); try congruence.
    + inversion H; clear H; subst.
      constructor.
      unfold update.
      destruct (string_dec x x0); try congruence.
  - inversion H; clear H; subst; try (constructor; auto).
    + eapply Eq_evaluates_to_true; eauto.
    + eapply Eq_evaluates_to_false; eauto.
  - inversion H; clear H; subst.
    constructor.
    auto.
Qed.

End State.

End TypeChecking.

Lemma post_env_of_stmt_mono E s E':
  post_env_of_stmt E s = Some E' ->
  forall x,
  In x E -> In x E'.
Proof.
  revert E E'.
  induction s; intros; simpl in H.
  - simpl in H.
    destruct (type_of E t); try congruence.
    destruct t0; try congruence.
  - destruct (type_of E t); try congruence.
    destruct t0; try congruence.
    injection H; clear H; intros; subst.
    right; assumption.
  - destruct (type_of E t); try congruence.
    destruct t0; try congruence.
    destruct (post_env_of_stmt E s1); try congruence.
    destruct (post_env_of_stmt E s2); try congruence.
  - destruct (type_of E t); try congruence.
    destruct t0; try congruence.
    destruct (post_env_of_stmt E s); try congruence.
  - case_eq (post_env_of_stmt E s1); intros; rewrite H1 in H; try congruence.
    apply IHs1 with (2:=H0) in H1.
    apply IHs2 with (1:=H) (2:=H1).
  - congruence.
Qed.

Fixpoint size_of_stmt(s: stmt): nat :=
  match s with
    If l t s1 s2 => 1 + size_of_stmt s1 + size_of_stmt s2
  | While l t s => 1 + size_of_stmt s
  | Seq s1 s2 => 1 + size_of_stmt s1 + size_of_stmt s2
  | _ => 0
  end.

Require Import Classical.

Lemma soundness_lemma:
  forall E la P j s E' Q,
  post_env_of_stmt E (Assert la P j ;; s) = Some E' ->
  is_valid_proof_outline (Assert la P j ;; s) = true ->
  ends_with_assert (Assert la P j ;; s) Q = true ->
  forall S,
  Forall (fun x => S x <> None) E ->
  evaluates_to S P (VBool true) ->
  (forall S',
   Forall (fun x => S' x <> None) E' ->
   evaluates_to S' Q (VBool true) ->
   ~ terminates_in S s S') ->
  diverges S s.
Proof.
  intros E la P j s E'.
  revert E la P j E'.
  apply Wf_nat.induction_ltof1 with (f:=size_of_stmt) (a:=s).
  clear s.
  intro s.
  intros IH E la P j E' Q Hwelltyped Hvalid Hendswith S HSE HP Hterm.
  simpl in *.
  case_eq (type_of E P); intros; rewrite H in Hwelltyped; try congruence.
  destruct t; try congruence.
  destruct s; simpl in *; try congruence.
  destruct s1; simpl in *; try congruence.
  - (* Assert t j0 *)
    case_eq (type_of E t); intros; rewrite H0 in Hwelltyped; try congruence.
    destruct t0; try congruence.
    destruct j0; try congruence.
    apply andb_prop in Hvalid.
    destruct Hvalid as [Hvalid0 Hvalid].
    assert (Ht: evaluates_to S t (VBool true)). {
      assert (value_of S t = VBool true). {
        apply is_valid_entailment_soundness with (2:=H) (3:=H0) (4:=Hvalid0); try assumption.
        * apply Forall_forall. assumption.
        * apply evaluates_to_unique with (2:=HP).
          apply value_of_soundness with (E:=E).
          -- apply Forall_forall; assumption.
          -- congruence.
      }
      rewrite <- H1.
      apply value_of_soundness with (E:=E).
      * apply Forall_forall; assumption.
      * congruence.
    }
    apply Seq_diverges2 with (S':=S).
    + constructor.
      assumption.
    + apply IH with (E:=E) (la:=l) (P:=t) (Q:=Q) (E':=E'); try assumption.
      * unfold ltof.
        simpl.
        lia.
      * rewrite H0.
        assumption.
      * intros.
        intro.
        elim (Hterm S' H1 H2).
        apply Seq_terminates_in with (S':=S).
        -- constructor.
           assumption.
        -- assumption.
  - (* Assign x t *)
    destruct s2; try congruence.
    destruct s2_1; try congruence.
    rename t0 into P'.
    case_eq (type_of E t); intros; rewrite H0 in Hwelltyped; try congruence.
    destruct t0; try congruence.
    apply andb_prop in Hvalid.
    destruct Hvalid as [Hvalid0 Hvalid].
    pose proof Hvalid0 as Hvalue_of.
    apply term_equivb_value_of with (S:=S) in Hvalue_of.
    apply term_equivb_type_of with (E:=E) in Hvalid0.
    apply Seq_diverges2 with (S':=update x (int_of_value (value_of S t)) S). {
      constructor.
      rewrite VInt_int_of_value_of with (E:=E).
      - apply value_of_soundness with (E:=E).
        + apply Forall_forall; assumption.
        + congruence.
      - apply Forall_forall; assumption.
      - assumption.
    }
    assert (HP'': evaluates_to S (subst x t P') (value_of S (subst x t P'))). {
      apply value_of_soundness with (E:=E).
      - apply Forall_forall; assumption.
      - rewrite <- Hvalid0. congruence.
    }
    assert (HP': evaluates_to (update x (int_of_value (value_of S t)) S) P' (VBool true)). {
      apply subst_soundness with (2:=H0). {
        apply Forall_forall; assumption.
      }
      assert (value_of S (subst x t P') = VBool true). {
        rewrite <- Hvalue_of.
        apply evaluates_to_unique with (2:=HP).
        apply value_of_soundness with (E:=E).
        - apply Forall_forall; assumption.
        - congruence.
      }
      rewrite <- H1.
      assumption.
    }
    apply Seq_diverges2 with (S':=update x (int_of_value (value_of S t)) S). {
      constructor.
      assumption.
    }
    eapply IH with (E:=x :: E) (P:=P') (Q:=Q) (E':=E'); try eassumption.
    + unfold ltof.
      simpl.
      lia.
    + constructor.
      * unfold update.
        destruct (string_dec x x); try congruence.
      * clear Hwelltyped H H0 Hterm Hvalid0. revert E HSE.
        induction E; intros.
        -- constructor.
        -- inversion HSE; clear HSE; subst.
           constructor.
           ++ unfold update.
              destruct (string_dec x a).
              ** congruence.
              ** assumption.
           ++ apply IHE; assumption.
    + intros.
      intro.
      elim (Hterm S' H1 H2).
      apply Seq_terminates_in with (S':=update x (int_of_value (value_of S t)) S).
      * constructor.
        rewrite VInt_int_of_value_of with (2:=H0).
        -- apply value_of_soundness with (E:=E).
           ++ apply Forall_forall; assumption.
           ++ congruence.
        -- apply Forall_forall; assumption.
      * apply Seq_terminates_in with (S':=update x (int_of_value (value_of S t)) S).
        -- constructor.
           assumption.
        -- assumption.
  - case_eq (type_of E t); intros; rewrite H0 in Hwelltyped; try congruence.
    destruct t0; try congruence.
    case_eq (post_env_of_stmt E s1); intros; rewrite H1 in Hwelltyped; try congruence.
    rename e into E'0.
    destruct s1; try congruence.
    destruct s1_1; try congruence.
    destruct s2; try congruence.
    destruct s2_1; try congruence.
    apply andb_prop in Hvalid. destruct Hvalid as [Hvalid Hvalid1].
    apply andb_prop in Hvalid. destruct Hvalid as [Hvalid Hvalid2].
    unfold term_eqb in Hvalid2.
    destruct (term_eq_dec t1 (BinOp And P (Not t))); try congruence. subst.
    clear Hvalid2.
    apply andb_prop in Hvalid. destruct Hvalid as [Hvalid Hvalid2].
    apply andb_prop in Hvalid. destruct Hvalid as [Hvalid Hvalid3].
    unfold term_eqb in Hvalid. destruct (term_eq_dec t0 (BinOp And P t)); try congruence. subst.
    clear Hvalid.
    destruct (classic (exists S', Forall (fun x => S' x <> None) E /\ evaluates_to S' (BinOp And P (Not t)) (VBool true) /\ terminates_in S (While t (Assert (BinOp And P t) j0;; s1_2)) S')). {
      destruct H2 as [S' [HS'E [HS'P Hterminates]]].
      eapply Seq_diverges2; try eassumption.
      apply Seq_diverges2 with (S':=S'). {
        constructor.
        assumption.
      }
      apply IH with (E:=E) (P:=BinOp And P (Not t)) (Q:=Q) (E':=E'); try assumption.
      - unfold ltof.
        simpl; lia.
      - intros.
        intro.
        elim (Hterm S'0 H2 H3).
        apply Seq_terminates_in with (S':=S'); try assumption.
        apply Seq_terminates_in with (S':=S'); try assumption.
        constructor; assumption.
    }
    apply Seq_diverges1.
    revert S HSE HP Hterm H2.
    cofix Hcofix.
    intros.
    constructor.
    assert (evaluates_to S t (VBool true)). {
      case_eq (value_of S t); intros. {
        assert (type_of_value (value_of S t) = TBool). {
          apply type_of_value_of with (E:=E); try assumption.
          apply Forall_forall; assumption.
        }
        rewrite H3 in H4; simpl in H4; congruence.
      }
      destruct b. 2:{
        elim H2.
        exists S.
        split. assumption.
        split. {
          assert (true = true && negb false)%bool. reflexivity.
          rewrite H4.
          constructor. assumption.
          constructor.
          rewrite <- H3.
          apply value_of_soundness with (E:=E); try assumption.
          - apply Forall_forall; assumption.
          - congruence.
        }
        constructor.
        apply If_terminates_in with (b:=false).
        - rewrite <- H3.
          apply value_of_soundness with (E:=E).
          + apply Forall_forall; assumption.
          + congruence.
        - constructor.
      }
      rewrite <- H3.
      apply value_of_soundness with (E:=E).
      * apply Forall_forall; assumption.
      * congruence.
    }
    apply If_diverges with (b:=true).
    + assumption.
    + destruct (classic (exists S'', Forall (fun x => S'' x <> None) E'0 /\ evaluates_to S'' P (VBool true) /\ terminates_in S s1_2 S'')). {
        destruct H4 as [S'' [HS''E'0 [HS''P Hs1_2_terminates]]].
        apply Seq_diverges2 with (S':=S''). {
          apply Seq_terminates_in with (S':=S). {
            constructor.
            assert (true = true && true)%bool. reflexivity.
            rewrite H4.
            constructor; try assumption.
          }
          assumption.
        }
        apply Hcofix; try assumption.
        - apply Forall_forall; intros.
          apply post_env_of_stmt_mono with (1:=H1) in H4.
          apply Forall_forall with (1:=HS''E'0) (2:=H4).
        - intros.
          intro.
          elim (Hterm S' H4 H5).
          inversion H6; clear H6; intros; subst.
          apply Seq_terminates_in with (S':=S'0); try assumption.
          constructor.
          apply If_terminates_in with (b:=true); try assumption.
          apply Seq_terminates_in with (S':=S''); try assumption.
          apply Seq_terminates_in with (S':=S); try assumption.
          constructor.
          assert (true = true && true)%bool. reflexivity.
          rewrite H6.
          constructor; assumption.
        - intro.
          destruct H4 as [S' [HS'E [HS'P Hterminates_in_S']]].
          elim H2.
          exists S'.
          split. assumption.
          split. assumption.
          constructor.
          apply If_terminates_in with (b:=true); try assumption.
          apply Seq_terminates_in with (S':=S''). {
            apply Seq_terminates_in with (S':=S). {
              constructor.
              assert (true = true && true)%bool. reflexivity.
              rewrite H4.
              constructor; assumption.
            }
            assumption.
          }
          assumption.
      }
      apply Seq_diverges1.
      apply Seq_diverges2 with (S':=S). {
        constructor.
        assert (true = true && true)%bool. reflexivity.
        rewrite H5.
        constructor; assumption.
      }
      apply IH with (E:=E) (P:=BinOp And P t) (E':=E'0) (Q:=P); try assumption.
      * unfold ltof. simpl. lia.
      * assert (true = true && true)%bool. reflexivity.
        rewrite H5.
        constructor; assumption.
      * intros.
        intro.
        elim H4.
        exists S'; tauto.
  - (* Pass *)
    injection Hwelltyped; clear Hwelltyped; intros; subst.
    unfold term_eqb in Hendswith.
    destruct (term_eq_dec P Q); try congruence; subst.
    elim (Hterm S HSE HP).
    constructor.
Qed.

Theorem soundness E P j s Q:
  post_env_of_stmt E (Assert P j ;; s) <> None ->
  is_valid_proof_outline (Assert P j ;; s) = true ->
  ends_with_assert (Assert P j ;; s) Q = true ->
  forall S,
  Forall (fun x => S x <> None) E ->
  evaluates_to S P (VBool true) ->
  is_safe S s (fun S' => evaluates_to S' Q (VBool true)).
Proof.
  intros.
  case_eq (post_env_of_stmt E (Assert P j ;; s)); intros; rewrite H4 in H; try congruence.
  rename e into E'.
  destruct (classic (exists S',
   Forall (fun x => S' x <> None) E' /\
   evaluates_to S' Q (VBool true) /\
   terminates_in S s S')).
  - destruct H5 as [S' [? [??]]].
    apply terminates_is_safe with (S':=S'); assumption.
  - apply diverges_is_safe.
    eapply soundness_lemma; try eassumption.
    intros.
    intro.
    elim H5.
    exists S'. tauto.
Qed.
