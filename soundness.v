Require Import Lia.
Require Export semantics proof_checker.

Inductive is_safe(S: state)(s: stmt): Prop :=
| terminates_is_safe S':
  terminates_in S s S' ->
  is_safe S s
| diverges_is_safe:
  diverges S s ->
  is_safe S s.

Definition env := list var.

Inductive type := TInt | TBool.

Definition type_eq_dec(t1 t2: type): {t1 = t2} + {t1 <> t2}.
decide equality.
Defined.

Definition type_eqb(t1 t2: type): bool :=
  if type_eq_dec t1 t2 then true else false.

Section TypeChecking.

Context (E: env).

Fixpoint type_of(t: term): option type :=
  match t with
    Val z => Some TInt
  | Var x => if in_dec string_dec x E then Some TInt else None
  | BinOp (Add|Sub) t1 t2 =>
    match type_of t1, type_of t2 with
      Some TInt, Some TInt => Some TInt
    | _, _ => None
    end
  | BinOp Eq t1 t2 =>
    match type_of t1, type_of t2 with
      Some TInt, Some TInt => Some TBool
    | _, _ => None
    end
  | BinOp And t1 t2 =>
    match type_of t1, type_of t2 with
      Some TBool, Some TBool => Some TBool
    | _, _ => None
    end
  | Not t =>
    match type_of t with
      Some TBool => Some TBool
    | _ => None
    end
  end.

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

Section State.

Context (S: state)(HS: forall x, In x E -> S x <> None).

Fixpoint value_of(t: term): value :=
  match t with
    Val z => VInt z
  | Var x =>
    match S x with
      None => VInt 0
    | Some z => VInt z
    end
  | BinOp op t1 t2 =>
    match op with
      Add => VInt (int_of_value (value_of t1) + int_of_value (value_of t2))
    | Sub => VInt (int_of_value (value_of t1) - int_of_value (value_of t2))
    | Eq => VBool (Z.eqb (int_of_value (value_of t1)) (int_of_value (value_of t2)))
    | And => VBool (bool_of_value (value_of t1) && bool_of_value (value_of t2))
    end
  | Not t => VBool (negb (bool_of_value (value_of t)))
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

Lemma value_of_poly_add_term z t p:
  value_of_poly (poly_add_term z t p) = (z * int_of_value (value_of t) + value_of_poly p)%Z.
Proof.
  induction p.
  - reflexivity.
  - destruct a as [z0 t0].
    simpl.
    destruct (term_eq_dec t t0).
    + subst.
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

Lemma Z_tautology_checker_soundness C:
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

Lemma conjunct_entailment_checker_soundness E Hs C j:
  Forall (fun H => type_of E H = Some TBool) Hs ->
  type_of E C = Some TBool ->
  is_valid_conjunct_entailment Hs C j = true ->
  forall S,
  Forall (fun x => S x <> None) E ->
  Forall (fun H => evaluates_to S H (VBool true)) Hs ->
  evaluates_to S C (VBool true).
Proof.

Lemma entailment_checker_soundness E P P' j:
  type_of E P = Some TBool ->
  type_of E P' = Some TBool ->
  is_valid_entailment P P' j = true ->
  forall S,
  Forall (fun x => S x <> None) E ->
  evaluates_to S P (VBool true) ->
  evaluates_to S P' (VBool true).
Proof.

Inductive poly_evaluates_to(S: state): list (Z * term) -> Z -> Prop :=
| empty_poly_evaluates_to:
  poly_evaluates_to S [] 0
| nonempty_poly_evaluates_to z t vt p vp:
  evaluates_to S t (VInt vt) ->
  poly_evaluates_to S p vp ->
  poly_evaluates_to S ((z, t)::p) (z * vt + vp)
.

Lemma poly_scale_soundness S p vp z:
  poly_evaluates_to S p vp ->
  poly_evaluates_to S (poly_scale z p) (z * vp).
Proof.
  revert p vp.
  induction p; intros.
  - inversion H; clear H; subst.
    rewrite Z.mul_0_r.
    constructor.
  - inversion H; clear H; subst.
    simpl.
    rewrite Z.mul_add_distr_l.
    rewrite Z.mul_assoc.
    constructor; auto.
Qed.

Lemma evaluates_to_unique S t v1:
  evaluates_to S t v1 ->
  forall v2,
  evaluates_to S t v2 ->
  v1 = v2.
Proof.
  induction 1; intros.
  - inversion H; clear H; subst; reflexivity.
  - inversion H0; clear H0; subst. congruence.
  - inversion H1; clear H1; subst.
    apply IHevaluates_to1 in H4.
    apply IHevaluates_to2 in H6.
    congruence.
  - inversion H1; clear H1; subst.
    apply IHevaluates_to1 in H4.
    apply IHevaluates_to2 in H6.
    congruence.
  - inversion H1; clear H1; subst.
    + apply IHevaluates_to1 in H4.
      apply IHevaluates_to2 in H6.
      congruence.
    + apply IHevaluates_to1 in H4.
      apply IHevaluates_to2 in H5.
      subst.
      congruence.
  - inversion H2; clear H2; subst.
    + apply IHevaluates_to1 in H5.
      apply IHevaluates_to2 in H7.
      congruence.
    + reflexivity.
  - inversion H0; clear H0; subst.
    apply IHevaluates_to in H2.
    injection H2; clear H2; intros; subst.
    reflexivity.
Qed.

Lemma poly_add_term_soundness S z t vt p vp:
  evaluates_to S t (VInt vt) ->
  poly_evaluates_to S p vp ->
  poly_evaluates_to S (poly_add_term z t p) (z * vt + vp).
Proof.
  revert p vp.
  induction p; intros.
  - inversion H0; clear H0; subst.
    simpl.
    constructor; auto.
    constructor.
  - inversion H0; clear H0; subst.
    simpl.
    destruct (term_eq_dec t t0).
    + subst.
      apply evaluates_to_unique with (1:=H) in H3.
      injection H3; clear H3; intros; subst.
      destruct (Z.eq_dec (z + z0) 0).
      * rewrite Z.add_assoc.
        rewrite <- Z.mul_add_distr_r.
        rewrite e.
        rewrite Z.mul_0_l.
        rewrite Z.add_0_l.
        assumption.
      * rewrite Z.add_assoc.
        rewrite <- Z.mul_add_distr_r.
        constructor; assumption.
    + rewrite Z.add_assoc.
      rewrite Z.add_comm with (n:=(z * vt)%Z).
      rewrite <- Z.add_assoc.
      constructor; auto.
Qed.

Lemma poly_add_soundness S p1 z1 p2 z2:
  poly_evaluates_to S p1 z1 ->
  poly_evaluates_to S p2 z2 ->
  poly_evaluates_to S (poly_add p1 p2) (z1 + z2).
Proof.
  intros.
  induction H.
  - simpl.
    tauto.
  - simpl.
    rewrite <- Z.add_assoc.
    apply poly_add_term_soundness; assumption.
Qed.

Lemma poly_subtract_soundness S p1 z1 p2 z2:
  poly_evaluates_to S p1 z1 ->
  poly_evaluates_to S p2 z2 ->
  poly_evaluates_to S (poly_subtract p1 p2) (z1 - z2).
Proof.
  intros.
  unfold poly_subtract.
  assert (z1 - z2 = z1 + (-1) * z2)%Z. lia. rewrite H1. clear H1.
  apply poly_add_soundness; try assumption.
  apply poly_scale_soundness.
  assumption.
Qed.

Lemma poly_of_soundness E t:
  type_of E t = Some TInt ->
  forall S,
  Forall (fun x => S x <> None) E ->
  exists z,
  poly_evaluates_to S (poly_of t) z /\
  evaluates_to S t (VInt z).
Proof.
  intros.
  revert H.
  induction t; simpl; intros.
  - exists z. split.
    + destruct (Z.eq_dec z 0).
      * subst. constructor.
      * assert (z = z * 1 + 0)%Z. lia. rewrite H1 at 2. clear H1.
        constructor.
        -- constructor.
        -- constructor.
    + constructor.
  - destruct (in_dec string_dec x E). 2:{ discriminate. }
    clear H.
    apply (proj1 (Forall_forall _ _)) with (2:=i) in H0.
    case_eq (S x); intros; try tauto.
    exists z.
    assert (evaluates_to S (Var x) (VInt z)). constructor; assumption.
    split; [|assumption].
    assert (z = 1 * z + 0)%Z. lia. rewrite H2. clear H2.
    constructor; try assumption.
    constructor.
  - destruct op.
    + (* Add *)
      case_eq (type_of E t1); intros; rewrite H1 in H.
      destruct t; try discriminate.
      case_eq (type_of E t2); intros; rewrite H2 in H.
      destruct t; try discriminate.
      

Lemma Z_tautology_checker_soundness E C:
  type_of E C = Some TBool ->
  is_Z_tautology C = true ->
  forall S,
  Forall (fun x => S x <> None) E ->
  evaluates_to S C (VBool true).
Proof.
  
Lemma conjunct_entailment_checker_soundness E Hs C j:
  Forall (fun H => type_of E H = Some TBool) Hs ->
  type_of E C = Some TBool ->
  is_valid_conjunct_entailment Hs C j = true ->
  forall S,
  Forall (fun x => S x <> None) E ->
  Forall (fun H => evaluates_to S H (VBool true)) Hs ->
  evaluates_to S C (VBool true).
Proof.

Lemma entailment_checker_soundness E P P' j:
  type_of E P = Some TBool ->
  type_of E P' = Some TBool ->
  is_valid_entailment P P' j = true ->
  forall S,
  Forall (fun x => S x <> None) E ->
  evaluates_to S P (VBool true) ->
  evaluates_to S P' (VBool true).
Proof.
  
Fixpoint stmt_is_well_typed(E: env)(s: stmt): option env :=
  match s with
    Assert P j =>
    match type_of E P with
      Some TBool => Some E
    | _ => None
    end
  | Assign x t =>
    match type_of E t with
      Some TInt => Some (x::E)
    | _ => None
    end
  | Pass => Some E
  | If C s1 s2 =>
    match type_of E C with
      Some TBool =>
      match stmt_is_well_typed E s1 with
        Some E1 =>
        match stmt_is_well_typed E s2 with
          Some E2 =>
          Some E
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  | While C s =>
    match type_of E C with
      Some TBool =>
      match stmt_is_well_typed E s with
        Some _ => Some E
      | _ => None
      end
    | _ => None
    end
  | s1 ;; s2 =>
    match stmt_is_well_typed E s1 with
      Some E => stmt_is_well_typed E s2
    | None => None
    end
  end.


Lemma soundness_lemma:
  forall E P j s,
  stmt_is_well_typed E (Assert P j ;; s) <> None ->
  is_valid_proof_outline (Assert P j ;; s) = true ->
  forall S,
  Forall (fun x => S x <> None) E ->
  evaluates_to S P (VBool true) ->
  (forall S', ~ terminates_in S s S') ->
  diverges S s.
Proof.
  cofix Hcofix.
  intros.
  destruct s; simpl in H0; try discriminate.
  - destruct s1; simpl in H0.
    + apply Seq_diverges2 with (S':=S).
      * constructor.

Theorem soundness E P j s:
  stmt_is_well_typed E (Assert P j ;; s) <> None ->
  is_valid_proof_outline (Assert P j ;; s) = true ->
  forall S,
  Forall (fun x => S x <> None) E ->
  evaluates_to S P (VBool true) ->
  is_safe S s.
