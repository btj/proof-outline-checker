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
      Some TInt, Some TInt => Some TInt
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

End TypeChecking.

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

Inductive poly_evaluates_to(S: var -> option Z): list (Z * term) -> Z -> Prop :=
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
      destruct (Z.eq_dec (z + z0) 0).
      * rewrite e.
        rewrite Z.eqb_refl.
        apply evaluates_to_unique with (1:=H) in H3.
        injection H3; clear H3; intros; subst.
        rewrite Z.add_assoc.
        rewrite <- Z.mul_add_distr_r.
        rewrite e.
        rewrite Z.mul_0_l.
        rewrite Z.add_0_l.
        assumption.
      * 

Lemma poly_add_soundness S p1 z1 p2 z2:
  poly_evaluates_to S p1 z1 ->
  poly_evaluates_to S p2 z2 ->
  poly_evaluates_to S (poly_add p1 p2) (z1 + z2).

Lemma poly_subtract_soundness S p1 z1 p2 z2:
  poly_evaluates_to S p1 z1 ->
  poly_evaluates_to S p2 z2 ->
  poly_evaluates_to S (poly_subtract p1 p2) (z1 - z2).
  

Lemma poly_of_soundness E t:
  type_of E t = Some TInt ->
  forall S,
  Forall (fun x => S x <> None) E ->
  exists z,
  poly_evaluates_to S (poly_of t) z /\
  evaluates_to S t (VInt z).

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
