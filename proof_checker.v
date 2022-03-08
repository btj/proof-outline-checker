Require Export List.
Require Export normalizer.

Export ListNotations.

Inductive result(A E: Type) :=
  Ok(a: A)
| Error(e: E)
.
Arguments Ok {A E} _.
Arguments Error {A E} _.

Inductive term_equiv: term -> term -> Prop :=
| Val_equiv l1 l2 z:
  term_equiv (Val l1 z) (Val l2 z)
| Var_equiv l1 l2 x:
  term_equiv (Var l1 x) (Var l2 x)
| BinOp_equiv la lb op ta1 ta2 tb1 tb2:
  term_equiv ta1 tb1 ->
  term_equiv ta2 tb2 ->
  term_equiv (BinOp la op ta1 ta2) (BinOp lb op tb1 tb2)
| Eq_equiv' tp la lb ta1 ta2 tb1 tb2:
  term_equiv ta1 tb2 ->
  term_equiv ta2 tb1 ->
  term_equiv (BinOp la (Eq tp) ta1 ta2) (BinOp lb (Eq tp) tb1 tb2)
| Not_equiv la lb ta tb:
  term_equiv ta tb ->
  term_equiv (Not la ta) (Not lb tb)
| Const_equiv l1 l2 c:
  term_equiv (Const l1 c) (Const l2 c)
| App_equiv la lb ta1 ta2 tb1 tb2:
  term_equiv ta1 tb1 ->
  term_equiv ta2 tb2 ->
  term_equiv (App la ta1 ta2) (App lb tb1 tb2)
.

Definition binop_eq_dec(o1 o2: binop): {o1 = o2} + {o1 <> o2}.
decide equality.
apply type_eq_dec.
Defined.

Definition binop_eqb o1 o2 := if binop_eq_dec o1 o2 then true else false.

Definition const_eq_dec(c1 c2: const): {c1 = c2} + {c1 <> c2}.
Proof.
  destruct c1 as [n1 tp1].
  destruct c2 as [n2 tp2].
  destruct (string_dec n1 n2).
  - subst.
    destruct (type_eq_dec tp1 tp2).
    + subst.
      left.
      reflexivity.
    + right.
      congruence.
  - right.
    congruence.
Defined.

Fixpoint term_equivb(t1 t2: term){struct t1}: bool :=
  match t1, t2 with
    Val _ z1, Val _ z2 => Z.eqb z1 z2
  | Var _ x1, Var _ x2 => if var_eq_dec x1 x2 then true else false
  | BinOp _ op1 ta1 tb1, BinOp _ op2 ta2 tb2 =>
    if binop_eq_dec op1 op2 then
      term_equivb ta1 ta2 && term_equivb tb1 tb2 ||
      match op1 with
        Eq _ => term_equivb ta1 tb2 && term_equivb tb1 ta2
      | _ => false
      end
    else
      false
  | Not _ t1, Not _ t2 => term_equivb t1 t2
  | Const _ c1, Const _ c2 => if const_eq_dec c1 c2 then true else false
  | App _ f1 a1, App _ f2 a2 => term_equivb f1 f2 && term_equivb a1 a2
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
  - destruct (var_eq_dec x x0); try congruence.
    subst.
    constructor.
  - destruct (binop_eq_dec op op0); try congruence. subst.
    apply Bool.orb_prop in H.
    destruct H.
    + apply andb_prop in H.
      destruct H.
      apply IHt1_1 in H.
      apply IHt1_2 in H0.
      constructor; assumption.
    + destruct op0; try discriminate.
      subst.
      apply andb_prop in H.
      destruct H.
      apply IHt1_1 in H.
      apply IHt1_2 in H0.
      constructor; assumption.
  - apply IHt1 in H.
    constructor; assumption.
  - destruct (const_eq_dec c c0).
    + subst. apply Const_equiv.
    + discriminate.
  - apply andb_prop in H.
    destruct H.
    apply IHt1_1 in H.
    apply IHt1_2 in H0.
    constructor; assumption.
Qed.

Definition term_equivb' t1 t2 := term_equivb (normalize t1) (normalize t2).

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
    BinOp l (Eq TInt) t1 t2 =>
    let p1 := poly_of t1 in
    let p2 := poly_of t2 in
    match poly_subtract p1 p2 with
      [] => true
    | _ => false
    end
  | BinOp l Le t1 t2 =>
    let p1 := poly_of t1 in
    let p2 := poly_of t2 in
    match poly_subtract p2 p1 with
      [] => true
    | [(z, Val _ 1)] => Z.leb 0 z
    | _ => false
    end
  | _ => false
  end.

Local Open Scope string_scope.

Fixpoint normalize_eq(t: term): term :=
  match t with
    Not l1 (Not l2 t) => normalize_eq t
  | Not l1 (BinOp l2 Le t1 t2) => BinOp l2 Le (BinOp l2 Add t2 (Val l2 1)) t1
  | _ => t
  end.

Definition is_Z_entailment(H C: term): bool :=
  match normalize_eq C with
    BinOp lC (Eq TInt) t1 t2 =>
    let pC := poly_subtract (poly_of t1) (poly_of t2) in
    match pC with
      [] => true
    | (zC0, tC0)::pC0 =>
      match normalize_eq H with
        BinOp lH (Eq TInt) t1 t2 =>
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
  | BinOp lC Le t1 t2 =>
    let pC := poly_subtract (poly_of t2) (poly_of t1) in
    let (pC', Cconst) :=
      match poly_lookup (Val lC 1) pC with
        None => (pC, 0%Z)
      | Some z => (poly_add_term (-z) (Val lC 1) pC, 0%Z)
      end
    in
    match pC' with
      [] => Z.leb 0 Cconst
    | (zC0, tC0)::pC0 =>
      match normalize_eq H with
        BinOp lH (Eq TInt) t1 t2 =>
        let pH := poly_subtract (poly_of t1) (poly_of t2) in
        match poly_lookup tC0 pH with
          None => false
        | Some zH0 =>
          match poly_subtract (poly_scale zH0 pC) (poly_scale zC0 pH) with
            [] => true
          | [(z, Val _ 1)] => Z.leb 0 (Z.mul z zH0)
          | _ => false
          end
        end
      | BinOp lJ Le t1 t2 =>
        let pH := poly_subtract (poly_of t2) (poly_of t1) in
        match poly_lookup tC0 pH with
          None => false
        | Some zH0 =>
          match poly_subtract (poly_scale zH0 pC) (poly_scale zC0 pH) with
            [] => true
          | [(z, Val _ 1)] => Z.leb 0 (Z.mul z zH0)
          | _ => false
          end
        end
      | _ => false
      end
    end
  | _ => false
  end.

Fixpoint rewrites(lhs rhs t: term): list term :=
  (if term_equivb t lhs then [rhs] else if term_equivb t rhs then [lhs] else []) ++
  match t with
    BinOp l op t1 t2 =>
    flat_map (fun t1' =>
      map (fun t2' => BinOp l op t1' t2') (rewrites lhs rhs t2)
    ) (rewrites lhs rhs t1)
  | Not l t => map (fun t' => Not l t') (rewrites lhs rhs t)
  | App l t1 t2 =>
    flat_map (fun t1' =>
      map (fun t2' => App l t1' t2') (rewrites lhs rhs t2)
    ) (rewrites lhs rhs t1)
  | t => [t]
  end.

Definition update(f: var -> option term)(x: var)(t: term)(y: var): option term :=
  if var_eq_dec x y then Some t else f y.

Fixpoint match_term f c C :=
  match c, C with
    Var _ x, t =>
    match f x with
      None => Some (update f x t)
    | Some t' =>
      if term_equivb t t' then Some f else None
    end
  | Val _ v, Val _ v' => if Z.eqb v v' then Some f else None
  | BinOp _ op t1 t2, BinOp _ op' t1' t2' =>
    if binop_eq_dec op op' then
      match match_term f t1 t1' with
        None =>
        match op with
          Eq _ =>
          match match_term f t1 t2' with
            Some f =>
            match_term f t2 t1'
          | None => None
          end
        | _ => None
        end
      | Some f =>
        match_term f t2 t2'
      end
    else
      None
  | Not _ t, Not _ t' =>
    match_term f t t'
  | Const _ c, Const _ c' => if const_eq_dec c c' then Some f else None
  | App _ tf ta, App _ tf' ta' =>
    match match_term f tf tf' with
      None => None
    | Some f =>
      match_term f ta ta'
    end
  | _, _ => None
  end.

Fixpoint match_law_premises{A}(l: loc)(f: var -> option term)(Hs: list term)(ps: list term)(ks: list (loc * nat))(cont: (var -> option term) -> result A (loc * string)): result A (loc * string) :=
  match ps, ks with
    [], [] => cont f
  | p::ps, (lk, k)::ks =>
    match nth_error Hs k with
    | None => Error (lk, "Conjunct index out of range")
    | Some H =>
      match match_term f p H with
      | None => Error (lk, "Conjunct does not match corresponding law premise")
      | Some f =>
        match_law_premises l f Hs ps ks cont
      end
    end
  | _, _ => Error (l, "Number of conjunct indices does not match number of law premises")
  end.

Definition law_application_checker_for(l: loc)(f: var -> option term)(Hs: list term)(ps: list term)(c: term)(ks: list (loc * nat)): result (term -> bool) (loc * string) :=
  match_law_premises l f Hs ps ks (fun f =>
    Ok (fun C =>
      match match_term f c C with
      | None => false
      | Some _ => true
      end
    )
  ).

Fixpoint type_of_term t :=
  match t with
    Val _ _ => TInt
  | Var _ (x, tp) => tp
  | BinOp _ (Eq _|Le|And) _ _ => TBool
  | BinOp _ (Add|Sub) _ _ => TInt
  | Not _ _ => TBool
  | Const _ (c, tp) => tp
  | App _ t1 t2 =>
    match type_of_term t1 with
      TFun _ tp => tp
    | _ => TBool (* Dummy value, never happens for well-typed terms *)
    end
  end.

Fixpoint can_rewrite(f: var -> option term)(lhs rhs t1 t2: term): bool :=
  term_equivb t1 t2 ||
  type_eqb (type_of_term lhs) (type_of_term t1) && (
    match match_term f lhs t1 with
      Some f =>
      match match_term f rhs t2 with
        Some _ => true
      | None => false
      end
    | _ => false
    end ||
    match match_term f rhs t1 with
      Some f =>
      match match_term f lhs t2 with
        Some _ => true
      | None => false
      end
    | _ => false
    end
  ) ||
  match t1, t2 with
  | BinOp _ op1 t11 t12, BinOp _ op2 t21 t22 =>
    binop_eqb op1 op2 &&
    (can_rewrite f lhs rhs t11 t21 && can_rewrite f lhs rhs t12 t22 ||
     match op1 with
       Eq _ => can_rewrite f lhs rhs t11 t22 && can_rewrite f lhs rhs t12 t21
     | _ => false
     end)
  | Not _ t1, Not _ t2 =>
    can_rewrite f lhs rhs t1 t2
  | App _ t11 t12, App _ t21 t22 =>
    can_rewrite f lhs rhs t11 t21 && can_rewrite f lhs rhs t12 t22
  | _, _ => false
  end.

Definition conjunct_entailment_checker_for(Hs: list term)(j: justif): result (term -> bool) (loc * string) :=
  match j with
    JZ l => Ok is_Z_tautology
  | JZ_at l lk k =>
    match nth_error Hs k with
      None => Error (lk, "Conjunct index out of range")
    | Some H => Ok (is_Z_entailment H)
    end
  | JRewrite l lk1 k1 lk2 k2 =>
    match nth_error Hs k1 with
    | Some H =>
      match H with
      | BinOp leq (Eq _) LHS RHS =>
        match nth_error Hs k2 with
          None => Error (lk2, "Conjunct index out of range")
        | Some H2 =>
          Ok (fun C => if existsb (term_equivb C) (rewrites LHS RHS H2) then true else false)
        end
      | _ => Error (loc_of_term H, "Equality expected")
      end
    | _ => Error (lk1, "Conjunct index out of range")
    end
  | JLaw l (Law ps c) ks =>
    law_application_checker_for l (fun _ => None) Hs ps c ks
  | JRewriteWithLaw l (Law ps c) ks lk k =>
    match c with
      BinOp _ (Eq tp) lhs rhs =>
      match_law_premises l (fun _ => None) Hs ps ks (fun f =>
        match nth_error Hs k with
          Some H =>
          Ok (fun C => can_rewrite f lhs rhs H C)
        | None => Error (lk, "Conjunct index out of range")
        end
      )
    | _ => Error (l, "Conclusion of law is not an equality")
    end
  end.

Fixpoint check_all{A B E}(checker: A -> result B E)(xs: list A): result (list B) E :=
  match xs with
    [] => Ok []
  | x::xs =>
    match checker x with
      Ok y =>
      match check_all checker xs with
        Ok ys => Ok (y::ys)
      | Error e => Error e
      end
    | Error e => Error e
    end
  end.

Definition check_conjunct_entailment(Hs: list term)(checkers: list (term -> bool))(C: term): result unit (loc * string) :=
  if
    (existsb (term_equivb C) Hs ||
     existsb (fun checker => checker C) checkers ||
     match C with
       BinOp _ (Eq _) t1 t2 =>
       term_equivb t1 t2
     | _ => false
     end)%bool
  then
    Ok tt
  else
    Error (loc_of_term C, "Conjunct not justified").

Definition check_entailment(P P': term)(js: list justif): result unit (loc * string) :=
  let Hs := conjuncts_of P in
  match check_all (conjunct_entailment_checker_for Hs) js with
    Error e => Error e
  | Ok checkers =>
    let Cs := conjuncts_of P' in
    match check_all (check_conjunct_entailment Hs checkers) Cs with
      Ok _ => Ok tt
    | Error e => Error e
    end
  end.

Fixpoint subst(x: var)(t: term)(t0: term): term :=
  match t0 with
  | Val _ _ => t0
  | Var l y => if var_eq_dec x y then t else t0
  | BinOp l op t1 t2 => BinOp l op (subst x t t1) (subst x t t2)
  | Not l t0 => Not l (subst x t t0)
  | Const _ _ => t0
  | App l tf targ => App l (subst x t tf) (subst x t targ)
  end.

Fixpoint ends_with_assert(s: stmt)(P: term): bool :=
  match s with
    Assert la P' _ ;; Pass lp => term_equivb' P' P
  | _ ;; s' => ends_with_assert s' P
  | _ => false
  end.

Fixpoint free_vars(t: term): list var :=
  match t with
    Var _ x => [x]
  | Val _ v => []
  | BinOp _ _ t1 t2 => free_vars t1 ++ free_vars t2
  | Not _ t => free_vars t
  | Const _ _ => []
  | App _ tf ta => free_vars tf ++ free_vars ta
  end.

Fixpoint assigned_vars(s: stmt): list var :=
  match s with
    Assert _ _ _ => []
  | Assign _ x t => [x]
  | If _ C s1 s2 => assigned_vars s1 ++ assigned_vars s2
  | While _ C body => assigned_vars body
  | s1 ;; s2 => assigned_vars s1 ++ assigned_vars s2
  | Pass _ => []
  end.

Fixpoint check_proof_outline(total: bool)(s: stmt): result unit (loc * string) :=
  match s with
    Assert laP P _ ;; (Assert laP' P' js ;; _) as s =>
    match check_entailment P P' js with
      Ok _ =>
      check_proof_outline total s
    | Error e => Error e
    end
  | Assert laP P _ ;; Assign lass x t ;; (Assert laQ Q _ ;; _) as s =>
    if term_equivb P (subst x t Q) then
      check_proof_outline total s
    else
      Error (laP, "Assignment precondition does not match postcondition with RHS substituted for LHS")
  | Assert laP P _ ;; If li C ((Assert laPthen Pthen _ ;; _) as thenBody) ((Assert laPelse Pelse _ ;; _) as elseBody) ;; (Assert laQ Q _ ;; _) as s =>
    if negb (term_equivb' Pthen (BinOp li And P C)) then
      Error (laPthen, "The precondition of the 'then' block of an 'if' statement must match the conjunction of the 'if' statement's precondition and the condition")
    else if negb (ends_with_assert thenBody Q) then
      Error (li, "The 'then' block of an 'if' statement must end with an assertion that asserts the 'if' statement's postcondition")
    else
      match check_proof_outline total thenBody with
        Error e => Error e
      | Ok _ =>
        if negb (term_equivb' Pelse (BinOp li And P (Not li C))) then
          Error (laPelse, "The precondition of the 'else' block of an 'if' statement must match the conjunction of the 'if' statement's precondition and the negation of the condition")
        else if negb (ends_with_assert elseBody Q) then
          Error (li, "The 'else' block of an 'if' statement must end with an assertion that asserts the 'if' statement's postcondition")
        else
          check_proof_outline total elseBody
      end
  | Assert laInv Inv _ ;; While lw C body ;; ((Assert laQ Q _ ;; _) as s) =>
    if total then
      match body with
        Assign las ((_, TInt) as x) V ;; ((Assert laP P _ ;; body1) as body0) =>
        if existsb (var_eqb x) (free_vars Inv) then
          Error (laInv, "Variable '" ++ fst x ++ "' must not appear in the loop invariant")
        else if existsb (var_eqb x) (free_vars C) then
          Error (lw, "Variable '" ++ fst x ++ "' must not appear in the loop condition")
        else if existsb (var_eqb x) (assigned_vars body1) then
          Error (loc_of_stmt body1, "Variable '" ++ fst x ++ "' must not be assigned to in the loop body")
        else if negb (term_equivb' P (BinOp lw And Inv (BinOp lw And C (BinOp lw (Eq TInt) V (Var lw x))))) then
          Error (laP, "Loop body precondition does not match conjunction of invariant, condition, and equality of variant and variable")
        else if negb (ends_with_assert body1 (BinOp lw And Inv (BinOp lw And (BinOp lw Le (Val lw 0) V) (BinOp lw Le (BinOp lw Add V (Val lw 1)) (Var lw x))))) then
          Error (loc_of_stmt body1, "Loop body does not end with an assert statement that asserts the conjunction of the loop invariant and that the variant is nonnegative and less than the variable")
        else
          match check_proof_outline total body0 with
            Error e => Error e
          | Ok _ =>
            if negb (term_equivb' Q (BinOp lw And Inv (Not lw C))) then
              Error (laQ, "Loop postcondition does not match conjunction of invariant and negation of condition")
            else
              Ok tt
          end
      | _ => Error (lw, "Body of loop must start with assignment followed by assertion")
      end
    else
      match body with
        Assert laP P _ ;; _ =>
        if term_equivb' P (BinOp laInv And Inv C) then
          if ends_with_assert body Inv then
            match check_proof_outline total body with
              Ok _ =>
              if term_equivb' Q (BinOp laInv And Inv (Not laInv C)) then
                check_proof_outline total s
              else
                Error (laQ, "Loop postcondition does not match conjunction of invariant and negation of condition")
            | Error e => Error e
            end
          else
            Error (lw, "Body of loop does not end with an assert statement that asserts the loop invariant")
        else
          Error (laP, "Loop body precondition does not match conjunction of invariant and condition")
      | _ =>
        Error (loc_of_stmt body, "Body of loop must start with assert")
      end
  | Assert laP P _ ;; Pass lp => Ok tt
  | _ => Error (loc_of_stmt s, "Malformed proof outline")
  end.
