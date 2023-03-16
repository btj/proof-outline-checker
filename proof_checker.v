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

Fixpoint eval_closed_term(t: term): option Z :=
  match t with
    Val _ z => Some z
  | BinOp _ ((Add|Sub|Mul) as op) t1 t2 =>
    match eval_closed_term t1, eval_closed_term t2 with
      Some z1, Some z2 =>
      Some
        match op with
          Add => (z1 + z2)%Z
        | Sub => (z1 - z2)%Z
        | Mul => (z1 * z2)%Z
        | _ => 0%Z (* Dummy *)
        end
    | _, _ => None
    end
  | _ => None
  end.

Fixpoint subst'(f: var -> option term)(t: term): option term :=
  match t with
  | Val _ _ => Some t
  | Var l x => f x
  | BinOp l op t1 t2 =>
    match subst' f t1, subst' f t2 with
      Some t'1, Some t'2 =>
      Some (BinOp l op t'1 t'2)
    | _, _ => None
    end
  | Not l t =>
    match subst' f t with
      Some t' => Some (Not l t')
    | None => None
    end
  | Const _ _ => Some t
  | App l tf targ =>
    match subst' f tf, subst' f targ with
      Some t'f, Some t'arg =>
      Some (App l t'f t'arg)
    | _, _ => None
    end
  end.

Fixpoint match_term f c C :=
  match c, C with
    Var _ x, t =>
    match f x with
      None => Some (update f x t)
    | Some t' =>
      if term_equivb t t' then Some f else None
    end
  | Val _ v, t =>
    match eval_closed_term t with
      Some v' => if Z.eqb v v' then Some f else None
    | None => None
    end
  | t, Val _ v' =>
    match subst' f t with
      Some t =>
      match eval_closed_term t with
        Some v => if Z.eqb v v' then Some f else None
      | _ => None
      end
    | _ => None
    end
  | BinOp _ op t1 t2, BinOp _ op' t1' t2' =>
    if binop_eq_dec op op' then
      match
        match match_term f t1 t1' with
          None => None
        | Some f =>
          match_term f t2 t2'
        end
      with
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
      | Some f => Some f
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

Definition string_of_Z(k: Z): string :=
  match k with
    0%Z => "0"
  | 1%Z => "1"
  | 2%Z => "2"
  | 3%Z => "3"
  | 4%Z => "4"
  | 5%Z => "5"
  | 6%Z => "6"
  | 7%Z => "7"
  | 8%Z => "8"
  | 9%Z => "9"
  | _ => "?"
  end.

Fixpoint match_law_premises{A}(l: loc)(f: var -> option term)(Hs: list term)(ps: list term)(ks: list (loc * nat))(cont: (var -> option term) -> result A (loc * string)): result A (loc * string) :=
  match ps, ks with
    [], [] => cont f
  | p::ps, (lk, k)::ks =>
    match nth_error Hs k with
    | None => Error (lk, "Conjunctnummer ongeldig; het antecedent telt slechts " ++ string_of_Z (Z.of_nat (List.length Hs)) ++ " conjuncten")
    | Some H =>
      match match_term f p H with
      | None => Error (lk, "De vorm van deze conjunct komt niet overeen met de vorm van de overeenkomstige premisse van de wet")
      | Some f =>
        match_law_premises l f Hs ps ks cont
      end
    end
  | _, _ => Error (l, "Het aantal conjunctnummers is niet gelijk aan het aantal premissen van de wet")
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
  | BinOp _ (Add|Sub|Mul) _ _ => TInt
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
      None => Error (lk, "Conjunctnummer ongeldig; het antecedent telt slechts " ++ string_of_Z (Z.of_nat (List.length Hs)) ++ " conjuncten")
    | Some H => Ok (is_Z_entailment H)
    end
  | JRewrite l lk1 k1 lk2 k2 =>
    match nth_error Hs k1 with
    | Some H =>
      match H with
      | BinOp leq (Eq _) LHS RHS =>
        match nth_error Hs k2 with
          None => Error (lk2, "Conjunctnummer ongeldig; het antecedent telt slechts " ++ string_of_Z (Z.of_nat (List.length Hs)) ++ " conjuncten")
        | Some H2 =>
          Ok (fun C => if existsb (term_equivb C) (rewrites LHS RHS H2) then true else false)
        end
      | _ => Error (loc_of_term H, "Gelijkheid verwacht")
      end
    | _ => Error (lk1, "Conjunctnummer ongeldig; het antecedent telt slechts " ++ string_of_Z (Z.of_nat (List.length Hs)) ++ " conjuncten")
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
        | None => Error (lk, "Conjunctnummer ongeldig; het antecedent telt slechts " ++ string_of_Z (Z.of_nat (List.length Hs)) ++ " conjuncten")
        end
      )
    | _ => Error (l, "De conclusie van deze wet is geen gelijkheid")
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

Fixpoint normalize_conjunct t :=
  match t with
    Not _ (Not _ t) => normalize_conjunct t
  | _ => t
  end.

Definition check_conjunct_entailment(Hs: list term)(checkers: list (term -> bool))(C: term): result unit (loc * string) :=
  if
    (existsb (term_equivb (normalize_conjunct C)) (map normalize_conjunct Hs) ||
     existsb (fun checker => checker C) checkers ||
     match C with
       BinOp _ (Eq _) t1 t2 =>
       term_equivb t1 t2
     | _ => false
     end)%bool
  then
    Ok tt
  else
    Error (loc_of_term C, "Conjunct niet verantwoord").

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

Inductive error_type :=
  ShapeError
| JustificationError.

Fixpoint check_proof_outline(total: bool)(s: stmt): list (error_type * (loc * string)) :=
  match s with
    Assert laP P _ ;; (Assert laP' P' js ;; _) as s =>
    match check_entailment P P' js with
      Ok _ => []
    | Error e => [(JustificationError, e)]
    end
    ++ check_proof_outline total s
  | Assert laP P _ ;; Assign lass x t ;; (Assert laQ Q _ ;; _) as s =>
    (
      if term_equivb P (subst x t Q) then
        []
      else
        [(ShapeError, (lass, "Kan de correctheid van deze toekenning niet bewijzen; kan het toekenningsaxioma niet toepassen want de pre- en postconditie van de toekenning hebben niet de juiste vorm"))]
    )
    ++ check_proof_outline total s
  | Assert laP P _ ;; If li C ((Assert laPthen Pthen _ ;; _) as thenBody) ((Assert laPelse Pelse _ ;; _) as elseBody) ;; (Assert laQ Q _ ;; _) as s =>
    (
      if term_equivb' Pthen (BinOp li And P C) then
        []
      else
        [(ShapeError, (li, "Kan de correctheid van deze 'if'-opdracht niet bewijzen; kan de regel voor 'if'-opdrachten niet toepassen want de preconditie van de 'then'-tak heeft niet de juiste vorm$     assert P\n     if C:\n→     assert P and C\n         ...\n         assert Q\n     else:\n         assert P and not C\n         ...\n         assert Q\n     assert Q"))]
    )
    ++
    (
      if ends_with_assert thenBody Q then
        []
      else
        [(ShapeError, (li, "Kan de correctheid van deze 'if'-opdracht niet bewijzen; kan de regel voor 'if'-opdrachten niet toepassen want de postconditie van de 'then'-tak heeft niet de juiste vorm"))]
    )
    ++
    (
      if term_equivb' Pelse (BinOp li And P (Not li C)) then
        []
      else
        [(ShapeError, (li, "Kan de correctheid van deze 'if'-opdracht niet bewijzen; kan de regel voor 'if'-opdrachten niet toepassen want de preconditie van de 'else'-tak heeft niet de juiste vorm"))]
    )
    ++
    (
      if ends_with_assert elseBody Q then
        []
      else
        [(ShapeError, (li, "Kan de correctheid van deze 'if'-opdracht niet bewijzen; kan de regel voor 'if'-opdrachten niet toepassen want de postconditie van de 'else'-tak heeft niet de juiste vorm"))]
    )
    ++
    check_proof_outline total thenBody
    ++
    check_proof_outline total elseBody
    ++
    check_proof_outline total s
  | Assert laInv Inv _ ;; While lw C body ;; ((Assert laQ Q _ ;; _) as s) =>
    (
    if total then
      match body with
        Assign las ((_, TInt) as x) V ;; ((Assert laP P _ ;; body1) as body0) =>
        (
          if existsb (var_eqb x) (free_vars Inv) then
            [(ShapeError, (laInv, "Variable '" ++ fst x ++ "' mag niet voorkomen in de lusinvariant"))]
          else
            []
        )
        ++
        (
          if existsb (var_eqb x) (free_vars C) then
            [(ShapeError, (lw, "Variable '" ++ fst x ++ "' mag niet voorkomen in de lusvoorwaarde"))]
          else
            []
        )
        ++
        (
          if existsb (var_eqb x) (assigned_vars body1) then
            [(ShapeError, (loc_of_stmt body1, "Aan variable '" ++ fst x ++ "' mag niet toegekend worden in het luslichaam"))]
          else
            []
        )
        ++
        (
          if term_equivb' P (BinOp lw And Inv (BinOp lw And C (BinOp lw (Eq TInt) V (Var lw x)))) then
            []
          else
            [(ShapeError, (lw, "Kan de correctheid van deze lus niet bewijzen; kan de regel voor lussen niet toepassen want de preconditie van het luslichaam heeft niet de juiste vorm"))]
        )
        ++
        (
          if ends_with_assert body1 (BinOp lw And Inv (BinOp lw And (BinOp lw Le (Val lw 0) V) (BinOp lw Le (BinOp lw Add V (Val lw 1)) (Var lw x)))) then
            []
          else
            [(ShapeError, (lw, "Kan de correctheid van deze lus niet bewijzen; kan de regel voor lussen niet toepassen want de postconditie van het luslichaam heeft niet de juiste vorm"))]
        )
        ++
        (
          if term_equivb' Q (BinOp lw And Inv (Not lw C)) then
            []
          else
            [(ShapeError, (lw, "Kan de correctheid van deze lus niet bewijzen; kan de regel voor lussen niet toepassen want de postconditie van de lus heeft niet de juiste vorm"))]
        )
        ++
        check_proof_outline total body0
      | _ =>
        [(ShapeError, (lw, "Om totale correctheid te bewijzen van deze lus, moet het luslichaam beginnen met een toekenning gevolgd door een 'assert'-opdracht"))]
      end
    else
      match body with
        Assert laP P _ ;; _ =>
        (
          if term_equivb' P (BinOp laInv And Inv C) then
            []
          else
            [(ShapeError, (lw, "Kan de correctheid van deze lus niet bewijzen; kan de regel voor lussen niet toepassen want de preconditie van het luslichaam heeft niet de juiste vorm"))]
        )
        ++
        (
          if ends_with_assert body Inv then
            []
          else
            [(ShapeError, (lw, "Kan de correctheid van deze lus niet bewijzen; kan de regel voor lussen niet toepassen want de postconditie van het luslichaam heeft niet de juiste vorm"))]
        )
        ++
        (
          if term_equivb' Q (BinOp laInv And Inv (Not laInv C)) then
            []
          else
            [(ShapeError, (lw, "Kan de correctheid van deze lus niet bewijzen; kan de regel voor lussen niet toepassen want de postconditie van de lus heeft niet de juiste vorm"))]
        )
        ++
        check_proof_outline total body
      | _ =>
        [(ShapeError, (loc_of_stmt body, "Luslichaam moet beginnen met een 'assert'-opdracht"))]
      end
    )
    ++
    check_proof_outline total s
  | Assert laP P _ ;; Pass lp ;; ((Assert laQ Q _ ;; _) as s) =>
    (
      if term_equivb P Q then
        []
      else
        [(ShapeError, (laP, "De preconditie van een 'pass-opdracht moet gelijk zijn aan haar postconditie"))]
    )
    ++
    check_proof_outline total s
  | Assert laP P _ ;; Pass lp => []
  | _ =>
    [(ShapeError, (loc_of_stmt s, "Bewijssilhouet heeft een foute vorm"))]
  end.
