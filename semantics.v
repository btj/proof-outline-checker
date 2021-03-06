Require Export proof_outlines.

Definition state := var -> option Z.

Inductive value :=
| VInt(z: Z)
| VBool(b: bool)
.

Definition eval_binop op v1 v2 :=
  match op, v1, v2 with
    Add, VInt z1, VInt z2 => Some (VInt (z1 + z2))
  | Sub, VInt z1, VInt z2 => Some (VInt (z1 - z2))
  | And, VBool b1, VBool b2 => Some (VBool (b1 && b2))
  | Le, VInt z1, VInt z2 => Some (VBool (Z.leb z1 z2))
  | _, _, _ => None
  end.

Inductive evaluates_to(S: state): term -> value -> Prop :=
| Val_evaluates_to l z:
  evaluates_to S (Val l z) (VInt z)
| Var_evaluates_to l x z:
  S x = Some z ->
  evaluates_to S (Var l x) (VInt z)
| BinOp_evaluates_to l op t1 t2 v1 v2 v:
  evaluates_to S t1 v1 ->
  evaluates_to S t2 v2 ->
  eval_binop op v1 v2 = Some v ->
  evaluates_to S (BinOp l op t1 t2) v
| Eq_evaluates_to_true l t1 t2 v:
  evaluates_to S t1 v ->
  evaluates_to S t2 v ->
  evaluates_to S (BinOp l Eq t1 t2) (VBool true)
| Eq_evaluates_to_false l t1 t2 v1 v2:
  evaluates_to S t1 v1 ->
  evaluates_to S t2 v2 ->
  v1 <> v2 ->
  evaluates_to S (BinOp l Eq t1 t2) (VBool false)
| Not_evaluates_to l t b:
  evaluates_to S t (VBool b) ->
  evaluates_to S (Not l t) (VBool (negb b))
.

Definition update(x: var)(z: Z)(S: state): state :=
  fun y => if string_dec x y then Some z else S y.

Inductive terminates_in: state -> stmt -> state -> Prop :=
| Assert_terminates_in S l P j:
  evaluates_to S P (VBool true) ->
  terminates_in S (Assert l P j) S
| Assign_terminates_in S l x t z:
  evaluates_to S t (VInt z) ->
  terminates_in S (Assign l x t) (update x z S)
| Pass_terminates_in S l:
  terminates_in S (Pass l) S
| Seq_terminates_in S s1 S' s2 S'':
  terminates_in S s1 S' ->
  terminates_in S' s2 S'' ->
  terminates_in S (s1 ;; s2) S''
| If_terminates_in S C l b s1 s2 S':
  evaluates_to S C (VBool b) ->
  terminates_in S (if b then s1 else s2) S' ->
  terminates_in S (If l C s1 s2) S'
| While_terminates_in S l C s S':
  terminates_in S (If l C (s ;; While l C s) (Pass l)) S' ->
  terminates_in S (While l C s) S'
.

CoInductive diverges: state -> stmt -> Prop :=
| Seq_diverges1 S s1 s2:
  diverges S s1 ->
  diverges S (s1 ;; s2)
| Seq_diverges2 S s1 S' s2:
  terminates_in S s1 S' ->
  diverges S' s2 ->
  diverges S (s1 ;; s2)
| If_diverges S l C s1 s2 b:
  evaluates_to S C (VBool b) ->
  diverges S (if b then s1 else s2) ->
  diverges S (If l C s1 s2)
| While_diverges S l C s:
  diverges S (If l C (s ;; While l C s) (Pass l)) ->
  diverges S (While l C s)
.