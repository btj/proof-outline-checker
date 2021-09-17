Require Export List.
Require Export proof_outlines.

Definition env := list var.

Inductive type := TInt | TBool.

Definition type_eq_dec(t1 t2: type): {t1 = t2} + {t1 <> t2}.
decide equality.
Defined.

Definition type_eqb(t1 t2: type): bool :=
  if type_eq_dec t1 t2 then true else false.

Section Environment.

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

End Environment.

Fixpoint post_env_of_stmt(E: env)(s: stmt): option env :=
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
      match post_env_of_stmt E s1 with
        Some E1 =>
        match post_env_of_stmt E s2 with
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
      match post_env_of_stmt E s with
        Some _ => Some E
      | _ => None
      end
    | _ => None
    end
  | s1 ;; s2 =>
    match post_env_of_stmt E s1 with
      Some E => post_env_of_stmt E s2
    | None => None
    end
  end.
