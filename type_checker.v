Require Export List.
Require Export proof_outlines.

Definition env := list var.

Section Environment.

Context (E: env).

Fixpoint type_of(t: term): option type :=
  match t with
    Val l z => Some TInt
  | Var l x => if in_dec var_eq_dec x E then Some (snd x) else None
  | BinOp l (Add|Sub) t1 t2 =>
    match type_of t1, type_of t2 with
      Some TInt, Some TInt => Some TInt
    | _, _ => None
    end
  | BinOp l (Eq tp) t1 t2 =>
    match type_of t1, type_of t2 with
      Some tp1, Some tp2 =>
      if (type_eqb tp1 tp && type_eqb tp2 tp)%bool then
        Some TBool
      else
        None
    | _, _ => None
    end
  | BinOp l Le t1 t2 =>
    match type_of t1, type_of t2 with
      Some TInt, Some TInt => Some TBool
    | _, _ => None
    end
  | BinOp l And t1 t2 =>
    match type_of t1, type_of t2 with
      Some TBool, Some TBool => Some TBool
    | _, _ => None
    end
  | Not l t =>
    match type_of t with
      Some TBool => Some TBool
    | _ => None
    end
  | Const _ (cn, ctp) => Some ctp
  | App _ tf ta =>
    match type_of tf with
      Some (TFun tpa tpr) =>
      match type_of ta with
        Some tpa' =>
        if type_eq_dec tpa tpa' then Some tpr else None
      | None => None
      end
    | _ => None
    end
  end.

End Environment.

Fixpoint post_env_of_stmt(E: env)(s: stmt): option env :=
  match s with
    Assert l P j =>
    match type_of E P with
      Some TBool => Some E
    | _ => None
    end
  | Assign l x t =>
    match type_of E t with
      Some tp => if type_eq_dec tp (snd x) then Some (x::E) else None
    | _ => None
    end
  | Pass l => Some E
  | If l C s1 s2 =>
    match type_of E C with
      Some TBool =>
      match post_env_of_stmt E s1 with
        Some E1 =>
        match post_env_of_stmt E s2 with
          Some E2 =>
          Some (filter (fun x => existsb (var_eqb x) E2) E1)
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  | While l C s =>
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
