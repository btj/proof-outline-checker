open Proof_checker
open Js_of_ocaml

let bool_of_bool b = if b then True else False

let ascii_of_char c =
  let c = int_of_char c in
  Ascii
    (bool_of_bool ((c land 0x01) <> 0),
     bool_of_bool ((c land 0x02) <> 0),
     bool_of_bool ((c land 0x04) <> 0),
     bool_of_bool ((c land 0x08) <> 0),
     bool_of_bool ((c land 0x10) <> 0),
     bool_of_bool ((c land 0x20) <> 0),
     bool_of_bool ((c land 0x40) <> 0),
     bool_of_bool ((c land 0x80) <> 0))

let coq_string_of_string s =
  let rec iter k =
    if k = String.length s then
      EmptyString
    else
      String (ascii_of_char s.[k], iter (k + 1))
  in
  iter 0

let rec positive_of_int n =
  if n = 1 then
    XH
  else if n land 1 <> 0 then
    XI (positive_of_int (n lsr 1))
  else
    XO (positive_of_int (n lsr 1))

let z_of_int n =
  if n = 0 then Z0 else if n > 0 then Zpos (positive_of_int n) else Zneg (positive_of_int (-n))

let rec nat_of_int n =
  if n = 0 then O else S (nat_of_int (n - 1))

let _ =
  Js.export_all
    begin object%js
      val _Add = Add
      val _Sub = Sub
      val _Eq = Eq
      val _And = And
      method _Val n = Val (z_of_int n)
      method _Var s = Var (coq_string_of_string (Js.to_string s))
      method _BinOp op t1 t2 = BinOp (op, t1, t2)
      method _Not t = Not t
      val _JZ = JZ
      method _JZ_at_ k = JZ_at (nat_of_int k)
      method _JRewrite k1 k2 = JRewrite (nat_of_int k1, nat_of_int k2)
      method _Assert t j = Assert (t, j)
      method _Assign x t = Assign (coq_string_of_string (Js.to_string x), t)
      method _If t s1 s2 = If (t, s1, s2)
      method _While t s = While (t, s)
      method _Seq s1 s2 = Seq (s1, s2)
      val _Pass = Pass
      method stmt_is_well_typed_ e s = Proof_checker.post_env_of_stmt e s <> None
      method is_valid_proof_outline_ s = Proof_checker.is_valid_proof_outline s
    end end
