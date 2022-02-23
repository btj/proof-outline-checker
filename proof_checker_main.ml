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

let char_of_ascii (Ascii (b0, b1, b2, b3, b4, b5, b6, b7)) =
  Char.chr (
    (match b0 with True -> 1 | _ -> 0) lor
    (match b1 with True -> 2 | _ -> 0) lor
    (match b2 with True -> 4 | _ -> 0) lor
    (match b3 with True -> 8 | _ -> 0) lor
    (match b4 with True -> 16 | _ -> 0) lor
    (match b5 with True -> 32 | _ -> 0) lor
    (match b6 with True -> 64 | _ -> 0) lor
    (match b7 with True -> 128 | _ -> 0)
  )

let coq_string_of_string s =
  let rec iter k =
    if k = String.length s then
      EmptyString
    else
      String (ascii_of_char s.[k], iter (k + 1))
  in
  iter 0

let string_of_coq_string s =
  let buf = Buffer.create 10 in
  let rec iter s =
    match s with
      EmptyString -> Buffer.contents buf
    | String (c, s) -> Buffer.add_char buf (char_of_ascii c); iter s
  in
  iter s

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
      val _Nil = Nil
      val _None = None
      method _Cons h t = Cons (coq_string_of_string (Js.to_string h), t)
      method _Some v = Some v
      method _Val l n = Val (l, z_of_int n)
      method _Var l s = Var (l, coq_string_of_string (Js.to_string s))
      method _BinOp l op t1 t2 = BinOp (l, op, t1, t2)
      method _Not l t = Not (l, t)
      method _JZ l = JZ l
      method _JZ_at_ l lk k = JZ_at (l, lk, nat_of_int k)
      method _JRewrite l lk1 k1 lk2 k2 = JRewrite (l, lk1, nat_of_int k1, lk2, nat_of_int k2)
      method _Assert l t j = Assert (l, t, j)
      method _Assign l x t = Assign (l, coq_string_of_string (Js.to_string x), t)
      method _If l t s1 s2 = If (l, t, s1, s2)
      method _While l t s = While (l, t, s)
      method _Seq s1 s2 = Seq (s1, s2)
      method _Pass l = Pass l
      method stmt_is_well_typed_ e s = Js.bool (Proof_checker.post_env_of_stmt e s <> None)
      method check_proof_outline_ s = Proof_checker.check_proof_outline s
      method isOk r = Js.bool (match r with Ok _ -> true | _ -> false)
      method getLoc r = let Error (l, msg) = r in l
      method getMsg r = let Error (l, msg) = r in Js.string (string_of_coq_string msg)
    end end
