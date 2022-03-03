type _bool = bool
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
      val _Add: binop = Add
      val _Sub: binop = Sub
      val _Eq: binop = Eq0
      val _Le: binop = Le
      val _And: binop = And
      val _EnvNil: env = Nil
      val _JustifNil: justif list = Nil
      method _EnvCons (h: Js.js_string Js.t) (t: env): env = Cons (coq_string_of_string (Js.to_string h), t)
      method _JustifCons (j: justif) (js: justif list): justif list = Cons (j, js)
      method _Val (l: loc) (n: int): term = Val (l, z_of_int n)
      method _Var (l: loc) (s: Js.js_string Js.t): term = Var (l, coq_string_of_string (Js.to_string s))
      method _BinOp (l: loc) (op: binop) (t1: term) (t2: term): term = BinOp (l, op, t1, t2)
      method _Not (l: loc) (t: term): term = Not (l, t)
      method _JZ (l: loc): justif = JZ l
      method _JZ_at_ (l: loc) (lk: loc) (k: int): justif = JZ_at (l, lk, nat_of_int k)
      method _JRewrite (l: loc) (lk1: loc) (k1: int) (lk2: loc) (k2: int): justif = JRewrite (l, lk1, nat_of_int k1, lk2, nat_of_int k2)
      val _LawAppIndicesNil: (loc, int) prod list = Nil
      method _LawAppIndicesCons (l: loc) (k: int) (ks: (loc, nat) prod list): (loc, nat) prod list = Cons (Pair (l, nat_of_int k), ks)
      method _Law (p: term) (c: term): law = Law (conjuncts_of p, c)
      method _JLaw (l: loc) (_law: law) (ks: (loc, nat) prod list): justif = JLaw (l, _law, ks)
      method _Assert (l: loc) (t: term) (j: justif list): stmt = Assert (l, t, j)
      method _Assign (l: loc) (x: Js.js_string Js.t) (t: term): stmt = Assign (l, coq_string_of_string (Js.to_string x), t)
      method _If (l: loc) (t: term) (s1: stmt) (s2: stmt): stmt = If (l, t, s1, s2)
      method _While (l: loc) (t: term) (s: stmt): stmt = While (l, t, s)
      method _Seq (s1: stmt) (s2: stmt): stmt = Seq (s1, s2)
      method _Pass (l: loc): stmt = Pass l
      method stmt_is_well_typed_ (e: env) (s: stmt): _bool Js.t = Js.bool (Proof_checker.post_env_of_stmt e s <> None)
      method check_proof_outline_ (s: stmt): (unit0, (loc, string) prod) result = Proof_checker.check_proof_outline s
      method isOk (r: (unit0, (loc, string) prod) result): _bool Js.t = Js.bool (match r with Ok _ -> true | _ -> false)
      method getLoc (r: (unit0, (loc, string) prod) result): loc = let Error (Pair (l, msg)) = r in l
      method getMsg (r: (unit0, (loc, string) prod) result): Js.js_string Js.t = let Error (Pair (l, msg)) = r in Js.string (string_of_coq_string msg)
    end end
