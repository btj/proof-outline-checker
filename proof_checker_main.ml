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
      method _Eq(tp: type0): binop = Eq0 tp
      val _Le: binop = Le
      val _And: binop = And
      val _EnvNil: env = Nil
      val _JustifNil: justif list = Nil
      val _TermsNil: term list = Nil
      method _TermsCons (t: term) (ts: term list): term list = Cons (t, ts)
      val _TInt: type0 = TInt
      val _TBool: type0 = TBool
      method mkVar(name: Js.js_string Js.t)(tp: type0): var = Pair (coq_string_of_string (Js.to_string name), tp)
      method mkConst(name: Js.js_string Js.t)(tp: type0): var = Pair (coq_string_of_string (Js.to_string name), tp)
      method _TFun (argType: type0) (resultType: type0): type0 = TFun (argType, resultType)
      method _TSort (name: Js.js_string Js.t): type0 = TSort (coq_string_of_string (Js.to_string name))
      method _EnvCons (x: var) (t: env): env = Cons (x, t)
      method _JustifCons (j: justif) (js: justif list): justif list = Cons (j, js)
      method _Val (l: loc) (n: int): term = Val (l, z_of_int n)
      method _Var (l: loc) (x: var): term = Var (l, x)
      method _BinOp (l: loc) (op: binop) (t1: term) (t2: term): term = BinOp (l, op, t1, t2)
      method _Not (l: loc) (t: term): term = Not (l, t)
      method _Const (l: loc) (c: (string, type0) prod): term = Const (l, c)
      method _App (l: loc) (tf: term) (ta: term): term = App (l, tf, ta)
      method _JZ (l: loc): justif = JZ l
      method _JZ_at_ (l: loc) (lk: loc) (k: int): justif = JZ_at (l, lk, nat_of_int k)
      method _JRewrite (l: loc) (lk1: loc) (k1: int) (lk2: loc) (k2: int): justif = JRewrite (l, lk1, nat_of_int k1, lk2, nat_of_int k2)
      val _LawAppIndicesNil: (loc, int) prod list = Nil
      method _LawAppIndicesCons (l: loc) (k: int) (ks: (loc, nat) prod list): (loc, nat) prod list = Cons (Pair (l, nat_of_int k), ks)
      method _Law (ps: term list) (c: term): law = Law (ps, c)
      method _JLaw (l: loc) (_law: law) (ks: (loc, nat) prod list): justif = JLaw (l, _law, ks)
      method _JRewriteWithLaw (l: loc) (_law: law) (ks: (loc, nat) prod list) (lk: loc) (k: int): justif = JRewriteWithLaw (l, _law, ks, lk, nat_of_int k)
      method _Assert (l: loc) (t: term) (j: justif list): stmt = Assert (l, t, j)
      method _Assign (l: loc) (x: var) (t: term): stmt = Assign (l, x, t)
      method _If (l: loc) (t: term) (s1: stmt) (s2: stmt): stmt = If (l, t, s1, s2)
      method _While (l: loc) (t: term) (s: stmt): stmt = While (l, t, s)
      method _Seq (s1: stmt) (s2: stmt): stmt = Seq (s1, s2)
      method _Pass (l: loc): stmt = Pass l
      method stmt_is_well_typed_ (e: env) (s: stmt): _bool Js.t = Js.bool (Proof_checker.post_env_of_stmt e s <> None)
      method check_proof_outline_ (total: _bool Js.t) (s: stmt): (unit0, (loc, string) prod) result = Proof_checker.check_proof_outline (if Js.to_bool total then True else False) s
      method isOk (r: (unit0, (loc, string) prod) result): _bool Js.t = Js.bool (match r with Ok _ -> true | _ -> false)
      method getLoc (r: (unit0, (loc, string) prod) result): loc = let Error (Pair (l, msg)) = r in l
      method getMsg (r: (unit0, (loc, string) prod) result): Js.js_string Js.t = let Error (Pair (l, msg)) = r in Js.string (string_of_coq_string msg)
    end end
