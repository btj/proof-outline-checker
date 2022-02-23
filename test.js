const proof_checker = require('./proof_checker.js');

with (proof_checker) {
  function seq(ss) {
    return ss.reduceRight((acc, s) => Seq(s, acc));
  }

  function True(l) { return BinOp(l, Eq, Val(l, 0), Val(l, 0)); }

  const env0 = Cons("n", Nil)
  const outline1 = seq([
    Assert(0, True(1), None),
    Assert(2, BinOp(3, Eq, Val(4, 0), BinOp(5, Sub, Var(6, "n"), Var(7, "n"))), Some(JZ(8))),
    Assign(9, "i", Var(10, "n")),
    Assert(11, BinOp(12, Eq, Val(13, 0), BinOp(14, Sub, Var(15, "n"), Var(16, "i"))), None),
    Assign(17, "r", Val(18, 0)),
    Assert(19, BinOp(20, Eq, Var(21, "r"), BinOp(22, Sub, Var(23, "n"), Var(24, "i"))), None),
    While(25, Not(26, BinOp(27, Eq, Var(28, "i"), Val(29, 0))), seq([
      Assert(30, BinOp(31, And, BinOp(32, Eq, Var(33, "r"), BinOp(34, Sub, Var(35, "n"), Var(36, "i"))), Not(37, BinOp(38, Eq, Var(39, "i"), Val(40, 0)))), None),
      Assert(41, BinOp(42, Eq, BinOp(43, Add, Var(44, "r"), Val(45, 1)), BinOp(46, Sub, Var(47, "n"), BinOp(48, Sub, Var(49, "i"), Val(50, 1)))), Some(JZ_at(51, 52, 0))),
      Assign(53, "i", BinOp(54, Sub, Var(55, "i"), Val(56, 1))),
      Assert(57, BinOp(58, Eq, BinOp(59, Add, Var(60, "r"), Val(61, 1)), BinOp(62, Sub, Var(63, "n"), Var(64, "i"))), None),
      Assign(65, "r", BinOp(66, Add, Var(67, "r"), Val(68, 1))),
      Assert(69, BinOp(70, Eq, Var(71, "r"), BinOp(72, Sub, Var(73, "n"), Var(74, "i"))), None),
      Pass(75)
    ])),
    Assert(76, BinOp(77, And, BinOp(78, Eq, Var(79, "r"), BinOp(80, Sub, Var(81, "n"), Var(82, "i"))), Not(83, Not(84, BinOp(85, Eq, Var(86, "i"), Val(87, 0))))), None),
    Assert(88, BinOp(89, And, BinOp(90, Eq, Var(91, "r"), BinOp(92, Sub, Var(93, "n"), Var(94, "i"))), BinOp(95, Eq, Var(96, "i"), Val(97, 0))), Some(JZ_at(98, 99, 1))),
    Assert(100, BinOp(101, Eq, Var(102, "r"), BinOp(103, Sub, Var(104, "n"), Val(105, 0))), Some(JRewrite(106, 107, 1, 108, 0))),
    Assert(109, BinOp(110, Eq, Var(111, "r"), Var(112, "n")), Some(JZ_at(113, 114, 0))),
    Pass(115)
  ]);
  console.log("outline1 is well-typed: ", stmt_is_well_typed(env0, outline1));
  const result1 = check_proof_outline(outline1);
  console.log("isOk(check_proof_outline(outline1)) == ", isOk(result1));

  const outline2 = seq([
    Assert(0, True(1), None),
    Assert(2, BinOp(3, Eq, Val(4, 0), BinOp(5, Sub, Var(6, "n"), Var(7, "n"))), Some(JZ(8))),
    Assign(9, "i", Var(10, "n")),
    Assert(11, BinOp(12, Eq, Val(13, 0), BinOp(14, Sub, Var(15, "n"), Var(16, "i"))), None),
    Assign(17, "r", Val(18, 0)),
    Assert(19, BinOp(20, Eq, Var(21, "r"), BinOp(22, Sub, Var(23, "n"), Var(24, "i"))), None),
    While(25, Not(26, BinOp(27, Eq, Var(28, "i"), Val(29, 0))), seq([
      Assert(30, BinOp(31, And, BinOp(32, Eq, Var(33, "r"), BinOp(34, Sub, Var(35, "n"), Var(36, "i"))), Not(37, BinOp(38, Eq, Var(39, "i"), Val(40, 0)))), None),
      Assert(41, BinOp(42, Eq, BinOp(43, Add, Var(44, "r"), Val(45, 1)), BinOp(46, Sub, Var(47, "n"), BinOp(48, Sub, Var(49, "i"), Val(50, 1)))), Some(JZ_at(51, 52, 0))),
      Assign(53, "i", BinOp(54, Sub, Var(55, "i"), Val(56, 1))),
      Assert(57, BinOp(58, Eq, BinOp(59, Add, Var(60, "r"), Val(61, 1)), BinOp(62, Sub, Var(63, "n"), Var(64, "i"))), None),
      Assign(65, "n", BinOp(66, Add, Var(67, "r"), Val(68, 1))), // <-- wrong
      Assert(69, BinOp(70, Eq, Var(71, "r"), BinOp(72, Sub, Var(73, "n"), Var(74, "i"))), None),
      Pass(75)
    ])),
    Assert(76, BinOp(77, And, BinOp(78, Eq, Var(79, "r"), BinOp(80, Sub, Var(81, "n"), Var(82, "i"))), Not(83, Not(84, BinOp(85, Eq, Var(86, "i"), Val(87, 0))))), None),
    Assert(88, BinOp(89, And, BinOp(90, Eq, Var(91, "r"), BinOp(92, Sub, Var(93, "n"), Var(94, "i"))), BinOp(95, Eq, Var(96, "i"), Val(97, 0))), Some(JZ_at(98, 99, 1))),
    Assert(100, BinOp(101, Eq, Var(102, "r"), BinOp(103, Sub, Var(104, "n"), Val(105, 0))), Some(JRewrite(106, 107, 1, 108, 0))),
    Assert(109, BinOp(110, Eq, Var(111, "r"), Var(112, "n")), Some(JZ_at(113, 114, 0))),
    Pass(115)
  ]);
  console.log("outline2 is well-typed: ", stmt_is_well_typed(env0, outline2));
  const result2 = check_proof_outline(outline2);
  console.log("isOk(check_proof_outline(outline2)) == ", isOk(result2));
  console.log("getLoc(check_proof_outline(outline2)) == ", getLoc(result2));
  console.log("getMsg(check_proof_outline(outline2)) == ", getMsg(result2));
}
