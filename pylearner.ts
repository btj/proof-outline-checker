// TODO: Have js_of_ocaml generate these declarations automatically https://github.com/ocsigen/js_of_ocaml/issues/1245
type Env_ = {__brand: "proof_checker.env"};
type Term_ = {__brand: "proof_checker.term"};
type BinOp_ = {__brand: "proof_checker.binop"};
type Justif_ = {__brand: "proof_checker.justif"};
type Law_ = {__brand: "proof_checker.law"};
type TermList_ = {__brand: "proof_checker.(term list)"};
type LawAppIndices_ = {__brand: "proof_checker.((loc, nat) prod list)"};
type JustifList_ = {__brand: "proof_checker.(justif list)"};
type Stmt_ = {__brand: "proof_checker.stmt"};
type Result_ = {__brand: "proof_checker.((unit, (loc, string) prod) result)"};
type Type_ = {__brand: "proof_checker.type"};
type Var_ = {__brand: "proof_checker.((string * type0) prod)"};
type Const_ = {__brand: "proof_checker.((string * type0) prod)"};
declare function mkVar(name: string, type: Type_): Var_;
declare function mkConst(name: string, type: Type_): Const_;
declare var EnvNil: Env_;
declare function EnvCons(x: Var_, tail: Env_): Env_;
declare function Val(loc: Loc, value: number): Term_;
declare function Var(loc: Loc, x: Var_): Term_;
declare var Add: BinOp_;
declare var Sub: BinOp_;
declare var Mul: BinOp_;
declare function Eq(type: Type_): BinOp_;
declare var Le: BinOp_;
declare var And: BinOp_;
declare var TInt: Type_;
declare var TBool: Type_;
declare function TSort(sort: string): Type_;
declare function TFun(argumentType: Type_, resultType: Type_): Type_;
declare function BinOp(loc: Loc, op: BinOp_, t1: Term_, t2: Term_): Term_;
declare function Not(loc: Loc, t: Term_): Term_;
declare function Const(loc: Loc, c: Const_): Term_;
declare function App(loc: Loc, f: Term_, arg: Term_): Term_;
declare function JZ(l: Loc): Justif_;
declare function JZ_at(l: Loc, lk: Loc, k: number): Justif_;
declare function JRewrite(l: Loc, lk1: Loc, k1: number, lk2: Loc, k2: number): Justif_;
declare var TermsNil: TermList_;
declare function TermsCons(t: Term_, ts: TermList_): TermList_;
declare function Law(p: TermList_, c: Term_): Law_;
declare var LawAppIndicesNil: LawAppIndices_;
declare function LawAppIndicesCons(lk: Loc, k: number, ks: LawAppIndices_): LawAppIndices_;
declare function JLaw(l: Loc, law: Law_, ks: LawAppIndices_): Justif_;
declare function JRewriteWithLaw(l: Loc, law: Law_, ks: LawAppIndices_, lk: Loc, k: number): Justif_;
declare var JustifNil: JustifList_;
declare function JustifCons(j: Justif_, js: JustifList_): JustifList_;
declare function Pass(l: Loc): Stmt_;
declare function Seq(s1: Stmt_, s2: Stmt_): Stmt_;
declare function Assert(l: Loc, t: Term_, js: JustifList_): Stmt_;
declare function Assign(l: Loc, x: Var_, t: Term_): Stmt_;
declare function If(l: Loc, condition: Term_, thenBody: Stmt_, elseBody: Stmt_): Stmt_;
declare function While(l: Loc, t: Term_, body: Stmt_): Stmt_;
declare function stmt_is_well_typed(env: Env_, stmt: Stmt_): boolean;
declare function check_proof_outline(total: boolean, outline: Stmt_): Result_;
declare function isOk(result: Result_): boolean;
declare function getLoc(result: Result_): Loc;
declare function getMsg(result: Result_): string;

function isDigit(c: string) { return '0' <= c && c <= '9'; }
function isAlpha(c: string) { return 'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z' || c == '_'; }

function has(object: object, propertyName: string) { return Object.prototype.hasOwnProperty.call(object, propertyName); }

const keywordsList = [
  'False', 'None', 'True', 'and', 'as', 'assert', 'async',
  'await', 'break', 'class', 'continue',
  'def', 'del', 'elif', 'else', 'except', 'finally', 'for', 'from',
  'global', 'if', 'import', 'in', 'is', 'lambda', 'nonlocal', 'not',
  'or', 'pass', 'raise', 'return', 'try', 'while', 'with', 'yield'
];

type StringSet = {[index: string]: true};
const keywords: StringSet = {};

for (let keyword of keywordsList)
  keywords[keyword] = true;

const operatorsList = [
  '+', '-', '*', '**', '/', '//', '%', '@',
  '<<', '>>', '&', '|', '^', '~', ':=',
  '<', '>', '<=', '>=', '==', '!=',
  '(', ')', '[', ']', '{', '}',
  ',', ':', '.', ';', '@', '=', '->',
  '+=', '-=', '*=', '/=', '//=', '%=', '@=',
  '&=', '|=', '^=', '>>=', '<<=', '**='
]

const operators: StringSet = {};
const operatorPrefixes: StringSet = {};

for (let operator of operatorsList) {
  operators[operator] = true;
  for (let i = 1; i < operator.length; i++)
    operatorPrefixes[operator.substring(0, i)] = true;
}

const leftBrackets = {'(': true, '[': true, '{': true};
const rightBrackets = {')': true, ']': true, '}': true};

type LocFactory = (start: number, end: number) => Loc;

class Comment_ {
  constructor(public locFactory: LocFactory, public start: number, public text: string, public isOnNewLine: boolean) {}

  loc() {
    return this.locFactory(this.start, this.start + this.text.length);
  }
}

class Scanner {

  pos = -1;
  startOfLine = 0;
  indentStack = [''];
  bracketsDepth: number;
  emittedEOL = true;
  onNewLine = true;
  c: any;
  comment: any;
  tokenStart: any;
  value: any;

  constructor(
      public locFactory: LocFactory,
      public text: string,
      public parseExpression?: boolean,
      public commentListener?: (comment: Comment_) => void) {
    this.bracketsDepth = parseExpression ? 1 : 0;
    this.eat();
  }

  currentIndent() {
    return this.indentStack[this.indentStack.length - 1];
  }

  eat() {
    this.pos++;
    this.c = (this.pos == this.text.length ? '<EINDE>' : this.text.charAt(this.pos));
  }

  nextToken() {
    this.comment = null;
    eatWhite:
    for (;;) {
      switch (this.c) {
        case '\n':
        case '\r':
          this.eat();
          this.startOfLine = this.pos;
          this.onNewLine = true;
          break;
        case ' ':
        case '\t':
          this.eat();
          break;
        case '#':
          this.eat();
          const commentStart = this.pos;
          while (this.c != '<EINDE>' && this.c != '\n' && this.c != '\r')
            this.eat();
          const comment = new Comment_(this.locFactory, commentStart, this.text.slice(commentStart, this.pos), this.onNewLine);
          if (this.commentListener)
            this.commentListener(comment);
          if (!this.onNewLine)
            this.comment = comment;
          break;
        default:
          break eatWhite;
      }
    }
    this.tokenStart = this.pos;
    if (this.c == '<EINDE>') {
      if (this.bracketsDepth > 0)
        return 'EINDE'; // Parser will detect error
      if (!this.emittedEOL) {
        this.emittedEOL = true;
        this.value = this.comment;
        return 'REGELEINDE';
      }
      if (this.currentIndent() != '') {
        this.indentStack.pop();
        return "DEDENT";
      }
      return 'EINDE';
    }
    if (this.onNewLine) {
      if (this.bracketsDepth == 0) {
        if (!this.emittedEOL) {
          this.emittedEOL = true;
          this.value = this.comment;
          return 'REGELEINDE';
        }
        let indent = this.text.substring(this.startOfLine, this.tokenStart);
        if (indent == this.currentIndent()) {
        } else if (indent.startsWith(this.currentIndent())) {
          this.indentStack.push(indent);
          return "INDENT";
        } else if (this.indentStack.includes(indent)) {
          this.indentStack.pop();
          return "DEDENT";
        } else
          throw new LocError(this.locFactory(this.tokenStart, this.tokenStart + 1), "Foute indentatie");
      }
    }
    this.onNewLine = false;
    this.emittedEOL = false;
    if (isDigit(this.c)) {
      this.eat();
      while (isDigit(this.c))
        this.eat();
      this.value = this.text.substring(this.tokenStart, this.pos);
      return 'GETAL';
    }
    if (isAlpha(this.c)) {
      let c0 = this.c;
      this.eat();
      while (isAlpha(this.c) || isDigit(this.c))
        this.eat();
      this.value = this.text.substring(this.tokenStart, this.pos);
      if (has(keywords, this.value))
        return this.value;
      return 'NAAM';
    }
    
    let newPos = this.pos + 1;
    let longestOperatorFound = null;
    for (;;) {
      let operatorCandidate = this.text.substring(this.tokenStart, newPos);
      if (has(operators, operatorCandidate))
        longestOperatorFound = operatorCandidate;
      if (has(operatorPrefixes, operatorCandidate) && newPos < this.text.length)
        newPos++;
      else
        break;
    }
    if (longestOperatorFound === null)
      throw new LocError(this.locFactory(this.tokenStart, this.tokenStart + 1), "Fout teken");
    this.pos += longestOperatorFound.length - 1;
    this.eat();
    if (has(leftBrackets, longestOperatorFound))
      this.bracketsDepth++;
    else if (has(rightBrackets, longestOperatorFound))
      this.bracketsDepth--;
    return longestOperatorFound;
  }
}

abstract class Binding {
  constructor(public value: any) {}
  abstract getNameHTML(): string;
}

class LocalBinding extends Binding {

  constructor(public declaration: any, value: any) {
    super(value);
  }
  
  setValue(value: any) {
    return this.value = value;
  }

  getNameHTML() {
    return this.declaration.type.resolve().toHTML() + " " + this.declaration.name;
  }
}

class OperandBinding extends Binding {

  constructor(public expression: Expression, public value: any) {
    super(value);
  }

  getNameHTML() {
    return "(operand)";
  }
}

class ImplicitVariableDeclaration {

  type: ImplicitTypeExpression;

  constructor(public name: string, type: Type) {
    this.type = new ImplicitTypeExpression(type);
  }
}

class Scope {

  bindings: {[index: string]: Binding} = {};

  constructor(public outerScope: Scope|null, public inferBindings?: boolean) {}
  
  tryLookup(x: string): any {
    if (has(this.bindings, x))
      return this.bindings[x];
    if (this.outerScope != null)
      return this.outerScope.tryLookup(x);
    return null;
  }
  
  lookup(loc: Loc, x: string, createIfMissing?: boolean) {
    let result = this.tryLookup(x);
    if (result == null)
      if (createIfMissing) {
        result = this.bindings[x] = new LocalBinding(x, null);
      } else if (this.inferBindings) {
        const type = new InferredType();
        const decl = new ImplicitVariableDeclaration(x, type);
        result = this.bindings[x] = new LocalBinding(decl, type);
      } else
        throw new ExecutionError(loc, "Er bestaat hier geen variabele genaamd '" + x + "'");
    return result;
  }
  
  *allBindings(): Iterable<any> {
    if (this.outerScope != null)
      yield* this.outerScope.allBindings();
    for (let x in this.bindings)
      yield this.bindings[x];
  }
}

class StackFrame {

  operands = [];

  constructor(public title: string, public env: Scope) {}

  *allBindings() {
    yield* this.env.allBindings();
    for (let operand of this.operands)
      yield operand;
  }
}

class ASTNode {

  constructor(public loc: Loc, public instrLoc: Loc|null) {}

  async breakpoint() {
    await checkBreakpoint(this);
  }
  
  executionError(msg: string): never {
    throw new ExecutionError(this.instrLoc || this.loc, msg);
  }
}

type Value = any;

abstract class Expression extends ASTNode {

  type: Type|undefined;

  constructor(loc: Loc, instrLoc: Loc) {
    super(loc, instrLoc);
  }

  check_(env: Scope) {
    this.type = this.check(env);
    return this.type;
  }
  check(env: Scope): Type {
    throw new Error("Method not implemented.");
  }

  checkAgainst(env: Scope, targetType: Type) {
    let t = this.check_(env);
    if (targetType instanceof ReferenceType && t == nullType)
      return;
    if (!targetType.equals(t))
      this.executionError("Deze uitdrukking heeft type " + t + ", maar hier wordt een uitdrukking met type " + targetType + " verwacht");
  }
  
  async evaluateBinding(env: Scope, allowReadOnly?: boolean): Promise<(pop?: (nbOperands: number) => Value[]) => any> {
    this.executionError("Deze uitdrukking mag niet aan de linkerkant van een toekenning voorkomen");
  }

  push(value: Value) {
    push(new OperandBinding(this, value));
  }

  abstract evaluate(env: Scope): Promise<Value>;
}

class IntLiteral extends Expression {

  constructor(loc: Loc, public value: number, public silent?: boolean) {
    super(loc, loc);
  }

  check(env: Scope) {
    return intType;
  }

  async evaluate(env: Scope) {
    if (this.silent !== true)
      await this.breakpoint();
    this.push(+this.value);
  }
}

class BooleanLiteral extends Expression {

  constructor(loc: Loc, public value: boolean, public silent?: boolean) {
    super(loc, loc);
  }

  check(env: Scope) {
    return booleanType;
  }

  async evaluate(env: Scope) {
    if (this.silent !== true)
      await this.breakpoint();
    this.push(this.value);
  }
}

class NullLiteral extends Expression {
  constructor(loc: Loc) {
    super(loc, loc);
  }

  check(env: Scope) {
    return nullType;
  }

  async evaluate(env: Scope) {
    await this.breakpoint();
    this.push(null);
  }
}

class UnaryOperatorExpression extends Expression {

  constructor(loc: Loc, instrLoc: Loc, public operator: string, public operand: Expression) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    switch (this.operator) {
      case 'not':
        this.operand.checkAgainst(env, booleanType);
        return booleanType;
      default:
        this.executionError("Bewerkingsteken niet ondersteund");
    }
  }

  eval(v: Value) {
    switch (this.operator) {
      case 'not': return !v;
      default:
        this.executionError("Bewerkingsteken niet ondersteund");
    }
  }

  async evaluate(env: Scope) {
    await this.operand.evaluate(env);
    await this.breakpoint();
    let [v] = pop(1);
    this.push(this.eval(v));
  }
}

class BinaryOperatorExpression extends Expression {

  constructor(loc: Loc, instrLoc: Loc, public leftOperand: Expression, public operator: string, public rightOperand: Expression) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    switch (this.operator) {
      case '+':
        const lhsType = this.leftOperand.check_(env);
        if (!lhsType.isAddable())
          this.executionError("De linker operand ondersteunt geen optelling");
        this.rightOperand.checkAgainst(env, lhsType);
        return lhsType;
      case 'in':
        const rhsType = this.rightOperand.check_(env).unwrapInferredType();
        rhsType.isListType(); // Force list type if not yet inferred
        if (!(rhsType instanceof ListType))
          return this.executionError("De rechter operand is geen lijst");
        this.leftOperand.checkAgainst(env, rhsType.elementType);
        return booleanType;
      case '-':
      case '*':
      case '/':
      case '%':
      case '>>':
      case '>>>':
      case '<<':
      case '&':
      case '|':
      case '^':
        this.leftOperand.checkAgainst(env, intType);
        this.rightOperand.checkAgainst(env, intType);
        return intType;
      case '<':
      case '<=':
      case '>':
      case '>=':
        this.leftOperand.checkAgainst(env, intType);
        this.rightOperand.checkAgainst(env, intType);
        return booleanType;
      case '&&':
      case '||':
        this.leftOperand.checkAgainst(env, booleanType);
        this.rightOperand.checkAgainst(env, booleanType);
        return booleanType;
      case '==':
      case '!=':
        let lt = this.leftOperand.check_(env);
        this.rightOperand.checkAgainst(env, lt);
        return booleanType;
      default:
        this.executionError("Bewerkingsteken niet ondersteund");
    }
  }

  eval(v1: Value, v2: Value) {
    switch (this.operator) {
      case '+':
        if (v1 instanceof ListObject && v2 instanceof ListObject)
          return v1.plus(v2);
        if (typeof v1 == 'number' && typeof v2 == 'number')
          return (v1 + v2)|0;
        this.executionError("Foute operanden");
      case 'in':
        if (!(v2 instanceof ListObject))
          return this.executionError("Rechter operand is geen lijst");
        return v2.getElements().some(e => valueEquals(e, v1));
      case '-': return (v1 - v2)|0;
      case '*': return (v1 * v2)|0;
      case '/': return (v1 / v2)|0;
      case '%': return (v1 % v2)|0;
      case '&': return v1 & v2;
      case '|': return v1 | v2;
      case '^': return v1 ^ v2;
      case '>>': return v1 >> v2;
      case '>>>': return v1 >>> v2;
      case '<<': return v1 << v2;
      case '==':
        return valueEquals(v1, v2);
      case '!=':
        return !valueEquals(v1, v2);
      case '<': return v1 < v2;
      case '<=': return v1 <= v2;
      case '>': return v1 > v2;
      case '>=': return v1 >= v2;
      default: this.executionError("Bewerkingsteken '" + this.operator + "' niet ondersteund.");
    }
  }
  
  async evaluate(env: Scope) {
    await this.leftOperand.evaluate(env);
    if (this.operator == '&&' || this.operator == '||') {
      await this.breakpoint();
      let [b] = pop(1);
      if (b == (this.operator == '&&'))
        await this.rightOperand.evaluate(env);
      else
        this.push(b);
    } else {
      await this.rightOperand.evaluate(env);
      await this.breakpoint();
      let [v1, v2] = pop(2);
      this.push(this.eval(v1, v2));
    }
  }
}

class VariableExpression extends Expression {
  binding: LocalBinding|undefined;
  proofOutlineVariable: Var_|undefined;

  constructor(loc: Loc, public name: string) {
    super(loc, loc);
  }

  check(env: Scope) {
    this.binding = env.lookup(this.loc, this.name) as LocalBinding;
    return this.binding.declaration.type.type;
  }
  
  async evaluateBinding(env: Scope, allowReadOnly?: boolean) {
    return () => env.lookup(this.loc, this.name, !allowReadOnly);
  }
  
  async evaluate(env: Scope) {
    await this.breakpoint();
    this.push(env.lookup(this.loc, this.name).value);
  }

  getProofOutlineVariable(onError: () => never): Var_ {
    if (!this.proofOutlineVariable)
      this.proofOutlineVariable = mkVar(this.name, parseProofOutlineType(this.binding!.declaration.type.type, onError));
    return this.proofOutlineVariable;
  }
}

class AssignmentExpression extends Expression {

  declaration: any;

  constructor(loc: Loc, instrLoc: Loc, public lhs: Expression, public op: string, public rhs: Expression) {
    super(loc, instrLoc);
    this.declaration = null;
  }

  check(env: Scope) {
    if (this.op == '=') {
      if (this.lhs instanceof VariableExpression && env.tryLookup(this.lhs.name) == null) {
        this.declaration = new VariableDeclarationStatement(this.loc, this.instrLoc!, new ImplicitTypeExpression(), this.lhs.loc, this.lhs.name, this.rhs);
        this.declaration.check(env);
        this.lhs.binding = env.bindings[this.lhs.name] as LocalBinding;
        return voidType;
      }
      let t = this.lhs.check_(env);
      this.rhs.checkAgainst(env, t);
      return voidType;
    } else {
      this.lhs.checkAgainst(env, intType);
      this.rhs.checkAgainst(env, intType);
      return voidType;
    }
  }

  evaluateOperator(lhs: Value, rhs: Value) {
    switch (this.op) {
      case '=': return rhs;
      case '+=': return (lhs + rhs)|0;
      case '-=': return (lhs - rhs)|0;
      case '*=': return (lhs * rhs)|0;
      case '/=': return (lhs / rhs)|0;
      case '%=': return (lhs % rhs)|0;
      case '&=': return lhs & rhs;
      case '|=': return lhs | rhs;
      case '^=': return lhs ^ rhs;
      case '>>=': return lhs >> rhs;
      case '>>>=': return lhs >>> rhs;
      case '<<=': return lhs << rhs;
      default:
        this.executionError("Bewerkingsteken niet ondersteund");
    }
  }
  
  async evaluate(env: Scope) {
    if (this.declaration) {
      await this.declaration.execute(env);
      this.push(new OperandBinding(this, 'void'));
      return;
    }

    let bindingThunk = await this.lhs.evaluateBinding(env);
    if (this.op != '=')
      this.push(bindingThunk(peek).value);
    await this.rhs.evaluate(env);
    await this.breakpoint();
    let [rhs] = pop(1);
    let [lhsValue] = this.op == '=' ? [undefined] : pop(1);
    let lhs = bindingThunk(pop);
    let result = this.evaluateOperator(lhsValue, rhs);
    this.push(lhs.setValue(result));
  }
}

class IncrementExpression extends Expression {

  constructor(loc: Loc, instrLoc: Loc, public operand: Expression, public isDecrement: boolean, public isPostfix: boolean) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    this.operand.checkAgainst(env, intType);
    return intType;
  }

  async evaluate(env: Scope) {
    let bindingThunk = await this.operand.evaluateBinding(env);
    await this.breakpoint();
    let lhs = bindingThunk(pop);
    let oldValue = lhs.value;
    if (this.isDecrement)
      lhs.value = (lhs.value - 1)|0;
    else
      lhs.value = (lhs.value + 1)|0;
    this.push(this.isPostfix ? oldValue : lhs.value);
  }
}

let objectsCount = 0;
let objectsShown: any[] = [];

function collectGarbage() {
  for (let o of objectsShown)
    o.marked = false;
  for (let stackFrame of callStack)
    for (let binding of stackFrame.allBindings())
      if (binding.value instanceof JavaObject)
        binding.value.mark();
  let newObjectsShown = [];
  for (let o of objectsShown) {
    if (o.marked)
      newObjectsShown.push(o);
    else
      o.hide();
  }
  objectsShown = newObjectsShown;
}

function computeNextObjectY() {
  let svg = document.getElementById('arrows-svg')!;
  let svgRect = svg.getClientRects()[0];

  let nextObjectY = 0;
  
  for (let o of objectsShown) {
    let rect = o.domNode.getClientRects()[0];
    nextObjectY = Math.max(nextObjectY, rect.bottom - svgRect.top + 15);
  }

  return nextObjectY;
}

function createHeapObjectDOMNode(object: JavaObject) {
  let heap = document.getElementById('heap')!;
  let node = document.createElement('table');
  heap.appendChild(node);
  node.className = 'object-table';
  node.style.left = "0px";
  node.style.top = computeNextObjectY() + "px";
  node.onmousedown = event0 => {
    event0.preventDefault();
    let left0 = node.offsetLeft;
    let top0 = node.offsetTop;
    let moveListener = (event: MouseEvent) => {
      event.preventDefault();
      node.style.left = (left0 + event.x - event0.x) + "px";
      node.style.top = (top0 + event.y - event0.y) + "px";
      updateArrows();
    };
    let upListener = (event: MouseEvent) => {
      document.removeEventListener('mousemove', moveListener);
      document.removeEventListener('mouseup', upListener);
    };
    document.addEventListener('mousemove', moveListener);
    document.addEventListener('mouseup', upListener);
  };
  
  objectsShown.push(object);
  node.className = 'object-table';
  let titleRow = document.createElement('tr');
  node.appendChild(titleRow);
  let titleCell = document.createElement('td');
  titleRow.appendChild(titleCell);
  titleCell.colSpan = 2;
  titleCell.className = 'object-title-td';
  titleCell.innerText = object.toString();
  for (let field in object.fields) {
    let fieldRow = document.createElement('tr');
    node.appendChild(fieldRow);
    let nameCell = document.createElement('td');
    fieldRow.appendChild(nameCell);
    nameCell.className = 'field-name';
    nameCell.innerText = field;
    let valueCell = document.createElement('td');
    fieldRow.appendChild(valueCell);
    valueCell.className = 'field-value';
    valueCell.innerText = object.fields[field].value;
    object.fields[field].valueCell = valueCell;
  }
  return node;
}

function updateFieldArrows() {
  for (let o of objectsShown)
    o.updateFieldArrows();
}

class FieldBinding {

  arrow: SVGLineElement|null = null;
  valueCell: any;

  constructor(public value: Value) {}
  
  setValue(value: Value) {
    if (this.arrow != null) {
      this.arrow.parentNode!.removeChild(this.arrow);
      this.arrow = null;
    }
    this.value = value;
    if (value instanceof JavaObject) {
      this.arrow = createArrow(this.valueCell, value.domNode);
      this.valueCell.innerText = "()";
      this.valueCell.style.color = "white";
    } else {
      this.valueCell.innerText = value == null ? "null" : value;
      this.valueCell.style.color = "black";
    }
    return value;
  }
  
  updateArrow() {
    this.setValue(this.value);
  }
}

class JavaObject {

  id = ++objectsCount;
  marked: any;
  domNode: any;

  constructor(public type: ReferenceType, public fields: {[index: string]: FieldBinding}) {
    if (typeof document !== 'undefined')
      this.domNode = createHeapObjectDOMNode(this);
  }

  toString() {
    return this.type.toString() + " (id=" + this.id + ")";
  }
  
  mark() {
    if (!this.marked) {
      this.marked = true;
      for (let field in this.fields) {
        let value = this.fields[field].value;
        if (value instanceof JavaObject)
          value.mark();
      }
    }
  }
  
  hide() {
    this.domNode.parentNode.removeChild(this.domNode);
    for (let field in this.fields) // Remove arrows
      this.fields[field].setValue(null);
  }
  
  updateFieldArrows() {
    for (let field in this.fields)
      this.fields[field].updateArrow();
  }
}

function initialClassFieldBindings(class_: Class) {
  let fields: {[index: string]: FieldBinding} = {};
  for (let field in class_.fields)
    fields[field] = new FieldBinding(class_.fields[field].type.resolve().defaultValue());
  return fields;
}

class JavaClassObject extends JavaObject {
  constructor(public class_: Class) {
    super(class_.type, initialClassFieldBindings(class_));
  }
}

function initialArrayFieldBindings(initialContents: Value[]) {
  let fields: {[index: string]: FieldBinding} = {};
  for (let i = 0; i < initialContents.length; i++)
    fields[i] = new FieldBinding(initialContents[i]);
  return fields;
}

function valueEquals(value1: unknown, value2: unknown) {
  if (value1 instanceof ListObject && value2 instanceof ListObject)
    return value1.equals(value2);
  return value1 == value2;
}

class ListObject extends JavaObject {
  length: number;
  constructor(public elementType: Type, initialContents: Value[]) {
    super(new ListType(elementType), initialArrayFieldBindings(initialContents));
    this.length = initialContents.length;
  }
  getElements() {
    let result = [];
    for (let i = 0; i < this.length; i++)
      result.push(this.fields[i].value);
    return result;
  }
  plus(other: ListObject) {
    return new ListObject(this.elementType, this.getElements().concat(other.getElements()));
  }
  equals(v2: ListObject) {
    if (this.length != v2.length)
      return false;
    for (let i = 0; i < this.length; i++)
      if (!valueEquals(this.fields[i].value, v2.fields[i].value))
        return false;
    return true;
  }
}

class NewExpression extends Expression {
  constructor(loc: Loc, instrLoc: Loc, public className: string) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    if (!has(classes, this.className))
      this.executionError("Er is geen klasse genaamd " + this.className);
    return classes[this.className].type;
  }
  
  async evaluate(env: Scope) {
    await this.breakpoint();
    if (!has(classes, this.className))
      this.executionError("Er is geen klasse genaamd " + this.className);
    this.push(new JavaClassObject(classes[this.className]));
  }
}

class NewArrayExpression extends Expression {
  constructor(loc: Loc, instrLoc: Loc, public elementType: TypeExpression, public lengthExpr: Expression) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    this.elementType.resolve();
    this.lengthExpr.checkAgainst(env, intType);
    return new ListType(this.elementType.type!);
  }

  async evaluate(env: Scope) {
    await this.lengthExpr.evaluate(env);
    await this.breakpoint();
    let [length] = pop(1);
    if (length < 0)
      this.executionError("Negatieve lengte");
    this.elementType.resolve();
    this.push(new ListObject(this.elementType.type!, Array(length).fill(this.elementType.type!.defaultValue())));
  }
}

class ListExpression extends Expression {
  constructor(loc: Loc, instrLoc: Loc, public elementType: TypeExpression, public elementExpressions: Expression[]) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    this.elementType.resolve();
    for (let e of this.elementExpressions)
      e.checkAgainst(env, this.elementType.type!);
    return new ListType(this.elementType.type!);
  }

  async evaluate(env: Scope) {
    for (let e of this.elementExpressions)
      await e.evaluate(env);
    await this.breakpoint();
    let elements = pop(this.elementExpressions.length);
    this.elementType.resolve();
    this.push(new ListObject(this.elementType.type!, elements));
  }
}

class ReadOnlyBinding {
  constructor(public value: Value) {}
}

class SelectExpression extends Expression {
  constructor(loc: Loc, instrLoc: Loc, public target: Expression, public selectorLoc: Loc, public selector: string) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    let targetType = this.target.check_(env);
    if (targetType instanceof ListType) {
      if (this.selector != "length")
        this.executionError("Lijsten hebben geen veld genaamd '" + this.selector + "'");
      return intType;
    }
    if (!(targetType instanceof ClassType))
      this.executionError("Doel-uitdrukking moet van klassetype zijn");
    if (!has(targetType.class_.fields, this.selector))
      this.executionError("Klasse " + targetType.class_.name + " heeft geen veld genaamd '" + this.selector + "'");
    return targetType.class_.fields[this.selector].type.type!;
  }
  
  async evaluateBinding(env: Scope, allowReadOnly?: boolean) {
    await this.target.evaluate(env);
    return (pop?: (nbOperands: number) => Value[]) => {
      let [target] = pop!(1);
      if (target instanceof ListObject) {
        if (this.selector != "length")
          this.executionError(target + " heeft geen veld genaamd '" + this.selector + "'");
        if (allowReadOnly !== true)
          this.executionError("Je kan de lengte van een lijst niet aanpassen");
        return new ReadOnlyBinding(target.length);
      }
      if (!(target instanceof JavaObject))
        this.executionError(target + " is geen object");
      if (!has(target.fields, this.selector))
        this.executionError("Doelobject heeft geen veld genaamd " + this.selector);
      return target.fields[this.selector];
    }
  }
  
  async evaluate(env: Scope) {
    let bindingThunk = await this.evaluateBinding(env, true);
    await this.breakpoint();
    this.push(bindingThunk(pop).value);
  }
}

class SubscriptExpression extends Expression {
  constructor(loc: Loc, instrLoc: Loc, public target: Expression, public index: Expression) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    let targetType = this.target.check_(env);
    if (!(targetType.isListType()))
      this.executionError("Het doel van een element-uitdrukking moet een lijst zijn");
    this.index.checkAgainst(env, intType);
    return (targetType.unwrapInferredType() as ListType).elementType;
  }

  async evaluateBinding(env: Scope) {
    await this.target.evaluate(env);
    await this.index.evaluate(env);
    return (pop?: (nbOperands: number) => Value[]) => {
      let [target, index] = pop!(2);
      if (!(target instanceof ListObject))
        this.executionError(target + " is geen lijst");
      if (index < 0)
        index += target.length;
      if (index < 0)
        this.executionError("Negative lijst-index " + index);
      if (target.length <= index)
        this.executionError("Lijst-index " + index + " is niet kleiner dan de lengte " + target.length + " van de lijst");
      return target.fields[index];
    }
  }

  async evaluate(env: Scope) {
    let bindingThunk = await this.evaluateBinding(env);
    await this.breakpoint();
    this.push(bindingThunk(pop).value);
  }
}

class LenExpression extends Expression {
  constructor(loc: Loc, instrLoc: Loc, public target: Expression) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    let targetType = this.target.check_(env);
    if (!targetType.isListType())
      this.executionError("Argument van 'len moet een lijst zijn");
    return intType;
  }

  async evaluate(env: Scope) {
    await this.target.evaluate(env);
    let [target] = pop(1);
    if (!(target instanceof ListObject))
      this.executionError(target + ' is geen lijst');
    this.push(target.length);
  }
}

class SliceExpression extends Expression {
  constructor(loc: Loc, instrLoc: Loc, public target: Expression, public startIndex: Expression, public endIndex: Expression) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    let targetType = this.target.check_(env);
    if (!targetType.isListType())
      this.executionError('Doen van een slice-uitdrukking moet een lijst zijn');
    this.startIndex.checkAgainst(env, intType);
    this.endIndex.checkAgainst(env, intType);
    return targetType;
  }

  async evaluate(env: Scope) {
    await this.target.evaluate(env);
    await this.startIndex.evaluate(env);
    await this.endIndex.evaluate(env);
    let [target, startIndex, endIndex] = pop(3);
    if (!(target instanceof ListObject))
      this.executionError(target + " is geen lijst");
    if (startIndex < 0)
      startIndex += target.length;
    if (endIndex < 0)
      endIndex += target.length;
    if (startIndex < 0)
      startIndex = 0;
    if (target.length < endIndex)
      endIndex = target.length;
    let sliceElements = [];
    if (endIndex <= startIndex)
      sliceElements = [];
    else
      sliceElements = target.getElements().slice(startIndex, endIndex);
    this.push(new ListObject(target.elementType, sliceElements));
  }
}

class CallExpression extends Expression {
  arguments: Expression[];
  method: AbstractMethodDeclaration|undefined;
  constructor(loc: Loc, instrLoc: Loc, public callee: Expression, args: Expression[]) {
    super(loc, instrLoc);
    this.arguments = args;
  }

  check(env: Scope) {
    if (this.callee instanceof VariableExpression) {
      if (!has(toplevelMethods, this.callee.name))
        this.executionError("Er bestaat geen functie met naam " + this.callee.name);
      this.method = toplevelMethods[this.callee.name];
      if (this.method.parameterDeclarations.length != this.arguments.length)
        this.executionError("Fout aantal argumenten");
      for (let i = 0; i < this.arguments.length; i++)
        this.arguments[i].checkAgainst(env, this.method.parameterDeclarations[i].type.type!);
      return this.method.returnType.type!;
    } else
      this.executionError("De opgeroepene-uitdrukking moet een functienaam zijn");
  }

  async evaluate(env: Scope) {
    if (this.callee instanceof VariableExpression) {
      if (!has(toplevelMethods, this.callee.name))
        this.executionError("Er bestaat geen functie met naam " + this.callee.name);
      let method = toplevelMethods[this.callee.name];
      if (method.parameterDeclarations.length != this.arguments.length)
        this.executionError("Fout aantal argumenten");
      for (let e of this.arguments)
        await e.evaluate(env);
      await this.breakpoint();
      let args = pop(this.arguments.length);
      await method.call(this, args);
    } else
      this.executionError("De opgeroepene-uitdrukking moet een functienaam zijn");
  }
}

abstract class Type {
  isListType() {
    return false;
  }
  isAddable() {
    return false;
  }
  constructor() {}
  toHTML() {
    let text = this.toString();
    if (has(keywords, text))
      return "<span class='keyword'>" + text + "</span>";
    return text;
  }
  unwrapInferredType(): Type {
    let t: Type = this;
    while (t instanceof InferredType && t.type != null)
      t = t.type;
    return t;
  }
  equals(other: Type): boolean {
    other = other.unwrapInferredType();
    if (other instanceof InferredType)
      return other.equals(this);
    return this == other;
  }
  abstract defaultValue(): Value;
}

class InferredType extends Type {
  type: Type|null = null;
  isAddable_: true|undefined;
  constructor() {
    super();
  }
  equals(other: Type): boolean {
    other = other.unwrapInferredType();
    if (this == other)
      return true;
    if (this.type != null)
      return this.type.equals(other);
    if (this.isAddable_ && !other.isAddable())
      return false;
    this.type = other;
    return true;
  }
  toString() {
    return this.type == null ? "?" : this.type.toString();
  }
  defaultValue() { return this.type ? this.type.defaultValue() : null; }
  isAddable(): boolean {
    if (this.type)
      return this.type.isAddable();
    return this.isAddable_ = true;
  }
  isListType(): boolean {
    if (this.type)
      return this.type.isListType();
    this.type = new ListType(new InferredType());
    return true;
  }
}

class AnyType extends Type {
  constructor() { super(); }
  defaultValue() { return null; }
  toString() { return "Any"; }
}

let anyType = new AnyType();

class IntType extends Type {
  constructor() { super(); }
  defaultValue() { return 0; }
  toString() { return "int"; }
  isAddable(): boolean {
      return true;
  }
}

let intType = new IntType();

class VoidType extends Type {
  constructor() { super(); }
  toString() { return "void"; }
  defaultValue() { return null; }
}

let voidType = new VoidType();

class BooleanType extends Type {
  constructor() { super(); }
  defaultValue() { return false; }
  toString() { return "boolean"; }
}

let booleanType = new BooleanType();

class ReferenceType extends Type {
  constructor() { super(); }
  defaultValue() { return null; }
}

class NullType extends ReferenceType {
  constructor() { super(); }
  toString() { return "nulltype"; }
}

let nullType = new NullType();

class ClassType extends ReferenceType {
  constructor(public class_: Class) {
    super();
  }
  toString() { return this.class_.name; }
}

class ListType extends ReferenceType {
  constructor(public elementType: Type) {
    super();
  }
  toString() { return "list[" + this.elementType.toString() + "]"; }
  toHTML() { return this.toString(); }
  equals(other: Type): boolean {
    other = other.unwrapInferredType();
    if (other instanceof InferredType)
      return other.equals(this);
    return other instanceof ListType && this.elementType.equals(other.elementType);
  }
  isAddable(): boolean {
      return true;
  }
  isListType(): boolean {
      return true;
  }
}

abstract class TypeExpression extends ASTNode {
  type: Type|undefined;
  constructor(loc: Loc) {
    super(loc, loc);
  }
  abstract resolve(): Type;
}

class ImplicitTypeExpression extends ASTNode {
  type: any;
  constructor(type?: Type) {
    super(null as unknown as Loc, null as unknown as Loc);
    this.type = type || new InferredType();
  }
  resolve() {
    return this.type;
  }
}

class LiteralTypeExpression extends TypeExpression {
  constructor(loc: Loc, public type: Type) {
    super(loc);
  }
  resolve() {
    return this.type;
  }
}

class ClassTypeExpression extends TypeExpression {
  constructor(loc: Loc, public name: string) {
    super(loc);
  }
  resolve() {
    if (!has(classes, this.name))
      throw new LocError(this.loc, "Er bestaat geen klasse met deze naam");
    return this.type = classes[this.name].type;
  }
}

class ArrayTypeExpression extends TypeExpression {
  elementType: any;
  constructor(loc: Loc, public elementTypeExpression: TypeExpression) {
    super(loc);
  }
  resolve() {
    this.elementType = this.elementTypeExpression.resolve();
    this.type = new ListType(this.elementType);
    return this.type;
  }
}

abstract class Statement extends ASTNode {
  constructor(loc: Loc, instrLoc: Loc) {
    super(loc, instrLoc);
  }
  abstract check(env: Scope): void
  abstract execute(env: Scope): Promise<Value>
}

class VariableDeclarationStatement extends Statement {
  constructor(loc: Loc, instrLoc: Loc, public type: TypeExpression, public nameLoc: Loc, public name: string, public init: Expression) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    this.type.resolve();
    if (env.tryLookup(this.name) != null)
      throw new ExecutionError(this.nameLoc, "Er bestaat hier al een variabele met naam '" + this.name + "'.");
    this.init.checkAgainst(env, this.type.type!);
    env.bindings[this.name] = new LocalBinding(this, this.type.type);
  }
  
  async execute(env: Scope) {
    await this.init.evaluate(env);
    await this.breakpoint();
    let [v] = pop(1);
    env.bindings[this.name] = new LocalBinding(this, v);
  }
}

class PassStatement extends Statement {
  constructor(loc: Loc, instrLoc: Loc) {
    super(loc, instrLoc);
  }

  check(env: Scope) {}
  async execute(env: Scope) {}
}

class ExpressionStatement extends Statement {
  constructor(loc: Loc, instrLoc: Loc, public expr: Expression) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    this.expr.check_(env);
  }
  
  async execute(env: Scope) {
    await this.expr.evaluate(env);
    pop(1);
  }
}

class ReturnStatement extends Statement {
  constructor(loc: Loc, instrLoc: Loc, public operand?: Expression|null) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    let resultType = env.tryLookup("#result");
    if (resultType == null)
      this.executionError("'return'-opdrachten zijn hier niet toegelaten");
    if (this.operand == null) {
      if (resultType.value != voidType)
        this.executionError("Resultaatwaarde verwacht");
    } else {
      this.operand.checkAgainst(env, resultType.value);
    }
  }

  async execute(env: Scope) {
    if (this.operand != null) {
      await this.operand.evaluate(env);
      await this.breakpoint();
      let [v] = pop(1);
      return v;
    } else {
      return "void";
    }
  }
}

class BlockStatement extends Statement {
  scope: Scope|undefined;
  constructor(loc: Loc, public stmts: Statement[]) {
    super(loc, loc);
  }

  check(env: Scope) {
    this.scope = new Scope(env);
    for (let stmt of this.stmts)
      stmt.check(this.scope);
  }

  async execute(env: Scope) {
    let result;
    for (let stmt of this.stmts) {
      result = await stmt.execute(env);
      if (result !== undefined)
        break;
    }
    return result;
  }
}

let iterationCount = 0;

class WhileStatement extends Statement {
  constructor(loc: Loc, instrLoc: Loc, public condition: Expression, public body: Statement) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    this.condition.checkAgainst(env, booleanType);
    this.body.check(env);
  }

  async execute(env: Scope) {
    let result;
    while (result === undefined) {
      iterationCount++;
      if (iterationCount == 1000)
        this.executionError("Teveel lus-iteraties. Mogelijke oneindige lus.");
      await this.condition.evaluate(env);
      await this.breakpoint();
      let [b] = pop(1);
      if (!b)
        break;
      result = await this.body.execute(env);
    }
    return result;
  }
}

class IfStatement extends Statement {
  constructor(loc: Loc, instrLoc: Loc, public condition: Expression, public thenBody: Statement, public elseBody: Statement|null) {
    super(loc, instrLoc);
  }

  check(env: Scope) {
    this.condition.checkAgainst(env, booleanType);
    this.thenBody.check(env);
    if (this.elseBody != null)
      this.elseBody.check(env);
    if (this.thenBody instanceof BlockStatement && this.elseBody instanceof BlockStatement) {
      for (const x in this.thenBody.scope!.bindings) {
        if (env.tryLookup(x) == null && has(this.elseBody.scope!.bindings, x)) {
          const thenBinding = this.thenBody.scope!.bindings[x] as LocalBinding;
          const elseBinding = this.elseBody.scope!.bindings[x] as LocalBinding;
          if (thenBinding.value.equals(elseBinding.value))
            env.bindings[x] = new LocalBinding(thenBinding.declaration, thenBinding.value);
        }
      }
    }
  }

  async execute(env: Scope) {
    await this.condition.evaluate(env);
    await this.breakpoint();
    let [b] = pop(1);
    if (b)
      return await this.thenBody.execute(env);
    else if (this.elseBody != null)
      return await this.elseBody.execute(env);
  }
}

class AssertStatement extends Statement {
  constructor(loc: Loc, instrLoc: Loc, public condition: Expression, public comment: Comment_|null) {
    super(loc, instrLoc);
  }
  
  check(env: Scope) {
    this.condition.checkAgainst(env, booleanType);
  }
  
  async execute(env: Scope) {
    await this.condition.evaluate(env);
    await this.breakpoint();
    let [b] = pop(1);
    if (!b)
      this.executionError("De bewering is onwaar");
  }
}

class Declaration extends ASTNode {
  constructor(loc: Loc, public name: string) {
    super(loc, null);
  }
}

class ParameterDeclaration extends Declaration {
  proofOutlineVariable: Var_|undefined;
  constructor(loc: Loc, public type: TypeExpression, public nameLoc: Loc, name: string) {
    super(loc, name);
  }

  check() {
    this.type.resolve();
  }
  getProofOutlineVariable(onError: () => never): Var_ {
    if (!this.proofOutlineVariable)
      this.proofOutlineVariable = mkVar(this.name, parseProofOutlineType(this.type.type!, onError));
    return this.proofOutlineVariable;
  }
}

let maxCallStackDepth = 100;

abstract class AbstractMethodDeclaration extends Declaration {
  constructor(loc: Loc, public returnType: TypeExpression, name: string, public parameterDeclarations: ParameterDeclaration[]) {
    super(loc, name);
  }
  abstract call(callExpr: Expression, args: Value[]): Promise<Value>;
  abstract enter(): void;
  abstract check(): void;
  abstract checkProofOutlines(): void;
}

class MethodDeclaration extends AbstractMethodDeclaration {
  implicitReturnStmt: ReturnStatement;
  constructor(loc: Loc, returnType: TypeExpression, public nameLoc: Loc, name: string, parameterDeclarations: ParameterDeclaration[], public bodyBlock: Statement[]) {
    super(loc, returnType, name, parameterDeclarations);
    let closeBraceLoc = new Loc(loc.doc, loc.end - 1, loc.end);
    this.implicitReturnStmt = new ReturnStatement(closeBraceLoc, closeBraceLoc);
  }

  enter() {
    this.returnType.resolve();
    for (let p of this.parameterDeclarations)
      p.check();
  }

  check() {
    let env = new Scope(null);
    for (let p of this.parameterDeclarations) {
      if (has(env.bindings, p.name))
        this.executionError("Er bestaat al een parameter met deze naam");
      env.bindings[p.name] = new LocalBinding(p, p.type.type);
    }
    env.bindings["#result"] = new LocalBinding(this, this.returnType.type);
    for (let stmt of this.bodyBlock)
      stmt.check(env);
  }

  async call(callExpr: CallExpression, args: Value[]) {
    let env = new Scope(null);
    if (callStack.length >= maxCallStackDepth)
      throw new LocError(callExpr.loc, "Maximum aantal genestelde oproepen (= " + maxCallStackDepth + ") overschreden");
    let stackFrame = new StackFrame(this.name, env);
    callStack.push(stackFrame);
    for (let i = 0; i < args.length; i++)
      env.bindings[this.parameterDeclarations[i].name] = new LocalBinding(this.parameterDeclarations[i], args[i]);
    let result;
    for (let stmt of this.bodyBlock) {
      result = await stmt.execute(env);
      if (result !== undefined)
        break;
    }
    if (result === undefined) {
      await checkBreakpoint(this.implicitReturnStmt);
      result = "void";
    }
    callStack.pop();
    push(new OperandBinding(callExpr, result));
  }

  checkProofOutlines() {
    let env = this.parameterDeclarations.reduceRight((acc, d) => {
      return EnvCons(d.getProofOutlineVariable(() => {
        return d.executionError(`Parameters van type ${d.type.type!.toString()} worden nog niet ondersteund in bewijssilhouetten`);
      }), acc)
    }, EnvNil);
    let outlineStart = null;
    let outlineStartComment = null;
    let outlineStartEnv = null;
    let total = null;

    for (let i = 0; i < this.bodyBlock.length; i++) {
      const stmt = this.bodyBlock[i];
      if (stmt instanceof ExpressionStatement && stmt.expr instanceof AssignmentExpression && stmt.expr.declaration != null)
        env = EnvCons(stmt.expr.declaration.name, env);
      if (stmt instanceof AssertStatement && stmt.comment != null) {
        if (stmt.comment.text.includes('PRECONDITION') || stmt.comment.text.includes('PRECONDITIE')) {
          if (outlineStart != null)
            stmt.executionError("Onverwachte PRECONDITIE-markering binnen in een bewijssilhouet");
          outlineStart = i;
          outlineStartComment = stmt.comment;
          outlineStartEnv = env;
          total = !(stmt.comment.text.includes('PARTIAL CORRECTNESS') || stmt.comment.text.includes('PARTIËLE CORRECTHEID') || stmt.comment.text.includes("PARTIELE CORRECTHEID"));
        }
        if (stmt.comment.text.includes('POSTCONDITION') || stmt.comment.text.includes("POSTCONDITIE")) {
          if (outlineStart == null)
            return stmt.executionError("POSTCONDITIE zonder PRECONDITIE");
          checkProofOutline(total!, outlineStartEnv!, this.bodyBlock.slice(outlineStart, i + 1));
          outlineStart = null;
          outlineStartComment = null;
          outlineStartEnv = null;
        }
      }
    }

    if (outlineStartComment != null)
      throw new LocError(outlineStartComment.loc(), "PRECONDITIE zonder POSTCONDITIE");
  }
}

const intListSort = TSort("list[int]");

function parseProofOutlineType(t: Type, onError: () => never) {
  t = t.unwrapInferredType();
  if (t == intType)
    return TInt;
  else if (t == booleanType)
    return TBool;
  else if (t instanceof ListType && t.elementType.equals(intType))
    return intListSort;
  return onError();
}

const intListPlusConst = mkConst("+", TFun(intListSort, TFun(intListSort, intListSort)));
const intListInConst = mkConst("in", TFun(TInt, TFun(intListSort, TBool)));
const intListSliceConst = mkConst("slice", TFun(intListSort, TFun(TInt, TFun(TInt, intListSort))));
const intListLenConst = mkConst("len", TFun(intListSort, TInt));
const intListSubscriptConst = mkConst("at", TFun(intListSort, TFun(TInt, TInt)));
const intListCons = mkConst("Cons", TFun(TInt, TFun(intListSort, intListSort)));
const intListNil = mkConst("Nil", intListSort);

function mkIntListTerm(l: Loc, elems: Term_[]): Term_ {
  return elems.reduceRight((acc, t) => App(l, App(l, Const(l, intListCons), t), acc), Const(l, intListNil));
}

function parseProofOutlineExpression(e: Expression): Term_ {
  if (e instanceof IntLiteral)
    return Val(e.loc, +e.value);
  else if (e instanceof BooleanLiteral)
    if (e.value)
      return BinOp(e.loc, Eq(TInt), Val(e.loc, 0), Val(e.loc, 0));
    else
      return BinOp(e.loc, Eq(TInt), Val(e.loc, 0), Val(e.loc, 1));
  else if (e instanceof VariableExpression)
    return Var(e.loc, e.getProofOutlineVariable(() => {
      e.executionError(`Variablen van type '${e.binding!.declaration.type.type}' worden nog niet ondersteund in bewijssilhouetten`);
    }));
  else if (e instanceof BinaryOperatorExpression) {
    const t1 = parseProofOutlineExpression(e.leftOperand);
    const t2 = parseProofOutlineExpression(e.rightOperand);
    let op = null;
    switch (e.operator) {
      case '+':
        if (e.leftOperand.type!.unwrapInferredType() instanceof ListType)
          return App(e.loc, App(e.loc, Const(e.loc, intListPlusConst), t1), t2);
        else if (e.leftOperand.type!.unwrapInferredType() == intType)
          op = Add;
        else
          throw new Error();
        break;
      case 'in':
        return App(e.loc, App(e.loc, Const(e.loc, intListInConst), t1), t2);
      case '-': op = Sub; break;
      case '*': op = Mul; break;
      case '==':
        op = Eq(parseProofOutlineType(e.leftOperand.type!, () => {
          e.executionError(`Het vergelijken van waarden van type ${e.leftOperand.type!} wordt nog niet ondersteund`);
        }));
        break;
      case '<=': op = Le; break;
      case '>=': return BinOp(e.loc, Le, t2, t1);
      case '<': return BinOp(e.loc, Le, BinOp(e.loc, Add, t1, Val(e.loc, 1)), t2);
      case '>': return BinOp(e.loc, Le, BinOp(e.loc, Add, t2, Val(e.loc, 1)), t1);
      case '!=':
        const tp = parseProofOutlineType(e.leftOperand.type!, () => {
          e.executionError(`Het vergelijken van waarden van type ${e.leftOperand.type!} wordt nog niet ondersteund`);
        });
        return Not(e.loc, BinOp(e.loc, Eq(tp), t1, t2));
      case '&&': op = And; break;
      default:
        e.executionError("Dit bewerkingsteken wordt nog niet ondersteund in bewijssilhouetten");
    }
    return BinOp(e.loc, op, t1, t2);
  } else if (e instanceof UnaryOperatorExpression) {
    let op = null;
    switch (e.operator) {
      case 'not':
        return Not(e.loc, parseProofOutlineExpression(e.operand));
      default:
        e.executionError("Dit bewerkingsteken wordt nog niet ondersteund in bewijssilhouetten");
    }
  } else if (e instanceof CallExpression) {
    const parseType = (t: Type) => {
      return parseProofOutlineType(t, () => {
        return e.callee.executionError("Oproepen van functies met een parameter van type '" + t.toString() + "' worden nog niet ondersteund in bewijssilhouetten");
      });
    };
    const constType = e.method!.parameterDeclarations.reduceRight(
      (acc, p) => TFun(parseType(p.type.type!), acc),
      parseType(e.method!.returnType.type!)
    );
    return e.arguments.reduce(
      (acc, arg) => App(e.loc, acc, parseProofOutlineExpression(arg)),
      Const(e.callee.loc, mkConst(e.method!.name, constType))
    );
  } else if (e instanceof ListExpression) {
    if (!e.elementType.type!.equals(intType))
      e.executionError("Lijsten waarvan de elementen geen int-waarden zijn worden nog niet ondersteund in bewijssilhouetten");
    return mkIntListTerm(e.loc, e.elementExpressions.map(parseProofOutlineExpression));
  } else if (e instanceof LenExpression) {
    if (!(e.target.type!.unwrapInferredType() as ListType).elementType.equals(intType))
      e.executionError("Lijsten waarvan de elementen geen int-waarden zijn worden nog niet ondersteund in bewijssilhouetten");
    return App(e.loc, Const(e.loc, intListLenConst), parseProofOutlineExpression(e.target));
  } else if (e instanceof SliceExpression) {
    if (!(e.target.type!.unwrapInferredType() as ListType).elementType.equals(intType))
      e.executionError("Lijsten waarvan de elementen geen int-waarden zijn worden nog niet ondersteund in bewijssilhouetten");
    return App(e.loc, App(e.loc, App(e.loc, Const(e.loc, intListSliceConst), parseProofOutlineExpression(e.target)), parseProofOutlineExpression(e.startIndex)), parseProofOutlineExpression(e.endIndex));
  } else if (e instanceof SubscriptExpression) {
    if (!(e.target.type!.unwrapInferredType() as ListType).elementType.equals(intType))
      e.executionError("Lijsten waarvan de elementen geen int-waarden zijn worden nog niet ondersteund in bewijssilhouetten");
    return App(e.loc, App(e.loc, Const(e.loc, intListSubscriptConst), parseProofOutlineExpression(e.target)), parseProofOutlineExpression(e.index));
  } else
    e.executionError("Deze vorm van uitdrukking wordt nog niet ondersteund in een bewijssilhouet");
}

class JustificationScanner {

  text: any;
  pos = -1;
  c: any;
  tokenStart: any;
  value: number|null = null;
  token: any;

  constructor(public comment: Comment_) {
    this.text = this.comment.text;
    this.eat();
  }

  eat() {
    this.pos++;
    this.c = (this.pos == this.text.length ? '<EINDE>' : this.text.charAt(this.pos));
  }

  nextToken0() {
  eatWhite:
    for (;;) {
      switch (this.c) {
        case ' ':
        case '\t':
          this.eat();
          break;
        default:
          break eatWhite;
      }
    }
    this.tokenStart = this.pos;
    if (this.c == '<EINDE>' || this.c == '#')
      return '<EINDE>';
    if (isDigit(this.c)) {
      this.eat();
      while (isDigit(this.c))
        this.eat();
      const text = this.text.substring(this.tokenStart, this.pos);
      const value = +text;
      if (text != value.toString())
        this.error("Getal te groot");
      this.value = value;
      return '<GETAL>';
    }
    if (isAlpha(this.c)) {
      this.eat();
      while (isAlpha(this.c) || isDigit(this.c))
        this.eat();
      this.value = null;
      return this.text.substring(this.tokenStart, this.pos);
    }
    throw new LocError(this.comment.locFactory(this.comment.start + this.tokenStart, this.comment.start + this.tokenStart + 1), "Bad character");
  }

  nextToken() {
    this.token = this.nextToken0();
    return this.token;
  }

  expect(token: string) {
    if (this.token != token)
      this.error(`'${token}' verwacht`);
    const value = this.value;
    this.nextToken();
    return value;
  }

  loc() {
    return this.comment.locFactory(this.comment.start + this.tokenStart, this.comment.start + this.pos);
  }

  error(msg: string): never {
    throw new LocError(this.loc(), msg);
  }
}

function expectConjunctIndex(scanner: JustificationScanner) {
  const lk = scanner.loc();
  const k = scanner.expect('<GETAL>')!;
  if (k == 0)
    throw new LocError(lk, "Conjunctnummer moet groter dan nul zijn");
  return k - 1;
}

function parseJustification(scanner: JustificationScanner) {
  switch (scanner.token) {
    case 'Z': {
      const l = scanner.loc();
      scanner.nextToken();
      if (scanner.token == 'op') {
        scanner.nextToken();
        const lk = scanner.loc();
        const k = expectConjunctIndex(scanner);
        return JZ_at(l, lk, +k);
      }
      return JZ(l);
    }
    case 'Herschrijven': {
      const l = scanner.loc();
      scanner.nextToken();
      scanner.expect('met');
      if (scanner.token == '<GETAL>') {
        const lk1 = scanner.loc();
        const k1 = expectConjunctIndex(scanner);
        scanner.expect('in');
        const lk2 = scanner.loc();
        const k2 = expectConjunctIndex(scanner);
        return JRewrite(l, lk1, k1, lk2, k2);
      }
      if (has(laws, scanner.token)) {
        const llawName = scanner.loc();
        const lawName = scanner.token;
        scanner.nextToken();
        const ks: [Loc, number][] = [];
        if (scanner.token == 'op') {
          scanner.expect('op');
          for (;;) {
            const lk = scanner.loc();
            const k = expectConjunctIndex(scanner);
            ks.push([lk, k]);
            if (scanner.token != 'en')
              break;
            scanner.expect('en');
          }
        }
        const ks_ = ks.reduceRight((acc, [lk, k]) => LawAppIndicesCons(lk, k, acc), LawAppIndicesNil);
        scanner.expect('in');
        const lk = scanner.loc();
        const k = expectConjunctIndex(scanner);
        return JRewriteWithLaw(l, laws[lawName].law, ks_, lk, k);
      }
      scanner.error("Conjunctnummer of naam van een wet verwacht");
    }
    default:
      if (has(laws, scanner.token)) {
        const l = scanner.loc();
        const lawName = scanner.token;
        scanner.nextToken();
        const ks: [Loc, number][] = [];
        if (scanner.token == 'op') {
          scanner.expect('op');
          for (;;) {
            const lk = scanner.loc();
            const k = expectConjunctIndex(scanner);
            ks.push([lk, k]);
            if (scanner.token != 'en')
              break;
            scanner.expect('en');
          }
        }
        const ks_ = ks.reduceRight((acc, [lk, k]) => LawAppIndicesCons(lk, k, acc), LawAppIndicesNil);
        return JLaw(l, laws[lawName].law, ks_);
      }
      scanner.error("'Z' of 'Herschrijven' of naam van een wet verwacht");
  }
}

function parseJustifications(comment: Comment_) {
  const scanner = new JustificationScanner(comment);
  scanner.nextToken();
  if (scanner.token == '<EINDE>')
    return JustifNil;
  let result = JustifNil;
  for (;;) {
    const j = parseJustification(scanner);
    result = JustifCons(j, result);
    if (scanner.token != 'of')
      break;
    scanner.nextToken();
  }
  if (scanner.token != '<EINDE>')
    scanner.error("Einde van de verantwoording verwacht");
  return result;
}

function parseProofOutline(stmts: Statement[], i: number, precededByAssert: boolean): Stmt_ {
  if (stmts.length == i)
    return Pass(null as unknown as Loc);
  const stmt = stmts[i];
  if (stmt instanceof AssertStatement) {
    const body = parseProofOutlineExpression(stmt.condition);
    const justif = precededByAssert && stmt.comment != null ? parseJustifications(stmt.comment) : JustifNil;
    return Seq(Assert(stmt.loc, body, justif), parseProofOutline(stmts, i + 1, true));
  } else if (stmt instanceof ExpressionStatement && stmt.expr instanceof AssignmentExpression && stmt.expr.op == '=' && stmt.expr.lhs instanceof VariableExpression) {
    const lhs = stmt.expr.lhs;
    const x = stmt.expr.lhs.getProofOutlineVariable(() => {
      return stmt.executionError(`Toekenningen aan variabelen van het type ${lhs.type} worden nog niet ondersteund.`);
    });
    return Seq(Assign(stmt.loc, x, parseProofOutlineExpression(stmt.expr.rhs)), parseProofOutline(stmts, i + 1, false));
  } else if (stmt instanceof IfStatement) {
    if (stmt.elseBody == null)
      return stmt.executionError("'if'-opdrachten in bewijssilhouetten moeten een 'else'-tak hebben. Voeg 'else: pass' toe.");
    if (!(stmt.thenBody instanceof BlockStatement) || !(stmt.elseBody instanceof BlockStatement))
      return stmt.executionError("In een bewijssilhouet moeten de takken van 'if'-opdrachten blokken zijn.");
    return Seq(If(stmt.loc, parseProofOutlineExpression(stmt.condition), parseProofOutline(stmt.thenBody.stmts, 0, false), parseProofOutline(stmt.elseBody.stmts, 0, false)), parseProofOutline(stmts, i + 1, false));
  } else if (stmt instanceof WhileStatement) {
    const cond = parseProofOutlineExpression(stmt.condition);
    if (!(stmt.body instanceof BlockStatement))
      return stmt.body.executionError("In een bewijssilhouet moet het lichaam van een lus een blok zijn.");
    const body = parseProofOutline(stmt.body.stmts, 0, false);
    return Seq(While(stmt.loc, cond, body), parseProofOutline(stmts, i + 1, false));
  } else if (stmt instanceof PassStatement) {
    return Seq(Pass(stmt.loc), parseProofOutline(stmts, i + 1, false));
  } else
    return stmt.executionError("Deze vorm van opdracht wordt nog niet ondersteund in een bewijssilhouet.");
}

function checkProofOutline(total: boolean, env: Env_, stmts: Statement[]) {
  const outline = parseProofOutline(stmts, 0, false);
  if (!stmt_is_well_typed(env, outline))
    throw new LocError(new Loc(stmts[0].loc.doc, stmts[0].loc.start, stmts[stmts.length - 1].loc.end), "Het bewijssilhouet voldoet niet aan de typeregels");
  const result = check_proof_outline(total, outline);
  if (!isOk(result))
    throw new LocError(getLoc(result), getMsg(result));
  nbProofOutlinesChecked++;
}

class BuiltInMethodDeclaration extends AbstractMethodDeclaration {
  constructor(returnType: TypeExpression, name: string, parameterDeclarations: ParameterDeclaration[], public body: (callExpr: CallExpression, args: Value[]) => Promise<Value>) {
    super(null as unknown as Loc, returnType, name, parameterDeclarations);
  }
  enter() {}
  check() {}
  async call(callExpr: CallExpression, args: Value[]) {
    let result = await this.body(callExpr, args);
    push(new OperandBinding(callExpr, result));
  }
  checkProofOutlines() {}
}

class FieldDeclaration extends Declaration {
  constructor(loc: Loc, public type: TypeExpression, name: string) {
    super(loc, name);
  }

  enter() {
    this.type.resolve();
  }
}

class Class extends Declaration {
  type: ClassType;
  fields: {[index: string]: FieldDeclaration} = {};
  constructor(loc: Loc, name: string, fields: FieldDeclaration[]) {
    super(loc, name);
    this.type = new ClassType(this);
    for (let field of fields) {
      if (has(this.fields, field.name))
        field.executionError("Een veld met deze naam bestaat al in deze klasse");
      this.fields[field.name] = field;
    }
  }

  enter() {
    for (let field in this.fields)
      this.fields[field].enter();
  }
}

class Loc {
  constructor(public doc: any, public start: number, public end: number) {}
}

function mkLocFactory(doc: any) {
  return (start: number, end: number) => new Loc(doc, start, end);
}

class LocError extends Error {
  constructor(public loc: Loc, public msg: string) {
    super();
  }
}

class ParseError extends LocError {
  constructor(loc: Loc, msg: string) {
    super(loc, msg);
  }
}

class ExecutionError extends LocError {
  constructor(loc: Loc, msg: string) {
    super(loc, msg);
  }
}

type RelationalChain = Expression | [Loc, Expression, string, RelationalChain];

class Parser {

  scanner: Scanner;
  token: any;
  posStack: any[];
  lastPos: any;
  lastValue: any;

  constructor(public locFactory: LocFactory, text: string, parseExpression?: boolean, commentListener?: (comment: Comment_) => void) {
    this.scanner = new Scanner(locFactory, text, parseExpression, commentListener);
    this.token = this.scanner.nextToken();
    this.posStack = [];
  }

  pushStart() {
    this.posStack.push(this.scanner.tokenStart);
  }

  popLoc() {
    return this.locFactory(this.posStack.pop(), this.lastPos);
  }

  dupLoc() {
    return this.locFactory(this.posStack[this.posStack.length - 1], this.lastPos);
  }

  tokenLoc() {
    return this.locFactory(this.scanner.tokenStart, this.scanner.pos);
  }

  parseError(msg: string): never {
    throw new ParseError(this.tokenLoc(), msg);
  }

  next() {
    this.lastValue = this.scanner.value;
    this.lastPos = this.scanner.pos;
    this.token = this.scanner.nextToken();
  }

  expect(token: string) {
    if (this.token != token)
      this.parseError((token == 'EINDE' ? "einde van de invoer " : token) + " verwacht");
    this.next();
    return this.lastValue;
  }

  parsePrimaryExpression(): Expression {
    this.pushStart();
    switch (this.token) {
      case 'GETAL':
        this.next();
        return new IntLiteral(this.popLoc(), this.lastValue);
      case 'NAAM':
        this.next();
        return new VariableExpression(this.popLoc(), this.lastValue);
      case "[": {
        this.pushStart();
        this.next();
        let instrLoc = this.popLoc();
        let elementExpressions = [];
        if (this.token != ']') {
          for (;;) {
            elementExpressions.push(this.parseExpression());
            if (this.token != ',')
              break;
            this.next();
          }
        }
        this.expect(']');
        let type = new ImplicitTypeExpression();
        return new ListExpression(this.popLoc(), instrLoc, type, elementExpressions);
      }
      case "new":
        this.next();
        let instrLoc = this.dupLoc();
        let type: TypeExpression|null = this.tryParsePrimaryType();
        if (type == null)
          return this.parseError("Type verwacht");
        if (this.token == '[') {
          this.next();
          let lengthExpr = null;
          if (this.token != ']')
            lengthExpr = this.parseExpression();
          this.expect(']');
          while (this.token == '[') {
            this.next();
            this.expect(']');
            type = new ArrayTypeExpression(type.loc, type);
          }
          let elementExpressions = null;
          if (this.token == '{') {
            this.next();
            elementExpressions = [];
            if (this.token != '}') {
              for (;;) {
                elementExpressions.push(this.parseExpression());
                if (this.token != ',')
                  break;
                this.next();
              }
            }
            this.expect('}');
          }
          let loc = this.popLoc();
          if (lengthExpr != null) {
            if (elementExpressions != null)
              throw new LocError(loc, "Vermeld ofwel een lengte, ofwel een initialisatie-uitdrukking; niet beide.");
            return new NewArrayExpression(loc, instrLoc, type, lengthExpr);
          } else {
            if (elementExpressions == null)
              throw new LocError(loc, "Vermeld een lengte of een initialisatie-uitdrukking.");
            return new ListExpression(loc, instrLoc, type, elementExpressions);
          }
        }
        if (!(type instanceof ClassTypeExpression))
          throw new LocError(type.loc, "Klassetype verwacht");
        this.expect('(');
        this.expect(')');
        return new NewExpression(this.popLoc(), instrLoc, type.name);
      case "(":
        this.next();
        let e = this.parseExpression();
        this.expect(")");
        this.popLoc();
        return e;
      case "None":
        this.next();
        return new NullLiteral(this.popLoc());
      case "True":
      case "False": {
        let kwd = this.token;
        this.next();
        return new BooleanLiteral(this.popLoc(), kwd == "True");
      }
      case "++":
      case "--": {
        this.pushStart();
        let op = this.token;
        this.next();
        let instrLoc = this.popLoc();
        let e = this.parsePostfixExpression();
        return new IncrementExpression(this.popLoc(), instrLoc, e, op == '--', false);
      }
      case "-": {
        this.pushStart();
        let op = this.token;
        this.next();
        let instrLoc = this.popLoc();
        let e = this.parsePostfixExpression();
        return new BinaryOperatorExpression(this.popLoc(), instrLoc, new IntLiteral(instrLoc, 0, true), '-', e);
      }
      case "not": {
        this.pushStart();
        let op = this.token;
        this.next();
        let instrLoc = this.popLoc();
        let e = this.parseRelationalExpression();
        return new UnaryOperatorExpression(this.popLoc(), instrLoc, op, e);
      }
      case "INDENT":
        return this.parseError("De inspringing van deze regel komt niet overeen met die van de vorige regel");
      default:
        return this.parseError("Getal of naam verwacht");
    }
  }
  
  parsePostfixExpression() {
    this.pushStart();
    let e = this.parsePrimaryExpression();
    for (;;) {
      switch (this.token) {
        case '.': {
          this.pushStart();
          this.next();
          this.pushStart();
          let x = this.expect('NAAM');
          let nameLoc = this.popLoc();
          let instrLoc = this.popLoc();
          e = new SelectExpression(this.dupLoc(), instrLoc, e, nameLoc, x);
          break;
        }
        case '(': {
          this.pushStart();
          this.next();
          let instrLoc = this.popLoc();
          let args = [];
          if (this.token != ')') {
            for (;;) {
              args.push(this.parseExpression());
              if (this.token != ',')
                break;
              this.next();
            }
          }
          this.expect(')');
          if (e instanceof VariableExpression && e.name == 'len') {
            if (args.length != 1)
              return this.parseError("'len' verwacht één argument");
            e = new LenExpression(this.dupLoc(), instrLoc, args[0]);
          } else
            e = new CallExpression(this.dupLoc(), instrLoc, e, args);
          break;
        }
        case '[': {
          this.pushStart();
          this.next();
          let instrLoc = this.popLoc();
          let startIndex;
          if (this.token == ':')
            startIndex = new IntLiteral(instrLoc, 0);
          else
            startIndex = this.parseExpression();
          if (this.token == ':') {
            this.next();
            let endIndex;
            if (this.token == ']')
              endIndex = new LenExpression(instrLoc, instrLoc, e);
            else
              endIndex = this.parseExpression();
            this.expect(']');
            e = new SliceExpression(this.dupLoc(), instrLoc, e, startIndex, endIndex);
          } else {
            this.expect(']');
            e = new SubscriptExpression(this.dupLoc(), instrLoc, e, startIndex);
          }
          break;
        }
        case '++':
        case '--': {
          this.pushStart();
          let op = this.token;
          this.next();
          let instrLoc = this.popLoc();
          e = new IncrementExpression(this.dupLoc(), instrLoc, e, op == '--', true);
          break;
        }
        default:
          this.popLoc();
          return e;
      }
    }
  }

  parseMultiplicativeExpression() {
    this.pushStart();
    let e = this.parsePostfixExpression();
    for (;;) {
      switch (this.token) {
        case '*':
        case '/':
        case '%':
          this.pushStart();
          let op = this.token;
          this.next();
          let instrLoc = this.popLoc();
          let rightOperand = this.parsePostfixExpression();
          e = new BinaryOperatorExpression(this.dupLoc(), instrLoc, e, op, rightOperand);
          break;
        default:
          this.popLoc();
          return e;
      }
    }
  }

  parseAdditiveExpression() {
    this.pushStart();
    let e = this.parseMultiplicativeExpression();
    for (;;) {
      switch (this.token) {
        case '+':
        case '-':
          this.pushStart();
          let op = this.token;
          this.next();
          let instrLoc = this.popLoc();
          let rightOperand = this.parseMultiplicativeExpression();
          e = new BinaryOperatorExpression(this.dupLoc(), instrLoc, e, op, rightOperand);
          break;
        default:
          this.popLoc();
          return e;
      }
    }
  }

  parseRelationalChain(): RelationalChain {
    let e = this.parseAdditiveExpression();
    switch (this.token) {
      case '==':
      case '!=':
      case '<':
      case '<=':
      case '>':
      case '>=': {
        this.pushStart();
        let op = this.token;
        this.next();
        let instrLoc = this.popLoc();
        let rhs = this.parseRelationalChain();
        return [instrLoc, e, op, rhs];
      }
      case 'not': {
        this.pushStart();
        this.next();
        const notInstrLoc = this.popLoc();
        if (this.token != 'in')
          this.parseError("'in' verwacht");
        this.pushStart();
        this.next();
        const inInstrLoc = this.popLoc();
        let rhs = this.parseAdditiveExpression();
        const loc = this.popLoc();
        return new UnaryOperatorExpression(loc, notInstrLoc, 'not', new BinaryOperatorExpression(loc, inInstrLoc, e, 'in', rhs));
      }
      case 'in': {
        this.pushStart();
        this.next();
        let instrLoc = this.popLoc();
        let rhs = this.parseAdditiveExpression();
        return new BinaryOperatorExpression(this.popLoc(), instrLoc, e, 'in', rhs);
      }
      default:
        return e;
    }
  }

  parseRelationalExpression() {
    function expandChain([instrLoc, e, op, rhs]: [Loc, Expression, string, RelationalChain]): Expression {
      if (rhs instanceof Array) {
        const conjuncts = expandChain(rhs);
        const e1 = rhs[1];
        const conjunct = new BinaryOperatorExpression(new Loc(e.loc.doc, e.loc.start, e1.loc.end), instrLoc, e, op, e1);
        const l = new Loc(e.loc.doc, e.loc.start, conjuncts.loc.end);
        return new BinaryOperatorExpression(l, l, conjunct, '&&', conjuncts);
      } else
        return new BinaryOperatorExpression(new Loc(e.loc.doc, e.loc.start, rhs.loc.end), instrLoc, e, op, rhs);
    }
    const chain = this.parseRelationalChain();
    if (chain instanceof Array)
      return expandChain(chain);
    else
      return chain;
  }

  parseConjunction(): Expression {
    this.pushStart();
    let e = this.parseRelationalExpression();
    if (this.token == 'and') {
      this.pushStart();
      this.next();
      let instrLoc = this.popLoc();
      let rhs = this.parseConjunction();
      return new BinaryOperatorExpression(this.popLoc(), instrLoc, e, '&&', rhs);
    } else {
      this.popLoc();
      return e;
    }
  }
  
  parseDisjunction(): Expression {
    this.pushStart();
    let e = this.parseConjunction();
    if (this.token == 'or') {
      this.pushStart();
      this.next();
      let instrLoc = this.popLoc();
      let rhs = this.parseDisjunction();
      return new BinaryOperatorExpression(this.popLoc(), instrLoc, e, '||', rhs);
    } else {
      this.popLoc();
      return e;
    }
  }
  
  parseAssignmentExpression(): Expression {
    this.pushStart();
    let e = this.parseDisjunction();
    switch (this.token) {
      case '=':
      case '+=':
      case '-=':
      case '*=':
      case '/=':
      case '%=':
      case '>>=':
      case '<<=':
      case '>>>=':
      case '|=':
      case '&=':
      case '^=':
        this.pushStart();
        let op = this.token;
        this.next();
        let instrLoc = this.popLoc();
        let rightOperand = this.parseExpression();
        return new AssignmentExpression(this.popLoc(), instrLoc, e, op, rightOperand);
      default:
        this.popLoc();
        return e;
    }
  }

  parseExpression() {
    return this.parseAssignmentExpression();
  }

  tryParsePrimaryType() {
    this.pushStart();
    switch (this.token) {
      case "int":
        this.next();
        return new LiteralTypeExpression(this.popLoc(), intType);
      case "boolean":
        this.next();
        return new LiteralTypeExpression(this.popLoc(), booleanType);
      case "void":
        this.next();
        return new LiteralTypeExpression(this.popLoc(), voidType);
      case "TYPE_IDENT":
        this.next();
        return new ClassTypeExpression(this.popLoc(), this.lastValue);
      case "byte":
      case "short":
      case "long":
      case "float":
      case "double":
      case "char":
        this.parseError("Type '" + this.token + "' wordt (nog) niet ondersteund; gebruik type 'int'.");
      default:
        this.popLoc();
        return null;
    }
  }
  
  tryParseType() {
    this.pushStart();
    let type: TypeExpression|null = this.tryParsePrimaryType();
    if (type == null) {
      this.popLoc();
      return null;
    }
    while (this.token == '[') {
      this.next();
      this.expect(']');
      type = new ArrayTypeExpression(this.dupLoc(), type);
    }
    this.popLoc();
    return type;
  }
  
  parseType() {
    let type = this.tryParseType();
    if (type == null)
      this.parseError("Type verwacht");
    return type;
  }

  parseSuite(): BlockStatement {
    this.pushStart();
    this.expect('REGELEINDE');
    this.expect('INDENT');
    let stmts = this.parseStatements({'DEDENT': true});
    this.expect('DEDENT');
    return new BlockStatement(this.popLoc(), stmts);
  }

  parseIfStatementTail(): Statement {
    this.pushStart();
    this.next();
    let instrLoc = this.popLoc();
    let condition = this.parseExpression();
    this.expect(':');
    let thenBody = this.parseSuite();
    let elseBody = null;
    switch (this.token) {
      case 'else':
        this.next();
        this.expect(':');
        elseBody = this.parseSuite();
        break;
      case 'elif':
        elseBody = this.parseIfStatementTail();
        break;
    }
    return new IfStatement(this.popLoc(), instrLoc, condition, thenBody, elseBody);
} 

  parseStatement() {
    this.pushStart();
    switch (this.token) {
      case 'while': {
        this.pushStart();
        this.next();
        let instrLoc = this.popLoc();
        let condition = this.parseExpression();
        this.expect(':');
        let body = this.parseSuite();
        return new WhileStatement(this.popLoc(), instrLoc, condition, body);
      }
      case 'return': {
        this.pushStart();
        this.next();
        let instrLoc = this.popLoc();
        let e;
        if (this.token == 'REGELEINDE')
          e = null;
        else
          e = this.parseExpression();
        this.expect('REGELEINDE');
        return new ReturnStatement(this.popLoc(), instrLoc, e);
      }
      case 'if': {
        return this.parseIfStatementTail();
      }
      case 'assert': {
        this.pushStart();
        this.next();
        let instrLoc = this.popLoc();
        let condition = this.parseExpression();
        const comment = this.expect('REGELEINDE');
        return new AssertStatement(this.popLoc(), instrLoc, condition, comment);
      }
      case 'pass': {
        this.pushStart();
        this.next();
        let instrLoc = this.popLoc();
        this.expect('REGELEINDE');
        return new PassStatement(this.popLoc(), instrLoc);
      }
    }
    let e = this.parseExpression();
    this.pushStart();
    this.expect('REGELEINDE');
    let instrLoc = this.popLoc();
    return new ExpressionStatement(this.popLoc(), instrLoc, e);
  }
  
  parseStatements(terminators: {[index: string]: boolean}) {
    let statements = [];
    while (!(this.token in terminators)) {
      let stmt = this.parseStatement();
      statements.push(stmt);
    }
    return statements;
  }
  
  parseModifiers() {
    switch (this.token) {
      case "public":
      case "protected":
      case "private":
      case "static":
      case "final":
        this.parseError("This modifier is not supported by JLearner");
    }
  }
  
  parseClassMemberDeclaration() {
    this.pushStart();
    this.parseModifiers();
    let type = this.parseType();
    if (this.token == '(' && type instanceof ClassTypeExpression)
      this.parseError("Constructors are not (yet) supported by JLearner. Instead, define a 'create' method outside the class.");
    let x = this.expect('NAAM');
    if (this.token == '(')
      this.parseError("Methods inside classes are not (yet) supported by JLearner. Instead, define the method outside the class.");
    if (this.token == '=')
      this.parseError("Field initializers are not (yet) supported by JLearner.");
    this.expect(';');
    return new FieldDeclaration(this.popLoc(), type, x);
  }
  
  parseDeclaration(): Declaration {
    this.pushStart();
    switch (this.token) {
      case 'class':
        this.next();
        let x = this.expect('TYPE_IDENT');
        this.expect('{');
        let fields = [];
        while (this.token != '}')
          fields.push(this.parseClassMemberDeclaration());
        this.expect('}');
        return new Class(this.popLoc(), x, fields);
      case 'def':
        this.next();
        this.pushStart();
        let name = this.expect('NAAM');
        let nameLoc = this.popLoc();
        this.expect('(');
        let parameters = [];
        if (this.token != ')') {
          for (;;) {
            this.pushStart();
            let paramType = new ImplicitTypeExpression();
            this.pushStart();
            let paramName = this.expect('NAAM');
            let paramNameLoc = this.popLoc();
            parameters.push(new ParameterDeclaration(this.popLoc(), paramType, paramNameLoc, paramName));
            if (this.token != ',')
              break;
            this.next();
          }
        }
        this.expect(')');
        this.expect(':');
        let body = this.parseSuite();
        let type = new ImplicitTypeExpression();
        return new MethodDeclaration(this.popLoc(), type, nameLoc, name, parameters, body.stmts);
      default:
        this.parseError("'class' of 'def' verwacht");
    }
  }
  
  parseDeclarations() {
    let declarations = [];
    while (this.token != 'EINDE')
      declarations.push(this.parseDeclaration());
    return declarations;
  }
}

function parseDeclarations(locFactory: LocFactory, text: string, parseComment: (comment: Comment_) => void) {
  const parser = new Parser(locFactory, text, false, parseComment);
  return parser.parseDeclarations();
}

function parseStatements(locFactory: LocFactory, text: string) {
  const parser = new Parser(locFactory, text);
  return parser.parseStatements({'EINDE': true});
}

function parseExpression(locFactory: LocFactory, text: string) {
  const parser = new Parser(locFactory, text, true);
  const result = parser.parseExpression();
  parser.expect('EINDE');
  return result;
}

let lastCheckedDeclarations: string|null = null;
let classes: {[index: string]: Class};
let toplevelMethods: {[index: string]: AbstractMethodDeclaration};
let lawComments: Comment_[];
let laws: {[index: string]: LawInfo};

function checkDeclarations(declarations: Declaration[]) {
  classes = {};
  toplevelMethods = {};
  //toplevelMethods['len'] = new BuiltInMethodDeclaration([new ParameterDeclaration(null as unknown as Loc, new LiteralTypeExpression(null as unknown as Loc, intType), 'l'], async (callExpr, args) => {
  //   let arg = args[0];
  //   if (!(arg instanceof ListObject))
  //     throw new LocError(callExpr.loc, "len expects a list object");
  //   return arg.length;
  // });
  for (let declaration of declarations) {
    if (declaration instanceof Class) {
      if (has(classes, declaration.name))
        throw new LocError(declaration.loc, "Er bestaat al een klasse met deze naam");
      classes[declaration.name] = declaration;
    } else {
      if (has(toplevelMethods, declaration.name))
        throw new LocError(declaration.loc, "Er bestaat al een methode met deze naam");
      toplevelMethods[declaration.name] = declaration as AbstractMethodDeclaration;
    }
  }
  for (let c in classes)
    classes[c].enter();
  for (let m in toplevelMethods)
    toplevelMethods[m].enter();
  for (let m in toplevelMethods)
    toplevelMethods[m].check();
}

let toplevelScope: Scope;
let mainStackFrame;
let callStack: any;

function resetMachine() {
  toplevelScope = new Scope(null);
  mainStackFrame = new StackFrame("(toplevel)", toplevelScope);
  callStack = [mainStackFrame];
}

resetMachine();

function push(binding: Binding) {
  callStack[callStack.length - 1].operands.push(binding);
}

function peek(N: number) {
  let operands = callStack[callStack.length - 1].operands;
  let result = operands.slice(operands.length - N, operands.length);
  return result.map((binding: Binding) => binding.value);
}

function pop(N: number) {
  let operands = callStack[callStack.length - 1].operands;
  let result = operands.slice(operands.length - N, operands.length);
  operands.length -= N;
  return result.map((binding: Binding) => binding.value);
}

class CallStackArrow {
  constructor(public arrow: SVGLineElement, public fromNode: HTMLElement, public toNode: HTMLElement) {}
}

let callStackArrows: CallStackArrow[] = []

function createArrow(fromNode: HTMLElement, toNode: HTMLElement) {
  let svg = document.getElementById('arrows-svg') as unknown as SVGSVGElement;
  let arrow = document.createElementNS('http://www.w3.org/2000/svg','line');
  svg.appendChild(arrow);
  let fromRect = fromNode.getClientRects()[0];
  let toRect = toNode.getClientRects()[0];
  let svgRect = svg.getClientRects()[0];
  let fromX = (fromRect.left + fromRect.right) / 2 - svgRect.left;
  let fromY = (fromRect.top + fromRect.bottom) / 2 - svgRect.top;
  arrow.x1.baseVal.value = fromX;
  arrow.y1.baseVal.value = fromY;

  let toLeft = toRect.left - svgRect.left;
  let toRight = toRect.right - svgRect.left;
  let toTop = toRect.top - svgRect.top;
  let toBottom = toRect.bottom - svgRect.top;

  let toX = fromX < toLeft ? toLeft : fromX < toRight ? fromX : toRight;
  let toY = fromY < toTop ? toTop : fromY < toBottom ? fromY : toBottom;

  if ((toX - fromX) * (toX - fromX) + (toY - fromY) * (toY - fromY) < 400) {
    toX = fromX < (toLeft + toRight) / 2 ? toRight : toLeft;
    toY = fromY < (toTop + toBottom) / 2 ? toBottom : toTop;
  }

  arrow.x2.baseVal.value = toX;
  arrow.y2.baseVal.value = toY;
  (arrow as any).style = "stroke:rgb(0,0,0);stroke-width:1";
  arrow.setAttribute('marker-end', "url(#arrowhead)");
  
  let maxX = Math.max(fromX, toX);
  if (svg.width.baseVal.value < maxX)
    svg.width.baseVal.newValueSpecifiedUnits(1, maxX);
  let maxY = Math.max(fromY, toY);
  if (svg.height.baseVal.value < maxY)
    svg.height.baseVal.newValueSpecifiedUnits(1, maxY);
  return arrow;
}

function updateStackArrows() {
  for (let arrow of callStackArrows) {
    arrow.arrow.parentNode!.removeChild(arrow.arrow);
    arrow.arrow = createArrow(arrow.fromNode, arrow.toNode);
  }
}

function updateArrows() {
  updateStackArrows();
  updateFieldArrows();
}

function updateCallStack() {
  for (let arrow of callStackArrows)
    arrow.arrow.parentNode!.removeChild(arrow.arrow);
  callStackArrows = [];
  
  let callStackTable = document.getElementById('callstack')!;
  while (callStackTable.firstChild != null)
    callStackTable.removeChild(callStackTable.firstChild);
  for (let stackFrame of callStack) {
    if (stackFrame !== callStack[0]) {
      let titleRow = document.createElement('tr');
      callStackTable.appendChild(titleRow);
      let titleTd = document.createElement('td');
      titleRow.appendChild(titleTd);
      titleTd.colSpan = 2;
      titleTd.className = "stackframe-title";
      titleTd.innerText = stackFrame.title;
    }
    for (let binding of stackFrame.allBindings()) {
      let row = document.createElement('tr');
      callStackTable.appendChild(row);
      let nameCell = document.createElement('td');
      row.appendChild(nameCell);
      nameCell.className = "stack-variable-name";
      nameCell.innerHTML = binding.getNameHTML();
      if (resumeFunc == null && (binding instanceof LocalBinding || binding instanceof SyntheticVariableBinding)) {
        let removeButton = document.createElement('button');
        removeButton.innerText = "Remove";
        removeButton.style.display = "none";
        removeButton.onclick = () => {
          let name = binding instanceof LocalBinding ? binding.declaration.name : binding.name;
          delete toplevelScope.bindings[name];
          updateMachineView();
        };
        nameCell.insertBefore(removeButton, nameCell.firstChild);
        nameCell.onmouseenter = () => {
          removeButton.style.display = "inline";
          setTimeout(updateArrows, 0);
        };
        nameCell.onmouseleave = () => {
          removeButton.style.display = "none";
          setTimeout(updateArrows, 0);
        };
      }
      let valueCell = document.createElement('td');
      row.appendChild(valueCell);
      valueCell.className = "stack-value-td";
      let valueDiv = document.createElement('div');
      valueCell.appendChild(valueDiv);
      valueDiv.className = "stack-value-div";
      if (binding.value instanceof JavaObject) {
        valueDiv.innerText = "()";
        valueDiv.style.color = "white";
        setTimeout(() => callStackArrows.push({arrow: createArrow(valueCell, binding.value.domNode), fromNode: valueCell, toNode: binding.value.domNode}), 0);
      } else
        valueDiv.innerText = binding.value == null ? "null" : binding.value;
    }
  }
}

function updateMachineView() {
  iterationCount = 0;
  collectGarbage();
  updateCallStack();
  updateFieldArrows();
  updateButtonStates();
}

let nbProofOutlinesChecked: number;

class LawInfo {
  constructor(public comment: Comment_, public name: string, public law: Law_) {}
}

function conjunctsOf(e: Expression): Expression[] {
  if (e instanceof BinaryOperatorExpression && e.operator == '&&')
    return conjunctsOf(e.leftOperand).concat(conjunctsOf(e.rightOperand));
  return [e];
}

function checkLaws() {
  laws = {};
  for (const comment of lawComments) {
    const text = comment.text;
    const wetIndex = text.indexOf('Wet');
    const colonIndex = text.indexOf(':', wetIndex + 3);
    if (colonIndex < 0)
      throw new LocError(comment.loc(), "Wet moet van de vorm 'Wet NAAM: PREMISSEN ==> CONCLUSIE' zijn");
    const name = text.slice(wetIndex + 3, colonIndex).trim();
    const implication = text.substring(colonIndex + 1);
    const arrowIndex = implication.indexOf('==>');
    const premisesPos = comment.start + colonIndex + 1;
    let premises: Expression[];
    let conclusionPos: number;
    let conclusionText;
    if (0 <= arrowIndex) {
      const premisesText = implication.slice(0, arrowIndex);
      premises = conjunctsOf(parseExpression((start, end) => comment.locFactory(premisesPos + start, premisesPos + end), premisesText));
      conclusionPos = premisesPos + arrowIndex + 3;
      conclusionText = implication.substring(arrowIndex + 3);
    } else {
      premises = [];
      conclusionPos = premisesPos;
      conclusionText = implication;
    }
    const conclusion = parseExpression((start, end) => comment.locFactory(conclusionPos + start, conclusionPos + end), conclusionText);
    const scope = new Scope(null, true);
    premises.forEach(e => e.checkAgainst(scope, booleanType));
    conclusion.checkAgainst(scope, booleanType);
    for (const x in scope.bindings) {
      // If the type is an unbound inferred type, bind to list type or int type, depending on whether used as operand of addition...
      const type = (scope.bindings[x].value as Type).unwrapInferredType();
      if (type instanceof InferredType) {
        if (type.isAddable_)
          type.isListType();
        else
          type.equals(intType);
      }
    }
    const premisesParsed = premises.map(parseProofOutlineExpression).reduceRight((acc, t) => TermsCons(t, acc), TermsNil);
    laws[name] = new LawInfo(comment, name, Law(premisesParsed, parseProofOutlineExpression(conclusion)));
  }
}

function checkProofOutlines() {
  handleError(async () => {
    parseDeclarationsBox();
    checkLaws();
    nbProofOutlinesChecked = 0;
    for (let m in toplevelMethods)
      toplevelMethods[m].checkProofOutlines();
    alert(`${nbProofOutlinesChecked} bewijssilhouetten met succes gecontroleerd!`);
  });
}

declare var statementsEditor: any;

async function executeStatements(step: boolean) {
  await handleError(async () => {
    parseDeclarationsBox();
    let stmtsText = statementsEditor.getValue();
    let stmts = parseStatements(mkLocFactory(statementsEditor), stmtsText);
    let typeScope = new Scope(toplevelScope); // The type bindings should not be present when executing
    //for (let stmt of stmts)
    //  stmt.check(typeScope);
    currentBreakCondition = () => step;
    for (let stmt of stmts) {
      if (await stmt.execute(toplevelScope) !== undefined)
        break;
    }
  });
  updateMachineView();
}

function resetAndExecute() {
  reset();
  executeStatements(false);
}

function getTextCoordsFromOffset(text: string, offset: number) {
  let line = 0;
  let lineStart = 0;
  for (;;) {
    let nextBreak = text.indexOf('\n', lineStart);
    if (nextBreak < 0 || offset < nextBreak)
      return {line, ch: offset - lineStart};
    line++;
    lineStart = nextBreak + 1;
  }
}

let errorWidgets: {clear(): void}[] = [];

function clearErrorWidgets() {
  for (let widget of errorWidgets)
    widget.clear();
  errorWidgets = [];
}

function addErrorWidget(editor: any, line: number, msg: string) {
  var widget = document.createElement("div");
  var icon = widget.appendChild(document.createElement("span"));
  icon.innerHTML = "!";
  icon.className = "lint-error-icon";
  widget.appendChild(document.createTextNode(msg));
  widget.className = "lint-error";
  errorWidgets.push(editor.addLineWidget(line, widget, {coverGutter: false, noHScroll: true}));
}

async function handleError(body: () => Promise<void>) {
  clearErrorWidgets();
  try {
    await body();
  } catch (ex) {
    if (ex instanceof LocError) {
      let editor = ex.loc.doc;
      let text = editor.getValue();
      let start = getTextCoordsFromOffset(text, ex.loc.start);
      let end = getTextCoordsFromOffset(text, ex.loc.end);
      if (ex.loc.start == text.length) { // error at EOF
        if (!(text.length >= 2 && text.charAt(text.length - 1) == ' ' && text.charAt(text.length - 2) == ' ')) {
          if (text.charAt(text.length - 1) == ' ')
            editor.replaceRange(' ', start);
          else {
            editor.replaceRange('  ', start);
            start.ch++;
          }
        } else {
          start.ch--;
        }
        errorWidgets.push(editor.markText(start, {line: editor.lastLine()}, {className: "syntax-error"}));
        addErrorWidget(editor, editor.lastLine(), ex.msg);
    } else {
        errorWidgets.push(editor.markText(start, end, {className: "syntax-error"}));
        addErrorWidget(editor, start.line, ex.msg);
        editor.scrollIntoView({from: start, to: end}, 50);
      }
    } else {
      alert(ex);
    }
  }
}

function processComment(comment: Comment_) {
  if (comment.isOnNewLine && comment.text.trim().startsWith('Wet '))
    lawComments.push(comment);
}

declare var declarationsEditor: any;

function parseDeclarationsBox() {
  let text = declarationsEditor.getValue();
  if (lastCheckedDeclarations != null && lastCheckedDeclarations == text)
    return;
  lastCheckedDeclarations = null;
  resetMachine();
  updateMachineView();
  lawComments = [];
  let decls = parseDeclarations(mkLocFactory(declarationsEditor), text, processComment);
  checkDeclarations(decls);
  lastCheckedDeclarations = text;
}

type Pos = {line: number, ch: number};
type CMRange = {from: Pos, to: Pos};

let justificationLines: {[index: number]: {commentStart: number, antecedentConjunctRanges: CMRange[]}} = {};

function harvestJustificationLines(text: string, stmts: Statement[]) {
  for (let i = 0; i < stmts.length; i++) {
    const stmt = stmts[i];
    const prevStmt = i == 0 ? null : stmts[i - 1];
    if (stmt instanceof AssertStatement && stmt.comment && prevStmt instanceof AssertStatement) {
      const loc = stmt.comment.loc();
      const start = getTextCoordsFromOffset(text, loc.start);
      const antecedentConjuncts = conjunctsOf(prevStmt.condition);
      justificationLines[start.line] = {
        commentStart: start.ch,
        antecedentConjunctRanges: antecedentConjuncts.map(c => ({
          from: getTextCoordsFromOffset(text, c.loc.start),
          to: getTextCoordsFromOffset(text, c.loc.end)
        }))
      };
    } else if (stmt instanceof IfStatement) {
      if (stmt.thenBody instanceof BlockStatement)
        harvestJustificationLines(text, stmt.thenBody.stmts);
      if (stmt.elseBody instanceof BlockStatement)
        harvestJustificationLines(text, stmt.elseBody.stmts);
    } else if (stmt instanceof WhileStatement)
      if (stmt.body instanceof BlockStatement)
        harvestJustificationLines(text, stmt.body.stmts);
  }
}

function declarationsBoxChanged() {
  justificationLines = {};

  try {
    let text = declarationsEditor.getValue();
    let decls = parseDeclarations(mkLocFactory(declarationsEditor), text, () => {});
    for (const decl of decls) {
      if (decl instanceof MethodDeclaration) {
        let proofOutlineStart = null;
        for (let i = 0; i < decl.bodyBlock.length; i++) {
          const stmt = decl.bodyBlock[i];
          if (stmt instanceof AssertStatement) {
            if (proofOutlineStart == null && stmt.comment && (stmt.comment.text.includes('PRECONDITION') || stmt.comment.text.includes('PRECONDITIE')))
              proofOutlineStart = i;
            else if (proofOutlineStart != null && stmt.comment && (stmt.comment.text.includes('POSTCONDITION') || stmt.comment.text.includes('POSTCONDITIE'))) {
              harvestJustificationLines(text, decl.bodyBlock.slice(proofOutlineStart, i + 1));
              proofOutlineStart = null;
            }
          }
        }
        if (proofOutlineStart != null)
          harvestJustificationLines(text, decl.bodyBlock.slice(proofOutlineStart));
      }
    }
  } catch (e) {}
}

const antecedentConjunctMarks: {clear(): void}[] = [];

function declarationsBoxCursorMoved() {
  for (const mark of antecedentConjunctMarks)
    mark.clear();
  antecedentConjunctMarks.length = 0;

  const {line, ch} = declarationsEditor.getCursor();
  const info = justificationLines[line];
  if (info && info.commentStart <= ch) {
    for (let i = 0; i < info.antecedentConjunctRanges.length && i < 20; i++) {
      const {from, to} = info.antecedentConjunctRanges[i];
      const element = document.createElement('span');
      element.appendChild(document.createTextNode(String.fromCharCode(0x2460 + i)));
      antecedentConjunctMarks.push(declarationsEditor.markText(from, to, {className: 'antecedent-conjunct', startStyle: 'antecedent-conjunct-start-' + (i + 1)}));
    }
  }
}

class SyntheticVariableBinding extends Binding {
  constructor(public name: string, public value: Value) {
    super(value);
  }

  getNameHTML() {
    return this.name;
  }
}

let syntheticVariableCount = 0;

declare var expressionEditor: any;
declare var resultsEditor: any;

async function evaluateExpression(step: boolean) {
  await handleError(async () => {
    parseDeclarationsBox();
    let exprText = expressionEditor.getValue();
    let e = parseExpression(mkLocFactory(expressionEditor), exprText);
    e.check_(toplevelScope);
    currentBreakCondition = () => step;
    await e.evaluate(toplevelScope);
    let [v] = pop(1);
    let valueText;
    if (e.type!.unwrapInferredType() instanceof ReferenceType) {
      let varName = '$' + ++syntheticVariableCount;
      toplevelScope.bindings[varName] = new SyntheticVariableBinding(varName, v);
      valueText = varName;
    } else {
      valueText = "" + v;
    }
    resultsEditor.replaceRange(exprText, {line: resultsEditor.lastLine()});
    let resultsText = resultsEditor.getValue();
    let {line, ch} = getTextCoordsFromOffset(resultsText, resultsText.length);
    let text = " ==> " + valueText + "\r\n";
    resultsEditor.replaceRange(text, {line});
    resultsEditor.markText({line, ch}, {line}, {className: 'result', inclusiveRight: false});
    resultsEditor.scrollIntoView({line});
  });
  updateMachineView();
}

function markLoc(loc: Loc, className: string) {
  let text = loc.doc.getValue();
  return loc.doc.markText(getTextCoordsFromOffset(text, loc.start), getTextCoordsFromOffset(text, loc.end), {className});
}

let currentNode: ASTNode|null = null;
let currentBreakCondition: ((node: ASTNode) => boolean)|null = null;
let currentInstructionMark: {clear(): void}|null = null;
let resumeFunc: (() => void)|null = null;

function checkBreakpoint(node: ASTNode) {
  return new Promise<void>((resolve, reject) => {
    if (currentBreakCondition!(node)) {
      currentNode = node;
      currentBreakCondition = null;
      currentInstructionMark = markLoc(node.instrLoc!, "current-instruction");
      resumeFunc = () => {
        currentNode = null;
        currentInstructionMark!.clear();
        resolve();
      };
      updateMachineView();
    } else {
      resolve();
    }
  });
}

function resume() {
  let f = resumeFunc!;
  resumeFunc = null;
  f();
}

function isDifferentLine(loc1: Loc, loc2: Loc) {
  if (loc1.doc != loc2.doc)
    return true;
  let text = loc1.doc.getValue();
  let coords1 = getTextCoordsFromOffset(text, loc1.start);
  let coords2 = getTextCoordsFromOffset(text, loc2.start);
  return coords1.line != coords2.line;
}

function step() {
  let oldNode = currentNode!;
  let oldStackSize = callStack.length;
  let oldStackFrame = callStack[oldStackSize - 1];
  currentBreakCondition = node => {
    if (callStack.length != oldStackSize || callStack[oldStackSize - 1] !== oldStackFrame)
      return true;
    return isDifferentLine(node.loc, oldNode.loc);
  };
  resume();
}

function smallStep() {
  currentBreakCondition = node => true;
  resume();
}

function stepOver() {
  let oldNode = currentNode!;
  let oldStackSize = callStack.length;
  let oldStackFrame = callStack[oldStackSize - 1];
  currentBreakCondition = node => {
    if (callStack.length < oldStackSize || callStack[oldStackSize - 1] !== oldStackFrame)
      return true;
    if (callStack.length > oldStackSize)
      return false;
    return isDifferentLine(node.loc, oldNode.loc);
  };
  resume();
}

function stepOut() {
  let oldStackSize = callStack.length;
  let oldStackFrame = callStack[oldStackSize - 1];
  currentBreakCondition = node => {
    return callStack.length < oldStackSize || callStack[oldStackSize - 1] !== oldStackFrame;
  };
  resume();
}

function continue_() {
  currentBreakCondition = node => false;
  resume();
}

function reset() {
  currentNode = null;
  if (currentInstructionMark != null) {
    currentInstructionMark.clear();
    currentInstructionMark = null;
  }
  resumeFunc = null;

  resetMachine();
  updateMachineView();
}

function updateButtonStates() {
  let stepping = resumeFunc != null;
  (document.getElementById('executeButton') as HTMLButtonElement).disabled = stepping;
  (document.getElementById('resetAndExecuteButton') as HTMLButtonElement).disabled = stepping;
  (document.getElementById('stepThroughStatementsButton') as HTMLButtonElement).disabled = stepping;
  (document.getElementById('evaluateButton') as HTMLButtonElement).disabled = stepping;
  (document.getElementById('stepThroughExpressionButton') as HTMLButtonElement).disabled = stepping;

  (document.getElementById('stepButton') as HTMLButtonElement).disabled = !stepping;
  (document.getElementById('smallStepButton') as HTMLButtonElement).disabled = !stepping;
  (document.getElementById('stepOverButton') as HTMLButtonElement).disabled = !stepping;
  (document.getElementById('stepOutButton') as HTMLButtonElement).disabled = !stepping;
  (document.getElementById('continueButton') as HTMLButtonElement).disabled = !stepping;
}

type Example = {title: string, declarations: string, statements: string, expression: string};

const examples: Example[] = [{
  title: 'Kopieer een getal (partiële correctheid)',
  declarations:
`def copy(n):

    # Het programma hieronder kopieert het gegeven getal n in variabele r.
    # Voorzie het van een gepaste preconditie en postconditie en
    # bewijs de partiële correctheid.

    i = n
    r = 0
    while i != 0:
        i = i - 1
        r = r + 1

    return r
`,
  statements:
`assert copy(2) == 2
assert copy(7) == 7`,
  expression: `copy(3)`
}, {
  title: 'Kopieer een getal (partiële correctheid) (oplossing)',
  declarations:
`def copy(n):

    assert True # PRECONDITIE PARTIËLE CORRECTHEID
    assert 0 == n - n # Z
    i = n
    assert 0 == n - i
    r = 0
    assert r == n - i
    while i != 0:
        assert r == n - i and i != 0
        assert r + 1 == n - (i - 1) # Z op 1
        i = i - 1
        assert r + 1 == n - i
        r = r + 1
        assert r == n - i
    assert r == n - i and not i != 0
    assert r == n - i and i == 0 # Z op 2
    assert r == n - 0 # Herschrijven met 2 in 1
    assert r == n # Z op 1 # POSTCONDITIE

    return r
`,
  statements:
`assert copy(2) == 2
assert copy(7) == 7`,
  expression: `copy(3)`
}, {
  title: 'Kopieer een getal (alternatief)',
  declarations:
`# Wet LeAntisym: x <= y <= x ==> x == y

def copy(n):

    # Het programma hieronder kopieert de gegeven waarde n in de variabele r.
    # Voorzie het van een gepaste preconditie en postconditie
    # en bewijs de correctheid.

    i = n
    r = 0
    while 0 < i:
        i = i - 1
        r = r + 1

    return r
`,
  statements:
`assert copy(2) == 2
assert copy(7) == 7`,
  expression: `copy(3)`
}, {
  title: 'Kopieer een getal (alternatief) (oplossing) (partiële correctheid)',
  declarations:
`# Wet LeAntisym: x <= y <= x ==> x == y

def copy(n):

    assert 0 <= n # PRECONDITIE PARTIËLE CORRECTHEID
    assert 0 <= n and 0 == n - n # Z
    i = n
    assert 0 <= i and 0 == n - i
    r = 0
    assert 0 <= i and r == n - i
    while 0 < i:
        assert 0 <= i and r == n - i and 0 < i
        assert 0 <= i - 1 and r + 1 == n - (i - 1) # Z op 3 of Z op 2
        i = i - 1
        assert 0 <= i and r + 1 == n - i
        r = r + 1
        assert 0 <= i and r == n - i
    assert 0 <= i and r == n - i and not 0 < i
    assert 0 <= i and r == n - i and i <= 0 # Z op 3
    assert r == n - i and i == 0 # LeAntisym op 3 en 1
    assert r == n - 0 # Herschrijven met 2 in 1
    assert r == n # Z op 1 # POSTCONDITIE

    return r
`,
  statements:
`assert copy(2) == 2
assert copy(7) == 7`,
  expression: `copy(3)`
}, {
  title: 'Kopieer een getal (oplossing) (totale correctheid)',
  declarations:
`# Wet LeAntisym: x <= y and y <= x ==> x == y

def copy(n):

    assert 0 <= n # PRECONDITIE
    assert 0 <= n and 0 == n - n # Z
    i = n
    assert 0 <= i and 0 == n - i
    r = 0
    assert 0 <= i and r == n - i
    while 0 < i:
        oude_variant = i
        assert 0 <= i and r == n - i and 0 < i and i == oude_variant
        assert 0 < i and r + 1 == n - (i - 1) and i == oude_variant # Z op 2
        assert r + 1 == n - (i - 1) and 0 <= i - 1 < oude_variant # Z op 1 of Z op 3
        i = i - 1
        assert r + 1 == n - i and 0 <= i < oude_variant
        r = r + 1
        assert r == n - i and 0 <= i < oude_variant
        assert 0 <= i and r == n - i and 0 <= i < oude_variant
    assert 0 <= i and r == n - i and not 0 < i
    assert 0 <= i and r == n - i and i <= 0 # Z op 3
    assert r == n - i and 0 == i # LeAntisym op 1 en 3
    assert r == n - 0 # Herschrijven met 2 in 1
    assert r == n # Z op 1 # POSTCONDITIE

    return r
`,
  statements:
`assert copy(2) == 2
assert copy(7) == 7`,
  expression: `copy(3)`
}, {
  title: 'Minimum van drie getallen',
  declarations:
`# Wet LeTrans: x <= y <= z ==> x <= z

def min(x, y, z):

    # Het programma hieronder berekent in result het minimum van de getallen
    # x, y en z. Voorzie het van een gepaste preconditie en postconditie
    # en bewijs de correctheid.
    # Let op: het volstaat hier dat je bewijst dat het resultaat niet groter
    # is dan de invoerwaarden. Om een sterker resultaat te bewijzen, heb je
    # een hulpfunctie nodig; zie daarvoor de volgende oefening.

    if x <= y:
        if x <= z:
            result = x
        else:
            result = z
    else:
        if y <= z:
            result = y
        else:
            result = z

    return result
`,
  statements:
`assert min(1, 2, 3) == 1
assert min(1, 3, 2) == 1
assert min(2, 1, 3) == 1
assert min(2, 3, 1) == 1
assert min(3, 1, 2) == 1
assert min(3, 2, 1) == 1`,
  expression: `min(30, 20, 10)`
}, {
  title: 'Minimum van drie getallen (oplossing met zwakke postconditie)',
  declarations:
`# Wet LeTrans: x <= y <= z ==> x <= z

def min(x, y, z):

    assert True # PRECONDITIE

    if x <= y:
        assert True and x <= y
        if x <= z:
            assert True and x <= y and x <= z
            assert x <= x and x <= y and x <= z # Z
            result = x
            assert result <= x and result <= y and result <= z
        else:
            assert True and x <= y and not x <= z
            assert z <= x and x <= y # Z op 3
            assert z <= x and z <= y and z <= z # LeTrans op 1 en 2 of Z
            result = z
            assert result <= x and result <= y and result <= z
        assert result <= x and result <= y and result <= z
    else:
        assert True and not x <= y
        if y <= z:
            assert True and not x <= y and y <= z
            assert y <= x and y <= y and y <= z # Z op 2 of Z
            result = y
            assert result <= x and result <= y and result <= z
        else:
            assert True and not x <= y and not y <= z
            assert y <= x and z <= y # Z op 2 of Z op 3
            assert z <= x and z <= y and z <= z # LeTrans op 2 en 1 of Z
            result = z
            assert result <= x and result <= y and result <= z
        assert result <= x and result <= y and result <= z

    assert result <= x and result <= y and result <= z # POSTCONDITIE

    return result
`,
  statements:
`assert min(1, 2, 3) == 1
assert min(1, 3, 2) == 1
assert min(2, 1, 3) == 1
assert min(2, 3, 1) == 1
assert min(3, 1, 2) == 1
assert min(3, 2, 1) == 1`,
  expression: `min(30, 20, 10)`
}, {
  title: 'Minimum van drie getallen (met min-functie)',
  declarations:
`def min(x, y, z):
    if x <= y and x <= z:
        return x
    elif y <= x and y <= z:
        return y
    elif z <= x and z <= y:
        return z

# Wet min3_1: x <= y and x <= z ==> min(x, y, z) == x
# Wet min3_2: y <= x and y <= z ==> min(x, y, z) == y
# Wet min3_3: z <= x and z <= y ==> min(x, y, z) == z
# Wet LeTrans: x <= y and y <= z ==> x <= z

def my_min(x, y, z):

    # Het programma hieronder berekent in result het minimum van
    # de drie gegeven getallen x, y en z.
    # Voorzie het van een gepaste preconditie en
    # postconditie en bewijs de correctheid.
    # Je mag in je toestandsbeweringen gebruik maken
    # van de bovenstaande functie 'min'.

    if x <= y:
        if x <= z:
            result = x
        else:
            result = z
    else:
        if y <= z:
            result = y
        else:
            result = z

    return result
`,
  statements:
`assert my_min(1, 2, 3) == 1
assert my_min(1, 3, 2) == 1
assert my_min(2, 1, 3) == 1
assert my_min(2, 3, 1) == 1
assert my_min(3, 1, 2) == 1
assert my_min(3, 2, 1) == 1`,
  expression: `my_min(30, 20, 10)`
}, {
  title: 'Minimum van drie getallen (met min-functie) (oplossing)',
  declarations:
`def min(x, y, z):
    if x <= y and x <= z:
        return x
    elif y <= x and y <= z:
        return y
    elif z <= x and z <= y:
        return z

# Wet min3_1: x <= y and x <= z ==> min(x, y, z) == x
# Wet min3_2: y <= x and y <= z ==> min(x, y, z) == y
# Wet min3_3: z <= x and z <= y ==> min(x, y, z) == z
# Wet LeTrans: x <= y and y <= z ==> x <= z

def my_min(x, y, z):

    assert True # PRECONDITIE

    if x <= y:
        assert True and x <= y
        if x <= z:
            assert True and x <= y and x <= z
            assert x == min(x, y, z) # min3_1 op 2 en 3
            result = x
            assert result == min(x, y, z)
        else:
            assert True and x <= y and not x <= z
            assert z <= x and x <= y # Z op 3
            assert z <= x and z <= y # LeTrans op 1 en 2
            assert z == min(x, y, z) # min3_3 op 1 en 2
            result = z
            assert result == min(x, y, z)
        assert result == min(x, y, z)
    else:
        assert True and not x <= y
        if y <= z:
            assert True and not x <= y and y <= z
            assert y <= x and y <= z # Z op 2
            assert y == min(x, y, z) # min3_2 op 1 en 2
            result = y
            assert result == min(x, y, z)
        else:
            assert True and not x <= y and not y <= z
            assert y <= x and z <= y # Z op 2 of Z op 3
            assert z <= x and z <= y # LeTrans op 2 en 1
            assert z == min(x, y, z) # min3_3 op 1 en 2
            result = z
            assert result == min(x, y, z)
        assert result == min(x, y, z)

    assert result == min(x, y, z) # POSTCONDITIE

    return result
`,
  statements:
`assert my_min(1, 2, 3) == 1
assert my_min(1, 3, 2) == 1
assert my_min(2, 1, 3) == 1
assert my_min(2, 3, 1) == 1
assert my_min(3, 1, 2) == 1
assert my_min(3, 2, 1) == 1`,
  expression: `my_min(30, 20, 10)`
}, {
  title: 'Lijst vol eenen',
  declarations:
`def repeat(n, xs):
    if n == 0:
        return []
    else:
        return repeat(n - 1, xs) + xs

# Wet LeAntisym: x <= y <= x ==> x == y
# Wet RepeatZero: repeat(0, xs) == []
# Wet RepeatPlusOne: 0 <= n ==> repeat(n + 1, xs) == repeat(n, xs) + xs

def ones(n):

    # Examen MI 4/6/21

    # Het programma hieronder bouwt in res een lijst bestaande uit
    # n voorkomens van het getal één.
    # Voorzie het van een gepaste preconditie en postconditie
    # en bewijs de correctheid.
    # Je mag in je toestandsbeweringen gebruik maken van de
    # bovenstaande functie 'repeat', die de aaneenschakeling
    # van n exemplaren van de lijst xs teruggeeft.

    i = n
    res = []
    while 0 < i:
        res = res + [1]
        i = i - 1

    return res
`,
  statements:
`assert ones(2) == [1, 1]
assert ones(3) == [1, 1, 1]`,
  expression: `ones(4)`
}, {
  title: 'Lijst vol eenen (oplossing) (partiële correctheid)',
  declarations:
`def repeat(n, xs):
    if n == 0:
        return []
    else:
        return repeat(n - 1, xs) + xs

# Wet LeAntisym: x <= y <= x ==> x == y
# Wet RepeatZero: repeat(0, xs) == []
# Wet RepeatPlusOne: 0 <= n ==> repeat(n + 1, xs) == repeat(n, xs) + xs

def ones(n):

    assert 0 <= n # PRECONDITIE PARTIËLE CORRECTHEID

    assert 0 <= n <= n and [] == repeat(0, [1]) and n - n == 0 # Z of RepeatZero
    assert 0 <= n <= n and [] == repeat(n - n, [1]) # Herschrijven met 4 in 3
    i = n
    assert 0 <= i <= n and [] == repeat(n - i, [1])
    res = []
    assert 0 <= i <= n and res == repeat(n - i, [1])
    while 0 < i:
        assert 0 <= i <= n and res == repeat(n - i, [1]) and 0 < i
        assert 0 <= i <= n and res == repeat(n - i, [1]) and 0 < i and res + [1] == res + [1]
        assert 0 <= i - 1 <= n and res + [1] == repeat(n - i, [1]) + [1] and 0 <= n - i # Z op 4 of Z op 2 of Herschrijven met 3 in 5
        assert 0 <= i - 1 <= n and res + [1] == repeat(n - i + 1, [1]) and n - i + 1 == n - (i - 1) # Herschrijven met RepeatPlusOne op 4 in 3 of Z
        assert 0 <= i - 1 <= n and res + [1] == repeat(n - (i - 1), [1]) # Herschrijven met 4 in 3
        res = res + [1]
        assert 0 <= i - 1 <= n and res == repeat(n - (i - 1), [1])
        i = i - 1
        assert 0 <= i <= n and res == repeat(n - i, [1])
    assert 0 <= i <= n and res == repeat(n - i, [1]) and not 0 < i
    assert 0 <= i <= n and res == repeat(n - i, [1]) and i <= 0 # Z op 4
    assert 0 == i and res == repeat(n - i, [1]) # LeAntisym op 1 en 4
    assert res == repeat(n - 0, [1]) and n - 0 == n # Herschrijven met 1 in 2 of Z

    assert res == repeat(n, [1]) # Herschrijven met 2 in 1 # POSTCONDITIE

    return res
`,
  statements:
`assert ones(2) == [1, 1]
assert ones(3) == [1, 1, 1]`,
  expression: `ones(4)`
}, {
  title: 'Lengte van een lijst',
  declarations:
`# Wet LenNonneg: 0 <= len(xs)
# Wet LenEmpty: len([]) == 0
# Wet LenNonempty: xs != [] ==> len(xs) == 1 + len(xs[:-1])

# Examen MI 18/6/21

def length(xs):

    # Het programma hieronder berekent in res de lengte van de gegeven
    # niet-lege lijst xs.
    # Voorzie het van een gepaste preconditie en postconditie
    # en bewijs de correctheid.

    todo = xs[:-1]
    res = 1
    while todo != []:
        res = res + 1
        todo = todo[:-1]

    return res`,
  statements:
`assert length([1, 2, 3]) == 3
assert length([4, 3, 2, 1]) == 4`,
  expression: `length([10])`
}, {
  title: 'Lengte van een lijst (oplossing) (partiële correctheid)',
  declarations:
`# Wet LenNonneg: 0 <= len(xs)
# Wet LenEmpty: len([]) == 0
# Wet LenNonempty: xs != [] ==> len(xs) == 1 + len(xs[:-1])

def length(xs):

    assert xs != [] # PRECONDITIE PARTIËLE CORRECTHEID
    assert len(xs) == 1 + len(xs[:-1]) # LenNonempty op 1
    todo = xs[:-1]
    assert len(xs) == 1 + len(todo)
    res = 1
    assert len(xs) == res + len(todo) # LUSINVARIANT
    while todo != []:
        assert len(xs) == res + len(todo) and todo != []
        assert len(xs) == res + (1 + len(todo[:-1])) # Herschrijven met LenNonempty op 2 in 1
        assert len(xs) == (res + 1) + len(todo[:-1]) # Z op 1
        res = res + 1
        assert len(xs) == res + len(todo[:-1])
        todo = todo[:-1]
        assert len(xs) == res + len(todo)
    assert len(xs) == res + len(todo) and not todo != []
    assert len(xs) == res + len(todo) and todo == []
    assert len(xs) == res + len([]) # Herschrijven met 2 in 1
    assert len(xs) == res + 0 # Herschrijven met LenEmpty in 1
    assert res == len(xs) # Z op 1 # POSTCONDITIE

    return res`,
  statements:
`assert length([1, 2, 3]) == 3
assert length([4, 3, 2, 1]) == 4`,
  expression: `length([10])`
}, {
  title: 'Aaneenschakeling',
  declarations:
`# Wet Nonempty: xs != [] ==> xs == xs[:1] + xs[1:]
# Wet ConcatAssoc: xs + (ys + zs) == (xs + ys) + zs
# Wet ConcatEmpty: xs + [] == xs

# Examen MI 11/8/21

def concat(xs, ys):

    # Het programma hieronder berekent in variabele 'result' de aaneenschakeling
    # van de gegeven lijst 'xs' en de gegeven niet-lege lijst 'ys'.
    # Voorzie het van een gepaste preconditie en postconditie
    # en bewijs de correctheid.

    result = xs + ys[:1]
    todo = ys[1:]
    while todo != []:
        result = result + todo[:1]
        todo = todo[1:]

    return result`,
  statements:
`assert concat([1, 2, 3], [4, 5]) == [1, 2, 3, 4, 5]
assert concat([], [10]) == [10]`,
  expression: `concat([100, 200], [300, 400])`
}, {
  title: 'Aaneenschakeling (oplossing, partiële correctheid)',
  declarations:
`# Wet Nonempty: xs != [] ==> xs == xs[:1] + xs[1:]
# Wet ConcatAssoc: xs + (ys + zs) == (xs + ys) + zs
# Wet ConcatEmpty: xs + [] == xs

def concat(xs, ys):

    assert ys != [] # PRECONDITIE PARTIËLE CORRECTHEID
    assert ys != [] and xs + ys == xs + ys
    assert xs + (ys[:1] + ys[1:]) == xs + ys # Herschrijven met Nonempty op 1 in 2
    assert (xs + ys[:1]) + ys[1:] == xs + ys # Herschrijven met ConcatAssoc in 1
    result = xs + ys[:1]
    assert result + ys[1:] == xs + ys
    todo = ys[1:]
    assert result + todo == xs + ys # LUSINVARIANT
    while todo != []:
        assert result + todo == xs + ys and todo != []
        assert result + (todo[:1] + todo[1:]) == xs + ys # Herschrijven met Nonempty op 2 in 1
        assert (result + todo[:1]) + todo[1:] == xs + ys # Herschrijven met ConcatAssoc in 1
        result = result + todo[:1]
        assert result + todo[1:] == xs + ys
        todo = todo[1:]
        assert result + todo == xs + ys
    assert result + todo == xs + ys and not todo != []
    assert result + todo == xs + ys and todo == []
    assert result + [] == xs + ys # Herschrijven met 2 in 1
    assert result == xs + ys # Herschrijven met ConcatEmpty in 1 # POSTCONDITIE

    return result`,
  statements:
`assert concat([1, 2, 3], [4, 5]) == [1, 2, 3, 4, 5]
assert concat([], [10]) == [10]`,
  expression: `concat([100, 200], [300, 400])`
}, {
  title: 'Aaneenschakeling (oplossing, totale correctheid)',
  declarations:
`# Wet Nonempty: xs != [] ==> xs == xs[:1] + xs[1:]
# Wet ConcatAssoc: xs + (ys + zs) == (xs + ys) + zs
# Wet ConcatEmpty: xs + [] == xs
# Wet LenNonneg: 0 <= len(xs)
# Wet LenSlice: xs != [] ==> len(xs[1:]) < len(xs)

def concat(xs, ys):

    assert ys != [] # PRECONDITIE
    assert ys != [] and xs + ys == xs + ys
    assert xs + (ys[:1] + ys[1:]) == xs + ys # Herschrijven met Nonempty op 1 in 2
    assert (xs + ys[:1]) + ys[1:] == xs + ys # Herschrijven met ConcatAssoc in 1
    result = xs + ys[:1]
    assert result + ys[1:] == xs + ys
    todo = ys[1:]
    assert result + todo == xs + ys # LUSINVARIANT
    while todo != []:
        oude_variant = len(todo)
        assert result + todo == xs + ys and todo != [] and len(todo) == oude_variant
        assert result + (todo[:1] + todo[1:]) == xs + ys and len(todo[1:]) < len(todo) == oude_variant # Herschrijven met Nonempty op 2 in 1 of LenSlice op 2
        assert (
          (result + todo[:1]) + todo[1:] == xs + ys
          and 0 <= len(todo[1:]) < oude_variant
        ) # Herschrijven met ConcatAssoc in 1 of LenNonneg of Herschrijven met 3 in 2
        result = result + todo[:1]
        assert result + todo[1:] == xs + ys and 0 <= len(todo[1:]) < oude_variant
        todo = todo[1:]
        assert result + todo == xs + ys and 0 <= len(todo) < oude_variant
    assert result + todo == xs + ys and not todo != []
    assert result + todo == xs + ys and todo == []
    assert result + [] == xs + ys # Herschrijven met 2 in 1
    assert result == xs + ys # Herschrijven met ConcatEmpty in 1 # POSTCONDITIE

    return result`,
  statements:
`assert concat([1, 2, 3], [4, 5]) == [1, 2, 3, 4, 5]
assert concat([], [10]) == [10]`,
  expression: `concat([100, 200], [300, 400])`
}, {
  title: 'Aantal nullen',
  declarations:
`def nb_zeros(xs):
    if xs == []:
        return 0
    elif xs[0] == 0:
        return 1 + nb_zeros(xs[1:])
    else:
        return 0 + nb_zeros(xs[1:])

# Wet LeAntisym: a <= b <= a ==> a == b
# Wet LenNonnegative: 0 <= len(xs)
# Wet SliceFull: xs[:] == xs
# Wet NbZerosEmpty: nb_zeros(xs[i:i]) == 0
# Wet NbZerosZero: 0 <= i and i < len(xs) and xs[i] == 0 ==> nb_zeros(xs[:i + 1]) == nb_zeros(xs[:i]) + 1
# Wet NbZerosNonzero: 0 <= i and i < len(xs) and xs[i] != 0 ==> nb_zeros(xs[:i + 1]) == nb_zeros(xs[:i])

def number_of_zeros(xs):

    # Het programma hieronder berekent in n het aantal nullen in de gegeven lijst xs.
    # Voorzie het van een gepaste preconditie en postconditie en
    # bewijs de correctheid.
    # Je mag in je correctheidsbeweringen gebruik maken van de bovenstaande
    # functie 'nb_zeros', die het aantal nullen in de lijst xs teruggeeft.

    i = 0
    n = 0
    while i < len(xs):
        if xs[i] == 0:
            n = n + 1
        else:
            pass
        i = i + 1
    
    return n`,
  statements:
`assert number_of_zeros([1, 0, 2, 3, 0]) == 2
assert number_of_zeros([0, 10, 0, 5, 3, 0, 7]) == 3`,
  expression: `number_of_zeros([1, 2, 0, 3, 4]) == 1`
}, {
  title: 'Aantal nullen (oplossing, partiële correctheid)',
  declarations:
`def nb_zeros(xs):
    if xs == []:
        return 0
    elif xs[0] == 0:
        return 1 + nb_zeros(xs[1:])
    else:
        return 0 + nb_zeros(xs[1:])

# Wet LeAntisym: a <= b <= a ==> a == b
# Wet LenNonnegative: 0 <= len(xs)
# Wet SliceFull: xs[:] == xs
# Wet NbZerosEmpty: nb_zeros(xs[i:i]) == 0
# Wet NbZerosZero: 0 <= i and i < len(xs) and xs[i] == 0 ==> nb_zeros(xs[:i + 1]) == nb_zeros(xs[:i]) + 1
# Wet NbZerosNonzero: 0 <= i and i < len(xs) and xs[i] != 0 ==> nb_zeros(xs[:i + 1]) == nb_zeros(xs[:i])

def number_of_zeros(xs):

    assert True # PRECONDITIE PARTIËLE CORRECTHEID
    assert 0 <= 0 <= len(xs) and 0 == nb_zeros(xs[:0]) # Z of LenNonnegative of NbZerosEmpty
    i = 0
    assert 0 <= i <= len(xs) and 0 == nb_zeros(xs[:i])
    n = 0
    assert 0 <= i <= len(xs) and n == nb_zeros(xs[:i]) # Lusinvariant
    while i < len(xs):
        assert 0 <= i <= len(xs) and n == nb_zeros(xs[:i]) and i < len(xs)
        if xs[i] == 0:
            assert 0 <= i <= len(xs) and n == nb_zeros(xs[:i]) and i < len(xs) and xs[i] == 0
            assert 0 <= i < len(xs) and n == nb_zeros(xs[:i]) and nb_zeros(xs[:i]) + 1 == nb_zeros(xs[:i + 1]) # NbZerosZero op 1 en 4 en 5
            assert 0 <= i + 1 <= len(xs) and n + 1 == nb_zeros(xs[:i + 1]) # Z op 1 of Z op 2 of Herschrijven met 3 in 4
            n = n + 1
            assert 0 <= i + 1 <= len(xs) and n == nb_zeros(xs[:i + 1])
        else:
            assert 0 <= i <= len(xs) and n == nb_zeros(xs[:i]) and i < len(xs) and not xs[i] == 0
            assert 0 <= i < len(xs) and n == nb_zeros(xs[:i]) and xs[i] != 0
            assert 0 <= i < len(xs) and n == nb_zeros(xs[:i]) and nb_zeros(xs[:i]) == nb_zeros(xs[:i + 1]) # NbZerosNonzero op 1 en 2 en 4
            assert 0 <= i + 1 <= len(xs) and n == nb_zeros(xs[:i + 1]) # Z op 1 of Z op 2 of Herschrijven met 3 in 4
            pass
            assert 0 <= i + 1 <= len(xs) and n == nb_zeros(xs[:i + 1])
        assert 0 <= i + 1 <= len(xs) and n == nb_zeros(xs[:i + 1])
        i = i + 1
        assert 0 <= i <= len(xs) and n == nb_zeros(xs[:i])
    assert 0 <= i <= len(xs) and n == nb_zeros(xs[:i]) and not i < len(xs)
    assert len(xs) <= i <= len(xs) and n == nb_zeros(xs[:i]) # Z op 4
    assert i == len(xs) and n == nb_zeros(xs[:i]) # LeAntisym op 1 en 2
    assert n == nb_zeros(xs[:len(xs)]) # Herschrijven met 1 in 2
    assert n == nb_zeros(xs) # Herschrijven met SliceFull in 1 # POSTCONDITIE
    
    return n`,
  statements:
`assert number_of_zeros([1, 0, 2, 3, 0]) == 2
assert number_of_zeros([0, 10, 0, 5, 3, 0, 7]) == 3`,
  expression: `number_of_zeros([1, 2, 0, 3, 4]) == 1`
}, {
  title: 'Maximum van een lijst getallen',
  declarations:
`def max(xs):
    if len(xs) == 1:
        return xs[0]
    else:
        m = max(xs[1:])
        if xs[0] <= m:
            return m
        else:
            return xs[0]

# Wet MaxFirst: 1 <= len(xs) ==> max(xs[:1]) == xs[0]
# Wet MaxGreater: 1 <= i + 1 <= len(xs) and max(xs[:i]) < xs[i] ==> max(xs[:i + 1]) == xs[i]
# Wet MaxNotGreater: 1 <= i + 1 <= len(xs) and not max(xs[:i]) < xs[i] ==> max(xs[:i + 1]) == max(xs[:i])
# Wet LeAntisym: x <= y <= x ==> x == y
# Wet SliceFull: xs[:] == xs

def maximum(xs):

    # Het programma hieronder berekent in res het maximum van de elementen van de gegeven niet-lege lijst xs.
    # Voorzie het van een gepaste preconditie en postconditie en bewijs de correctheid.
    # Je mag in je correctheidsbeweringen gebruik maken van de bovenstaande functie 'max', die
    # het maximum van de elementen van de gegeven lijst 'xs' teruggeeft.

    res = xs[0]
    i = 1
    while i < len(xs):
        if res < xs[i]:
            res = xs[i]
        else:
            pass
        i = i + 1

    return res`,
  statements:
`assert maximum([3, 1, 4, 2]) == 4
assert maximum([8]) == 8`,
  expression: `maximum([-3, -2])`
}, {
  title: 'Maximum van een lijst getallen (oplossing, partiële correctheid)',
  declarations:
`def max(xs):
    if len(xs) == 1:
        return xs[0]
    else:
        m = max(xs[1:])
        if xs[0] <= m:
            return m
        else:
            return xs[0]

# Wet MaxFirst: 1 <= len(xs) ==> max(xs[:1]) == xs[0]
# Wet MaxGreater: 1 <= i + 1 <= len(xs) and max(xs[:i]) < xs[i] ==> max(xs[:i + 1]) == xs[i]
# Wet MaxNotGreater: 1 <= i + 1 <= len(xs) and not max(xs[:i]) < xs[i] ==> max(xs[:i + 1]) == max(xs[:i])
# Wet LeAntisym: x <= y <= x ==> x == y
# Wet SliceFull: xs[:] == xs

def maximum(xs):

    assert 1 <= len(xs) # PRECONDITIE PARTIËLE CORRECTHEID
    assert 1 <= 1 <= len(xs) and xs[0] == max(xs[:1]) # Z of MaxFirst op 1
    res = xs[0]
    assert 1 <= 1 <= len(xs) and res == max(xs[:1])
    i = 1
    assert 1 <= i <= len(xs) and res == max(xs[:i])
    while i < len(xs):
        assert 1 <= i <= len(xs) and res == max(xs[:i]) and i < len(xs)
        if res < xs[i]:
            assert 1 <= i <= len(xs) and res == max(xs[:i]) and i < len(xs) and res < xs[i]
            assert 1 <= i + 1 <= len(xs) and max(xs[:i]) < xs[i] # Z op 1 of Herschrijven met 3 in 5
            assert 1 <= i + 1 <= len(xs) and xs[i] == max(xs[:i + 1]) # MaxGreater op 1 en 2 en 3
            res = xs[i]
            assert 1 <= i + 1 <= len(xs) and res == max(xs[:i + 1])
        else:
            assert 1 <= i <= len(xs) and res == max(xs[:i]) and i < len(xs) and not res < xs[i]
            assert 1 <= i + 1 <= len(xs) and res == max(xs[:i]) and not max(xs[:i]) < xs[i] # Z op 1 of Herschrijven met 3 in 5
            assert 1 <= i + 1 <= len(xs) and res == max(xs[:i + 1]) # Herschrijven met MaxNotGreater op 1 en 2 en 4 in 3
            pass
            assert 1 <= i + 1 <= len(xs) and res == max(xs[:i + 1])
        assert 1 <= i + 1 <= len(xs) and res == max(xs[:i + 1])
        i = i + 1
        assert 1 <= i <= len(xs) and res == max(xs[:i])
    assert 1 <= i <= len(xs) and res == max(xs[:i]) and not i < len(xs)
    assert len(xs) <= i <= len(xs) and res == max(xs[:i]) # Z op 4
    assert res == max(xs[:len(xs)]) # Herschrijven met LeAntisym op 1 en 2 in 3
    assert res == max(xs) # Herschrijven met SliceFull in 1 # POSTCONDITIE

    return res`,
  statements:
`assert maximum([3, 1, 4, 2]) == 4
assert maximum([8]) == 8`,
  expression: `maximum([-3, -2])`
},{
title: 'Faculteit',
declarations:
`def fac(n):
    if n == 0:
        return 1
    else:
        return n * fac(n - 1)

# Wet LeAntisym: x <= y <= x ==> x == y
# Wet Fac0: fac(0) == 1
# Wet FacPlusOne: 0 <= n ==> fac(n + 1) == (n + 1) * fac(n)

def factorial(n):

    # Het programma hieronder berekent in de variabele 'res' de faculteit
    # van het gegeven getal 'n'.
    # Voorzie het van een gepaste preconditie en postconditie
    # en bewijs de correctheid.
    # Je mag in je correctheidsbeweringen gebruik maken van
    # de bovenstaande functie 'fac', die hetzelfde resultaat
    # berekent, maar dan recursief in plaats van iteratief.

    res = 1
    i = 0
    while i < n:
        i = i + 1
        res = i * res

    return res
`,
statements:
`assert factorial(3) == 6
assert factorial(0) == 1`,
expression: `factorial(4)`
},{
title: 'Som van kwadraten',
declarations:
`def som_kwadraten(n):
    if n == 0:
        return 0
    else:
        return n * n + som_kwadraten(n - 1)

# Wet LeAntisym: x <= y <= x ==> x == y
# Wet SomKwadraten0: som_kwadraten(0) == 0
# Wet SomKwadratenPlusOne: 0 <= n ==> som_kwadraten(n + 1) == (n + 1) * (n + 1) + som_kwadraten(n)

def som_van_kwadraten(n):

    # Het programma hieronder berekent in de variabele 'res' de som van
    # de kwadraten van de getallen tussen 0 en 'n'.
    # Voorzie het van een gepaste preconditie en postconditie
    # en bewijs de correctheid.
    # Je mag in je correctheidsbeweringen gebruik maken van
    # de bovenstaande functie 'som_kwadraten', die hetzelfde
    # resultaat teruggeeft, maar dan recursief berekend in
    # plaats van iteratief.

    res = 0
    i = 0
    while i < n:
        i = i + 1
        res = i * i + res

    return res
`,
statements:
`assert som_kwadraten(3) == 14
assert som_kwadraten(0) == 0`,
expression: `som_kwadraten(4) == 30`
},{
title: 'Som van oneven getallen',
declarations:
`def even(i):
    if i < 0:
        return even(-i)
    elif i == 0:
        return True
    elif i == 1:
        return False
    else:
        return even(i - 2)

def som_oneven(n):
    if n <= 0:
        return 0
    else:
        if even(n):
            return som_oneven(n - 1)
        else:
            return n + som_oneven(n - 1)

# Wet LeAntisym: x <= y <= x ==> x == y
# Wet Le20NotEven: i <= 20 and not even(i) ==> i <= 19
# Wet NotEven1: not even(1)
# Wet NotEvenPlus2: not even(i) ==> not even(i + 2)
# Wet SomOneven0: som_oneven(0) == 0
# Wet SomOnevenPlusTwo: 1 <= i and not even(i) ==> som_oneven(i + 1) == som_oneven(i - 1) + i

def som_van_oneven():

    # Het programma hieronder berekent de som van de oneven getallen tussen
    # 0 en 20.
    # Voorzie het van een gepaste preconditie en postconditie
    # en bewijs de correctheid.
    # Je mag in je correctheidsbeweringen gebruik maken van
    # de bovenstaande functies 'som_oneven' en 'even'.

    i = 1
    som = 0
    while i <= 20:
        som = som + i
        i = i + 2

    return som
`,
statements:
`assert som_van_oneven() == 19 + 17 + 15 + 13 + 11 + 9 + 7 + 5 + 3 + 1`,
expression: `som_van_oneven()`
},{
title: 'Kleinst gemeen veelvoud',
declarations:
`def ggd(a, b):
    if a == 0:
        return b
    elif b == 0:
        return a
    elif a < b:
        return ggd(a, b - a)
    else:
        return ggd(a - b, b)

# Wet LeAntisym: x <= y <= x ==> x == y
# Wet GgdZero: 0 <= x ==> ggd(x, 0) == x
# Wet GgdCommut: 0 <= x and 0 <= y ==> ggd(x, y) == ggd(y, x)
# Wet GgdMinus: 0 <= a <= b ==> ggd(b, a) == ggd(b - a, a)

def grootste_gemene_deler(a, b):

    # Het programma hieronder berekent in x de grootste gemene deler van
    # de gegeven niet-negatieve getallen a en b.
    # (We stellen de grootste gemene deler van nul en nul gelijk
    # aan nul.)
    # Voorzie het van een gepaste preconditie en postconditie
    # en bewijs de correctheid.
    # Je mag in je correctheidsbeweringen gebruik maken van de
    # bovenstaande functie 'ggd'.

    if a < b:
        x = b
        y = a
    else:
        x = a
        y = b
    while 0 < y:
        x = x - y
        if x < y:
            tmp = x
            x = y
            y = tmp
        else:
            pass

    return x

def kleinst_gemeen_veelvoud(a, b):
    return a * b / ggd(a, b)
`,
statements:
`assert kleinst_gemeen_veelvoud(15, 20) == 60`,
expression: `kleinst_gemeen_veelvoud(6, 10)`
},{
title: 'Dubbele voorkomens',
declarations:
`def nodup(xs):
    if xs == []:
        return []
    res0 = nodup(xs[:-1])
    if xs[-1] in res0:
        return res0
    else:
        return res0 + [xs[-1]]

# Wet LeAntisym: x <= y <= x ==> x == y
# Wet LenNonneg: 0 <= len(xs)
# Wet SliceEmpty: xs[:0] == []
# Wet SliceFull: xs[:] == xs
# Wet NoDupEmpty: nodup([]) == []
# Wet NoDupNotIn: 0 <= i < len(xs) and xs[i] not in nodup(xs[:i]) ==> nodup(xs[:i + 1]) == nodup(xs[:i]) + [xs[i]]
# Wet NoDupIn: 0 <= i < len(xs) and xs[i] in nodup(xs[:i]) ==> nodup(xs[:i + 1]) == nodup(xs[:i])
# Wet InEmpty: (x in []) == False
# Wet InEq: 0 <= i < len(xs) and x == xs[i] ==> (x in xs[:i + 1]) == True
# Wet InNotEq: 0 <= i < len(xs) and x != xs[i] ==> (x in xs[:i + 1]) == (x in xs[:i])

def zonder_dubbele_voorkomens(xs):

    # Het programma hieronder berekent in de variabele 'res' een versie
    # van de gegeven lijst 'xs' waaruit de eventuele herhaalde
    # voorkomens van elk element verwijderd zijn.
    # Voorzie het van een gepaste preconditie en postconditie
    # en bewijs de correctheid.
    # Je mag in je correctheidsbeweringen gebruik maken van de
    # bovenstaande functie 'nodup', die hetzelfde resultaat
    # berekent, maar dan op een minder efficiënte manier.

    res = []
    i = 0
    while i < len(xs):
        is_dubbel = False
        j = 0
        while j < len(res):
            if res[j] == xs[i]:
                is_dubbel = True
            else:
                pass
            j = j + 1
        if not is_dubbel:
            res = res + [xs[i]] # res.append(xs[i])
        else:
            pass
        i = i + 1

    return res
    
`,
statements:
`assert zonder_dubbele_voorkomens([10, 20, 30, 20, 40, 10, 50]) == [10, 20, 30, 40, 50]`,
expression: `zonder_dubbele_voorkomens([80, 60, 30, 60, 80, 10])`
},{
title: 'Fibonacci',
declarations:
`def fib(n):
    if n == 0:
        return 0
    elif n == 1:
        return 1
    else:
        return fib(n - 2) + fib(n - 1)

# Wet LeAntisym: x <= y <= x ==> x == y
# Wet Fib0: fib(0) == 0
# Wet Fib1: fib(1) == 1
# Wet FibPlusTwo: 0 <= i ==> fib(i + 2) == fib(i) + fib(i + 1)

def fibonacci(n):

    # Het programma hieronder berekent in variabele 'curr' het n-de
    # Fibonacci-getal.
    # Voorzie het van een gepaste preconditie en postconditie
    # en bewijs de correctheid.
    # Je mag in je correctheidsbeweringen gebruik maken van de
    # bovenstaande functie 'fib', die dezelfde uitkomst
    # berekent (maar op een minder efficiënte manier).

    prev = 1
    curr = 0
    i = 0
    while i < n:
        i = i + 1
        next = prev + curr
        prev = curr
        curr = next
    
    return curr

`,
statements:
`assert fibonacci(2) == 1
assert fibonacci(3) == 2
assert fibonacci(4) == 3
assert fibonacci(5) == 5
assert fibonacci(6) == 8`,
expression: `fibonacci(7)`
}
]

function setExample(example: Example) {
  reset();
  declarationsEditor.setValue(example.declarations || "");
  statementsEditor.setValue(example.statements || "");
  expressionEditor.setValue(example.expression || "");
}

function initExamples() {
  setExample(examples[0]);

  let examplesNode = document.getElementById('examples') as HTMLSelectElement;
  examplesNode.onchange = event => {
    if (examplesNode.selectedOptions.length > 0)
      (examplesNode.selectedOptions[0] as any).my_onselected();
  };
  for (let example of examples) {
    let exampleOption = document.createElement('option');
    examplesNode.appendChild(exampleOption);
    exampleOption.innerText = example.title;
    (exampleOption as any).my_onselected = () => setExample(example);
  }
}

async function testExamples(examples: Example[]) {
  for (const {declarations, statements, expression} of examples) {
    resetMachine();
    iterationCount = 0;
    lawComments = [];
    let decls = parseDeclarations(mkLocFactory(declarations), declarations, processComment);
    checkDeclarations(decls);

    let stmts = parseStatements(mkLocFactory(statements), statements);
    for (const stmt of stmts) {
      if (await stmt.execute(toplevelScope) !== undefined)
        break;
    }

    if (expression != '') {
      let e = parseExpression(mkLocFactory(expression), expression);
      await e.evaluate(toplevelScope);
      let [v] = pop(1);
    }

    checkLaws();
    for (let m in toplevelMethods)
      toplevelMethods[m].checkProofOutlines();
  }
}

declare var secretExamples: Example[]|undefined;

async function testPyLearner() {
  currentBreakCondition = () => false;
  await testExamples(examples);
  console.log('All tests passed!');
  if (typeof secretExamples !== 'undefined') {
    await testExamples(secretExamples);
    console.log('All secret tests passed!');
  }
}

if (typeof window === 'undefined') // We're being executed by Node.js.
  testPyLearner();