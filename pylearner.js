function isDigit(c) { return '0' <= c && c <= '9'; }
function isAlpha(c) { return 'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z' || c == '_'; }

function has(object, propertyName) { return Object.prototype.hasOwnProperty.call(object, propertyName); }

keywordsList = [
  'False', 'None', 'True', 'and', 'as', 'assert', 'async',
  'await', 'break', 'class', 'continue',
  'def', 'del', 'elif', 'else', 'except', 'finally', 'for', 'from',
  'global', 'if', 'import', 'in', 'is', 'lambda', 'nonlocal', 'not',
  'or', 'pass', 'raise', 'return', 'try', 'while', 'with', 'yield'
];

keywords = {};

for (let keyword of keywordsList)
  keywords[keyword] = true;

operatorsList = [
  '+', '-', '*', '**', '/', '//', '%', '@',
  '<<', '>>', '&', '|', '^', '~', ':=',
  '<', '>', '<=', '>=', '==', '!=',
  '(', ')', '[', ']', '{', '}',
  ',', ':', '.', ';', '@', '=', '->',
  '+=', '-=', '*=', '/=', '//=', '%=', '@=',
  '&=', '|=', '^=', '>>=', '<<=', '**='
]

operators = {};
operatorPrefixes = {};

for (let operator of operatorsList) {
  operators[operator] = true;
  for (let i = 1; i < operator.length; i++)
    operatorPrefixes[operator.substring(0, i)] = true;
}

class Comment {
  constructor(locFactory, start, text, isOnNewLine) {
    this.locFactory = locFactory;
    this.start = start;
    this.text = text;
    this.isOnNewLine = isOnNewLine;
  }

  loc() {
    return this.locFactory(this.start, this.start + this.text.length);
  }
}

class Scanner {
  constructor(locFactory, text, parseExpression, commentListener) {
    this.locFactory = locFactory;
    this.text = text;
    this.pos = -1;
    this.startOfLine = 0;
    this.indentStack = [''];
    this.bracketsDepth = parseExpression ? 1 : 0;
    this.emittedEOL = true;
    this.onNewLine = true;
    this.commentListener = commentListener;
    this.eat();
  }

  currentIndent() {
    return this.indentStack[this.indentStack.length - 1];
  }

  eat() {
    this.pos++;
    this.c = (this.pos == this.text.length ? "<EOF>" : this.text.charAt(this.pos));
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
          while (this.c != '<EOF>' && this.c != '\n' && this.c != '\r')
            this.eat();
          const comment = new Comment(this.locFactory, commentStart, this.text.slice(commentStart, this.pos), this.onNewLine);
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
    if (this.c == '<EOF>') {
      if (this.bracketsDepth > 0)
        return "EOF"; // Parser will detect error
      if (!this.emittedEOL) {
        this.emittedEOL = true;
        this.value = this.comment;
        return "EOL";
      }
      if (this.currentIndent() != '') {
        this.indentStack.pop();
        return "DEDENT";
      }
      return 'EOF';
    }
    if (this.onNewLine) {
      if (this.bracketsDepth == 0) {
        if (!this.emittedEOL) {
          this.emittedEOL = true;
          this.value = this.comment;
          return "EOL";
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
          throw new LocError(this.locFactory(this.tokenStart, this.tokenStart + 1), "Bad indentation");
      }
    }
    this.onNewLine = false;
    this.emittedEOL = false;
    if (isDigit(this.c)) {
      this.eat();
      while (isDigit(this.c))
        this.eat();
      this.value = this.text.substring(this.tokenStart, this.pos);
      return "NUMBER";
    }
    if (isAlpha(this.c)) {
      let c0 = this.c;
      this.eat();
      while (isAlpha(this.c) || isDigit(this.c))
        this.eat();
      this.value = this.text.substring(this.tokenStart, this.pos);
      if (has(keywords, this.value))
        return this.value;
      return "IDENT";
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
      throw new LocError(this.locFactory(this.tokenStart, this.tokenStart + 1), "Bad character");
    this.pos += longestOperatorFound.length - 1;
    this.eat();
    if (longestOperatorFound in ['(', '[', '{'])
      this.bracketsDepth++;
    else if (longestOperatorFound in [')', ']', '}'])
      this.bracketsDepth--;
    return longestOperatorFound;
  }
}

class LocalBinding {
  constructor(declaration, value) {
    this.declaration = declaration;
    this.value = value;
  }
  
  setValue(value) {
    return this.value = value;
  }

  getNameHTML() {
    return this.declaration.type.resolve().toHTML() + " " + this.declaration.name;
  }
}

class OperandBinding {
  constructor(expression, value) {
    this.expression = expression;
    this.value = value;
  }

  getNameHTML() {
    return "(operand)";
  }
}

class ImplicitVariableDeclaration {
  constructor(name, type) {
    this.name = name;
    this.type = new ImplicitTypeExpression(type);
  }
}

class Scope {
  constructor(outerScope, inferBindings) {
    this.outerScope = outerScope;
    this.bindings = {};
    this.inferBindings = inferBindings;
  }
  
  tryLookup(x) {
    if (has(this.bindings, x))
      return this.bindings[x];
    if (this.outerScope != null)
      return this.outerScope.tryLookup(x);
    return null;
  }
  
  lookup(loc, x, createIfMissing) {
    let result = this.tryLookup(x);
    if (result == null)
      if (createIfMissing) {
        result = this.bindings[x] = new LocalBinding(x, null);
      } else if (this.inferBindings) {
        const type = new InferredType();
        const decl = new ImplicitVariableDeclaration(x, type);
        result = this.bindings[x] = new LocalBinding(decl, type);
      } else
        throw new ExecutionError(loc, "No such variable in scope: " + x);
    return result;
  }
  
  *allBindings() {
    if (this.outerScope != null)
      yield* this.outerScope.allBindings();
    for (let x in this.bindings)
      yield this.bindings[x];
  }
}

class StackFrame {
  constructor(title, env) {
    this.title = title;
    this.env = env;
    this.operands = [];
  }

  *allBindings() {
    yield* this.env.allBindings();
    for (let operand of this.operands)
      yield operand;
  }
}

class ASTNode {
  constructor(loc, instrLoc) {
    this.loc = loc;
    this.instrLoc = instrLoc;
  }

  async breakpoint() {
    await checkBreakpoint(this);
  }
  
  executionError(msg) {
    throw new ExecutionError(this.instrLoc, msg);
  }
}

class Expression extends ASTNode {
  constructor(loc, instrLoc) {
    super(loc, instrLoc);
  }

  check_(env) {
    this.type = this.check(env);
    return this.type;
  }

  checkAgainst(env, targetType) {
    let t = this.check_(env);
    if (targetType instanceof ReferenceType && t == nullType)
      return;
    if (!targetType.equals(t))
      this.executionError("Expression has type " + t + ", but an expression of type " + targetType + " was expected");
  }
  
  async evaluateBinding(env) {
    this.executionError("This expression cannot appear on the left-hand side of an assignment");
  }

  push(value) {
    push(new OperandBinding(this, value));
  }
}

class IntLiteral extends Expression {
  constructor(loc, value, silent) {
    super(loc, loc);
    this.value = value;
    this.silent = silent;
  }

  check(env) {
    return intType;
  }

  async evaluate(env) {
    if (this.silent !== true)
      await this.breakpoint();
    this.push(+this.value);
  }
}

class BooleanLiteral extends Expression {
  constructor(loc, value, silent) {
    super(loc, loc);
    this.value = value;
    this.silent = silent;
  }

  check(env) {
    return booleanType;
  }

  async evaluate(env) {
    if (this.silent !== true)
      await this.breakpoint();
    this.push(this.value);
  }
}

class NullLiteral extends Expression {
  constructor(loc) {
    super(loc, loc);
  }

  check(env) {
    return nullType;
  }

  async evaluate(env) {
    await this.breakpoint();
    this.push(null);
  }
}

class UnaryOperatorExpression extends Expression {
  constructor(loc, instrLoc, operator, operand) {
    super(loc, instrLoc);
    this.operator = operator;
    this.operand = operand;
  }

  check(env) {
    switch (this.operator) {
      case 'not':
        this.operand.checkAgainst(env, booleanType);
        return booleanType;
      default:
        this.executionError("Operator not supported");
    }
  }

  eval(v) {
    switch (this.operator) {
      case 'not': return !v;
      default:
        this.executionError("Operator not supported");
    }
  }

  async evaluate(env) {
    await this.operand.evaluate(env);
    await this.breakpoint();
    let [v] = pop(1);
    this.push(this.eval(v));
  }
}

class BinaryOperatorExpression extends Expression {
  constructor(loc, instrLoc, leftOperand, operator, rightOperand) {
    super(loc, instrLoc);
    this.leftOperand = leftOperand;
    this.operator = operator;
    this.rightOperand = rightOperand;
  }

  check(env) {
    switch (this.operator) {
      case '+':
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
        this.executionError("Operator not supported");
    }
  }

  eval(v1, v2) {
    switch (this.operator) {
      case '+': return (v1 + v2)|0;
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
      case '==': return v1 == v2;
      case '!=': return v1 != v2;
      case '<': return v1 < v2;
      case '<=': return v1 <= v2;
      case '>': return v1 > v2;
      case '>=': return v1 >= v2;
      default: this.executionError("Operator '" + this.operator + "' not supported.");
    }
  }
  
  async evaluate(env) {
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
  constructor(loc, name) {
    super(loc, loc);
    this.name = name;
  }

  check(env) {
    return env.lookup(this.loc, this.name).declaration.type.type;
  }
  
  async evaluateBinding(env, allowReadOnly) {
    return () => env.lookup(this.loc, this.name, !allowReadOnly);
  }
  
  async evaluate(env) {
    await this.breakpoint();
    this.push(env.lookup(this.loc, this.name).value);
  }
}

class AssignmentExpression extends Expression {
  constructor(loc, instrLoc, lhs, op, rhs) {
    super(loc, instrLoc);
    this.lhs = lhs;
    this.op = op;
    this.rhs = rhs;
    this.declaration = null;
  }

  check(env) {
    if (this.op == '=') {
      if (this.lhs instanceof VariableExpression && env.tryLookup(this.lhs.name) == null) {
        this.declaration = new VariableDeclarationStatement(this.loc, this.instrLoc, new ImplicitTypeExpression(), this.lhs.loc, this.lhs.name, this.rhs);
        this.declaration.check(env);
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

  evaluateOperator(lhs, rhs) {
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
        this.executionError("Operator not supported");
    }
  }
  
  async evaluate(env) {
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
  constructor(loc, instrLoc, operand, isDecrement, isPostfix) {
    super(loc, instrLoc);
    this.operand = operand;
    this.isDecrement = isDecrement;
    this.isPostfix = isPostfix;
  }

  check(env) {
    this.operand.checkAgainst(env, intType);
    return intType;
  }

  async evaluate(env) {
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
let objectsShown = [];

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
  let svg = document.getElementById('arrows-svg');
  let svgRect = svg.getClientRects()[0];

  let nextObjectY = 0;
  
  for (let o of objectsShown) {
    let rect = o.domNode.getClientRects()[0];
    nextObjectY = Math.max(nextObjectY, rect.bottom - svgRect.top + 15);
  }

  return nextObjectY;
}

function createHeapObjectDOMNode(object) {
  let heap = document.getElementById('heap');
  let node = document.createElement('table');
  heap.appendChild(node);
  node.className = 'object-table';
  node.style.left = "0px";
  node.style.top = computeNextObjectY() + "px";
  node.onmousedown = event0 => {
    event0.preventDefault();
    let left0 = node.offsetLeft;
    let top0 = node.offsetTop;
    let moveListener = event => {
      event.preventDefault();
      node.style.left = (left0 + event.x - event0.x) + "px";
      node.style.top = (top0 + event.y - event0.y) + "px";
      updateArrows();
    };
    let upListener = event => {
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
  constructor(value) {
    this.value = value;
    this.arrow = null;
  }
  
  setValue(value) {
    if (this.arrow != null) {
      this.arrow.parentNode.removeChild(this.arrow);
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
  constructor(type, fields) {
    this.id = ++objectsCount;
    this.type = type;
    this.fields = fields;
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

function initialClassFieldBindings(class_) {
  let fields = {};
  for (let field in class_.fields)
    fields[field] = new FieldBinding(class_.fields[field].type.resolve().defaultValue());
  return fields;
}

class JavaClassObject extends JavaObject {
  constructor(class_) {
    super(class_.type, initialClassFieldBindings(class_));
    this.class_ = class_;
  }
}

function initialArrayFieldBindings(initialContents) {
  let fields = {};
  for (let i = 0; i < initialContents.length; i++)
    fields[i] = new FieldBinding(initialContents[i]);
  return fields;
}

class ListObject extends JavaObject {
  constructor(elementType, initialContents) {
    super(new ListType(elementType), initialArrayFieldBindings(initialContents));
    this.length = initialContents.length;
  }
}

class NewExpression extends Expression {
  constructor(loc, instrLoc, className) {
    super(loc, instrLoc);
    this.className = className;
  }

  check(env) {
    if (!has(classes, this.className))
      this.executionError("No such class: " + this.className);
    return classes[this.className].type;
  }
  
  async evaluate(env) {
    await this.breakpoint();
    if (!has(classes, this.className))
      this.executionError("No such class: " + this.className);
    this.push(new JavaClassObject(classes[this.className]));
  }
}

class NewArrayExpression extends Expression {
  constructor(loc, instrLoc, elementType, lengthExpr) {
    super(loc, instrLoc);
    this.elementType = elementType;
    this.lengthExpr = lengthExpr;
  }

  check(env) {
    this.elementType.resolve();
    this.lengthExpr.checkAgainst(env, intType);
    return new ListType(this.elementType.type);
  }

  async evaluate(env) {
    await this.lengthExpr.evaluate(env);
    await this.breakpoint();
    let [length] = pop(1);
    if (length < 0)
      this.executionError("Negative array length");
    this.elementType.resolve();
    this.push(new ListObject(this.elementType.type, Array(length).fill(this.elementType.type.defaultValue())));
  }
}

class ListExpression extends Expression {
  constructor(loc, instrLoc, elementType, elementExpressions) {
    super(loc, instrLoc);
    this.elementType = elementType;
    this.elementExpressions = elementExpressions;
  }

  check(env) {
    this.elementType.resolve();
    for (let e of this.elementExpressions)
      e.checkAgainst(env, this.elementType.type);
    return new ListType(this.elementType.type);
  }

  async evaluate(env) {
    for (let e of this.elementExpressions)
      await e.evaluate(env);
    await this.breakpoint();
    let elements = pop(this.elementExpressions.length);
    this.elementType.resolve();
    this.push(new ListObject(this.elementType.type, elements));
  }
}

class ReadOnlyBinding {
  constructor(value) {
    this.value = value;
  }
}

class SelectExpression extends Expression {
  constructor(loc, instrLoc, target, selectorLoc, selector) {
    super(loc, instrLoc);
    this.target = target;
    this.selectorLoc = selectorLoc;
    this.selector = selector;
  }

  check(env) {
    let targetType = this.target.check_(env);
    if (targetType instanceof ListType) {
      if (this.selector != "length")
        this.executionError("Arrays do not have a field named '" + this.selector + "'");
      return intType;
    }
    if (!(targetType instanceof ClassType))
      this.executionError("Target expression must be of class type");
    if (!has(targetType.class_.fields, this.selector))
      this.executionError("Class " + targetType.class_.name + " does not have a field named '" + this.selector + "'");
    return targetType.class_.fields[this.selector].type.type;
  }
  
  async evaluateBinding(env, allowReadOnly) {
    await this.target.evaluate(env);
    return pop => {
      let [target] = pop(1);
      if (target instanceof ListObject) {
        if (this.selector != "length")
          this.executionError(target + " does not have a field named '" + this.selector + "'");
        if (allowReadOnly !== true)
          this.executionError("Cannot modify an array's length");
        return new ReadOnlyBinding(target.length);
      }
      if (!(target instanceof JavaObject))
        this.executionError(target + " is not an object");
      if (!has(target.fields, this.selector))
        this.executionError("Target does not have a field named " + this.selector);
      return target.fields[this.selector];
    }
  }
  
  async evaluate(env) {
    let bindingThunk = await this.evaluateBinding(env, true);
    await this.breakpoint();
    this.push(bindingThunk(pop).value);
  }
}

class SubscriptExpression extends Expression {
  constructor(loc, instrLoc, target, index) {
    super(loc, instrLoc);
    this.target = target;
    this.index = index;
  }

  check(env) {
    let targetType = this.target.check_(env);
    if (!(targetType instanceof ListType))
      this.executionError("Target of subscript expression must be of array type");
    this.index.checkAgainst(env, intType);
    return targetType.elementType;
  }

  async evaluateBinding(env) {
    await this.target.evaluate(env);
    await this.index.evaluate(env);
    return pop => {
      let [target, index] = pop(2);
      if (!(target instanceof ListObject))
        this.executionError(target + " is not an array");
      if (index < 0)
        this.executionError("Negative array index " + index);
      if (target.length <= index)
        this.executionError("Array index " + index + " not less than array length " + target.length);
      return target.fields[index];
    }
  }

  async evaluate(env) {
    let bindingThunk = await this.evaluateBinding(env);
    await this.breakpoint();
    this.push(bindingThunk(pop).value);
  }
}

class CallExpression extends Expression {
  constructor(loc, instrLoc, callee, args) {
    super(loc, instrLoc);
    this.callee = callee;
    this.arguments = args;
  }

  check(env) {
    if (this.callee instanceof VariableExpression) {
      if (!has(toplevelMethods, this.callee.name))
        this.executionError("No such method: " + this.callee.name);
      let method = toplevelMethods[this.callee.name];
      if (method.parameterDeclarations.length != this.arguments.length)
        this.executionError("Incorrect number of arguments");
      for (let i = 0; i < this.arguments.length; i++)
        this.arguments[i].checkAgainst(env, method.parameterDeclarations[i].type.type);
      return method.returnType.type;
    }
  }

  async evaluate(env) {
    if (this.callee instanceof VariableExpression) {
      if (!has(toplevelMethods, this.callee.name))
        this.executionError("No such method: " + this.callee.name);
      let method = toplevelMethods[this.callee.name];
      if (method.parameterDeclarations.length != this.arguments.length)
        this.executionError("Incorrect number of arguments");
      for (let e of this.arguments)
        await e.evaluate(env);
      await this.breakpoint();
      let args = pop(this.arguments.length);
      await method.call(this, args);
    } else
      this.executionError("Callee expression must be a name");
  }
}

class Type {
  constructor() {}
  toHTML() {
    let text = this.toString();
    if (has(keywords, text))
      return "<span class='keyword'>" + text + "</span>";
    return text;
  }
  unwrapInferredType() {
    let t = this;
    while (t instanceof InferredType && t.type != null)
      t = t.type;
    return t;
  }
  equals(other) {
    other = other.unwrapInferredType();
    if (other instanceof InferredType)
      return other.equals(this);
    return this == other;
  }
}

class InferredType extends Type {
  constructor() {
    super();
    this.type = null;
  }
  equals(other) {
    other = other.unwrapInferredType();
    if (this == other)
      return true;
    if (this.type != null)
      return this.type.equals(other);
    this.type = other;
    return true;
  }
  toString() {
    return this.type == null ? "?" : this.type.toString();
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
}

let intType = new IntType();

class VoidType extends Type {
  constructor() { super(); }
  toString() { return "void"; }
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
  constructor(class_) {
    super();
    this.class_ = class_;
  }
  toString() { return this.class_.name; }
}

class ListType extends ReferenceType {
  constructor(elementType) {
    super();
    this.elementType = elementType;
  }
  toString() { return "list"; }
  toHTML() { return "list"; }
  equals(other) {
    other = other.unwrapInferredType();
    if (other instanceof InferredType)
      return other.equals(this);
    return other instanceof ListType && this.elementType.equals(other.elementType);
  }
}

class TypeExpression extends ASTNode {
  constructor(loc) {
    super(loc, loc);
  }
}

class ImplicitTypeExpression extends ASTNode {
  constructor(type) {
    super(null);
    this.type = type || intType;
  }
  resolve() {
    return this.type;
  }
}

class LiteralTypeExpression extends TypeExpression {
  constructor(loc, type) {
    super(loc);
    this.type = type;
  }
  resolve() {
    return this.type;
  }
}

class ClassTypeExpression extends TypeExpression {
  constructor(loc, name) {
    super(loc);
    this.name = name;
  }
  resolve() {
    if (!has(classes, this.name))
      throw new LocError(this.loc, "No such class");
    return this.type = classes[this.name].type;;
  }
}

class ArrayTypeExpression extends TypeExpression {
  constructor(loc, elementTypeExpression) {
    super(loc);
    this.elementTypeExpression = elementTypeExpression;
  }
  resolve() {
    this.elementType = this.elementTypeExpression.resolve();
    this.type = new ListType(this.elementType);
    return this.type;
  }
}

class Statement extends ASTNode {
  constructor(loc, instrLoc) {
    super(loc, instrLoc);
  }
}

class VariableDeclarationStatement extends Statement {
  constructor(loc, instrLoc, type, nameLoc, name, init) {
    super(loc, instrLoc);
    this.type = type;
    this.nameLoc = nameLoc;
    this.name = name;
    this.init = init;
  }

  check(env) {
    this.type.resolve();
    if (env.tryLookup(this.name) != null)
      throw new ExecutionError(this.nameLoc, "Variable '" + this.name + "' already exists in this scope.");
    this.init.checkAgainst(env, this.type.type);
    env.bindings[this.name] = new LocalBinding(this, this.type.type);
  }
  
  async execute(env) {
    if (env.tryLookup(this.name) != null)
      throw new ExecutionError(this.nameLoc, "Variable '"+this.name+"' already exists in this scope.");
    await this.init.evaluate(env);
    await this.breakpoint();
    let [v] = pop(1);
    env.bindings[this.name] = new LocalBinding(this, v);
  }
}

class ExpressionStatement extends Statement {
  constructor(loc, instrLoc, expr) {
    super(loc, instrLoc);
    this.expr = expr;
  }

  check(env) {
    this.expr.check_(env);
  }
  
  async execute(env) {
    await this.expr.evaluate(env);
    pop(1);
  }
}

class ReturnStatement extends Statement {
  constructor(loc, instrLoc, operand) {
    super(loc, instrLoc);
    this.operand = operand;
  }

  check(env) {
    let resultType = env.tryLookup("#result");
    if (resultType == null)
      this.executionError("Cannot return here");
    if (this.operand == null) {
      if (resultType.value != voidType)
        this.executionError("Return value expected");
    } else {
      this.operand.checkAgainst(env, resultType.value);
    }
  }

  async execute(env) {
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
  constructor(loc, stmts) {
    super(loc, loc);
    this.stmts = stmts;
  }

  check(env) {
    let scope = new Scope(env);
    for (let stmt of this.stmts)
      stmt.check(scope);
  }

  async execute(env) {
    let scope = new Scope(env);
    callStack[callStack.length - 1].env = scope;
    let result;
    for (let stmt of this.stmts) {
      result = await stmt.execute(scope);
      if (result !== undefined)
        break;
    }
    callStack[callStack.length - 1].env = env;
    return result;
  }
}

let iterationCount = 0;

class WhileStatement extends Statement {
  constructor(loc, instrLoc, condition, body) {
    super(loc, instrLoc);
    this.condition = condition;
    this.body = body;
  }

  check(env) {
    this.condition.checkAgainst(env, booleanType);
    this.body.check(env);
  }

  async execute(env) {
    let result;
    while (result === undefined) {
      iterationCount++;
      if (iterationCount == 1000)
        this.executionError("Too many loop iterations. Possible infinite loop.");
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
  constructor(loc, instrLoc, condition, thenBody, elseBody) {
    super(loc, instrLoc);
    this.condition = condition;
    this.thenBody = thenBody;
    this.elseBody = elseBody;
  }

  check(env) {
    this.condition.checkAgainst(env, booleanType);
    this.thenBody.check(env);
    if (this.elseBody != null)
      this.elseBody.check(env);
  }

  async execute(env) {
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
  constructor(loc, instrLoc, condition, comment) {
    super(loc, instrLoc);
    this.condition = condition;
    this.comment = comment;
  }
  
  check(env) {
    this.condition.checkAgainst(env, booleanType);
  }
  
  async execute(env) {
    await this.condition.evaluate(env);
    await this.breakpoint();
    let [b] = pop(1);
    if (!b)
      this.executionError("The assertion is false");
  }
}

class Declaration extends ASTNode {
  constructor(loc) {
    super(loc, null);
  }
}

class ParameterDeclaration extends Declaration {
  constructor(loc, type, nameLoc, name) {
    super(loc);
    this.type = type;
    this.nameLoc = nameLoc;
    this.name = name;
  }

  check() {
    this.type.resolve();
  }
}

let maxCallStackDepth = 100;

class MethodDeclaration extends Declaration {
  constructor(loc, returnType, nameLoc, name, parameterDeclarations, bodyBlock) {
    super(loc);
    this.returnType = returnType;
    this.nameLoc = nameLoc;
    this.name = name;
    this.parameterDeclarations = parameterDeclarations;
    this.bodyBlock = bodyBlock;
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
        this.executionError("Duplicate parameter name");
      env.bindings[p.name] = new LocalBinding(p, p.type.type);
    }
    env.bindings["#result"] = new LocalBinding(this, this.returnType.type);
    for (let stmt of this.bodyBlock)
      stmt.check(env);
  }

  async call(callExpr, args) {
    let env = new Scope(null);
    if (callStack.length >= maxCallStackDepth)
      throw new LocError(callExpr.loc, "Maximum call stack depth (= " + maxCallStackDepth + ") exceeded");
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
    let env = this.parameterDeclarations.reduceRight((acc, d) => EnvCons(d.name, acc), EnvNil);
    let outlineStart = null;
    let outlineStartEnv = null;

    for (let i = 0; i < this.bodyBlock.length; i++) {
      const stmt = this.bodyBlock[i];
      if (stmt instanceof ExpressionStatement && stmt.expr instanceof AssignmentExpression && stmt.expr.declaration != null)
        env = EnvCons(stmt.expr.declaration.name, env);
      if (stmt instanceof AssertStatement && stmt.comment != null) {
        if (stmt.comment.text.includes('PRECONDITION')) {
          if (outlineStart != null)
            stmt.executionError("Unexpected PRECONDITION tag inside proof outline");
          outlineStart = i;
          outlineStartEnv = env;
        }
        if (stmt.comment.text.includes('POSTCONDITION')) {
          if (outlineStart == null)
            stmt.executionError("POSTCONDITION without PRECONDITION");
          checkProofOutline(outlineStartEnv, this.bodyBlock.slice(outlineStart, i + 1));
          outlineStart = null;
          outlineStartEnv = null;
        }
      }
    }
  }
}

function parseProofOutlineExpression(e) {
  if (e instanceof IntLiteral)
    return Val(e.loc, +e.value);
  else if (e instanceof BooleanLiteral)
    if (e.value)
      return BinOp(e.loc, Eq, Val(e.loc, 0), Val(e.loc, 0));
    else
      return BinOp(e.loc, Eq, Val(e.loc, 0), Val(e.loc, 1));
  else if (e instanceof VariableExpression)
    return Var(e.loc, e.name);
  else if (e instanceof BinaryOperatorExpression) {
    const t1 = parseProofOutlineExpression(e.leftOperand);
    const t2 = parseProofOutlineExpression(e.rightOperand);
    let op = null;
    switch (e.operator) {
      case '+': op = Add; break;
      case '-': op = Sub; break;
      case '==': op = Eq; break;
      case '<=': op = Le; break;
      case '>=': return BinOp(e.loc, Le, t2, t1);
      case '<': return BinOp(e.loc, Le, BinOp(e.loc, Add, t1, Val(e.loc, 1)), t2);
      case '>': return BinOp(e.loc, Le, BinOp(e.loc, Add, t2, Val(e.loc, 1)), t1);
      case '!=': return Not(e.loc, BinOp(e.loc, Eq, t1, t2));
      case '&&': op = And; break;
      default:
        e.executionError("This binary operator is not yet supported in a proof outline");
    }
    return BinOp(e.loc, op, t1, t2);
  } else if (e instanceof UnaryOperatorExpression) {
    let op = null;
    switch (e.operator) {
      case 'not':
        return Not(e.loc, parseProofOutlineExpression(e.operand));
      default:
        e.executionError("This unary operator is not yet supported in a proof outline");
    }
  } else
    e.executionError("This expression form is not yet supported in a proof outline");
}

class JustificationScanner {
  constructor(comment) {
    this.comment = comment;
    this.text = this.comment.text;
    this.pos = -1;
    this.eat();
  }

  eat() {
    this.pos++;
    this.c = (this.pos == this.text.length ? "<EOF>" : this.text.charAt(this.pos));
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
    if (this.c == '<EOF>' || this.c == '#')
      return '<EOF>';
    if (isDigit(this.c)) {
      this.eat();
      while (isDigit(this.c))
        this.eat();
      const text = this.text.substring(this.tokenStart, this.pos);
      const value = +text;
      if (text != value.toString())
        this.error("Number too large");
      this.value = value;
      return '<NUMBER>';
    }
    if (isAlpha(this.c)) {
      this.eat();
      while (isAlpha(this.c))
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

  expect(token) {
    if (this.token != token)
      error(`'${token}' expected`);
    const value = this.value;
    this.nextToken();
    return value;
  }

  loc() {
    return this.comment.locFactory(this.comment.start + this.tokenStart, this.comment.start + this.pos);
  }

  error(msg) {
    throw new LocError(this.loc(), msg);
  }
}

function expectConjunctIndex(scanner) {
  const lk = scanner.loc();
  const k = scanner.expect('<NUMBER>');
  if (k == 0)
    throw new LocError(lk, "Conjunct index must be positive");
  return k - 1;
}

function parseJustification(scanner) {
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
      const lk1 = scanner.loc();
      const k1 = expectConjunctIndex(scanner);
      scanner.expect('in');
      const lk2 = scanner.loc();
      const k2 = expectConjunctIndex(scanner);
      return JRewrite(l, lk1, k1, lk2, k2);
    }
    default:
      if (has(laws, scanner.token)) {
        const l = scanner.loc();
        const lawName = scanner.token;
        scanner.nextToken();
        const ks = [];
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
        return JLaw(l, laws[lawName].law, ks.reduceRight((acc, [lk, k]) => LawAppIndicesCons(lk, k, acc), LawAppIndicesNil));
      }
      scanner.error("'Z' or 'Herschrijven' or law name expected");
  }
}

function parseJustifications(comment) {
  const scanner = new JustificationScanner(comment);
  scanner.nextToken();
  if (scanner.token == '<EOF>')
    return JustifNil;
  let result = JustifNil;
  for (;;) {
    const j = parseJustification(scanner);
    result = JustifCons(j, result);
    if (scanner.token != 'of')
      break;
    scanner.nextToken();
  }
  if (scanner.token != '<EOF>')
    scanner.error("End of justification expected");
  return result;
}

function parseProofOutline(stmts, i, precededByAssert) {
  if (stmts.length == i)
    return Pass(null);
  const stmt = stmts[i];
  if (stmt instanceof AssertStatement) {
    const body = parseProofOutlineExpression(stmt.condition);
    const justif = precededByAssert ? parseJustifications(stmt.comment) : JustifNil;
    return Seq(Assert(stmt.loc, body, justif), parseProofOutline(stmts, i + 1, true));
  } else if (stmt instanceof ExpressionStatement && stmt.expr instanceof AssignmentExpression && stmt.expr.op == '=' && stmt.expr.lhs instanceof VariableExpression) {
    return Seq(Assign(stmt.loc, stmt.expr.lhs.name, parseProofOutlineExpression(stmt.expr.rhs)), parseProofOutline(stmts, i + 1, false));
  } else if (stmt instanceof WhileStatement) {
    const cond = parseProofOutlineExpression(stmt.condition);
    if (!(stmt.body instanceof BlockStatement))
      stmt.body.executionError("In a proof outline, the body of a loop must be a block.");
    const body = parseProofOutline(stmt.body.stmts, 0, false);
    return Seq(While(stmt.loc, cond, body), parseProofOutline(stmts, i + 1, false));
  } else
    stmt.executionError("This statement form is not yet supported in a proof outline.");
}

function checkProofOutline(env, stmts) {
  const outline = parseProofOutline(stmts, 0, false);
  if (!stmt_is_well_typed(env, outline))
    throw new LocError(new Loc(stmts[0].loc.doc, stmts[0].loc.start, stmts[stmts.length - 1].loc.end), "Proof outline is not well-typed");
  const result = check_proof_outline(outline);
  if (!isOk(result))
    throw new LocError(getLoc(result), getMsg(result));
  nbProofOutlinesChecked++;
}

class BuiltInMethodDeclaration {
  constructor(paramNames, body) {
    this.parameterDeclarations = paramNames;
    this.body = body;
  }
  enter() {}
  check() {}
  async call(callExpr, args) {
    let result = await this.body(callExpr, args);
    push(new OperandBinding(callExpr, result));
  }
  checkProofOutlines() {}
}

class FieldDeclaration extends Declaration {
  constructor(loc, type, name) {
    super(loc);
    this.type = type;
    this.name = name;
  }

  enter() {
    this.type.resolve();
  }
}

class Class extends Declaration {
  constructor(loc, name, fields) {
    super(loc);
    this.name = name;
    this.type = new ClassType(this);
    this.fields = {};
    for (let field of fields) {
      if (has(this.fields, field.name))
        field.executionError("A field with this name already exists in this class");
      this.fields[field.name] = field;
    }
  }

  enter() {
    for (let field in this.fields)
      this.fields[field].enter();
  }
}

class Loc {
  constructor(doc, start, end) {
    this.doc = doc;
    this.start = start;
    this.end = end;
  }
}

function mkLocFactory(doc) {
  return (start, end) => new Loc(doc, start, end);
}

class LocError extends Error {
  constructor(loc, msg) {
    super();
    this.loc = loc;
    this.msg = msg;
  }
}

class ParseError extends LocError {
  constructor(loc, msg) {
    super(loc, msg);
  }
}

class ExecutionError extends LocError {
  constructor(loc, msg) {
    super(loc, msg);
  }
}

class Parser {
  constructor(locFactory, text, parseExpression, commentListener) {
    this.locFactory = locFactory;
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

  parseError(msg) {
    throw new ParseError(this.tokenLoc(), msg);
  }

  next() {
    this.lastValue = this.scanner.value;
    this.lastPos = this.scanner.pos;
    this.token = this.scanner.nextToken();
  }

  expect(token) {
    if (this.token != token)
      this.parseError((token == 'EOF' ? "end of input " : token) + " expected");
    this.next();
    return this.lastValue;
  }

  parsePrimaryExpression() {
    this.pushStart();
    switch (this.token) {
      case "NUMBER":
        this.next();
        return new IntLiteral(this.popLoc(), this.lastValue);
      case "IDENT":
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
        let type = this.tryParsePrimaryType();
        if (type == null)
          this.parseError("Type expected");
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
              throw new LocError(loc, "Mention either a length or an initializer; not both.");
            return new NewArrayExpression(loc, instrLoc, type, lengthExpr);
          } else {
            if (elementExpressions == null)
              throw new LocError(loc, "Mention either a length or an initializer");
            return new ListExpression(loc, instrLoc, type, elementExpressions);
          }
        }
        if (!(type instanceof ClassTypeExpression))
          throw new LocError(type.loc, "Class type expected");
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
      default:
        this.parseError("Number or identifier expected");
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
          let x = this.expect('IDENT');
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
          e = new CallExpression(this.dupLoc(), instrLoc, e, args);
          break;
        }
        case '[': {
          this.pushStart();
          this.next();
          let instrLoc = this.popLoc();
          let index = this.parseExpression();
          this.expect(']');
          e = new SubscriptExpression(this.dupLoc(), instrLoc, e, index);
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

  parseRelationalExpression() {
    this.pushStart();
    let e = this.parseAdditiveExpression();
    switch (this.token) {
      case '==':
      case '!=':
      case '<':
      case '<=':
      case '>':
      case '>=':
        this.pushStart();
        let op = this.token;
        this.next();
        let instrLoc = this.popLoc();
        let rhs = this.parseAdditiveExpression();
        return new BinaryOperatorExpression(this.popLoc(), instrLoc, e, op, rhs);
      default:
        this.popLoc();
        return e;
    }
  }
  
  parseConjunction() {
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
  
  parseDisjunction() {
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
  
  parseAssignmentExpression() {
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
        this.parseError("Type '" + this.token + "' is not (yet) supported by JLearner. Use type 'int'.");
      default:
        this.popLoc();
        return null;
    }
  }
  
  tryParseType() {
    this.pushStart();
    let type = this.tryParsePrimaryType();
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
      this.parseError("Type expected");
    return type;
  }

  parseSuite() {
    this.pushStart();
    this.expect('EOL');
    this.expect('INDENT');
    let stmts = this.parseStatements({'DEDENT': true});
    this.expect('DEDENT');
    return new BlockStatement(this.popLoc(), stmts);
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
        if (this.token == 'EOL')
          e = null;
        else
          e = this.parseExpression();
        this.expect('EOL');
        return new ReturnStatement(this.popLoc(), instrLoc, e);
      }
      case 'if': {
        this.pushStart();
        this.next();
        let instrLoc = this.popLoc();
        let condition = this.parseExpression();
        this.expect(':');
        let thenBody = this.parseSuite();
        let elseBody = null;
        if (this.token == 'else') {
          this.next();
          this.expect(':');
          elseBody = this.parseSuite();
        }
        return new IfStatement(this.popLoc(), instrLoc, condition, thenBody, elseBody);
      }
      case 'assert': {
        this.pushStart();
        this.next();
        let instrLoc = this.popLoc();
        let condition = this.parseExpression();
        const comment = this.expect('EOL');
        return new AssertStatement(this.popLoc(), instrLoc, condition, comment);
      }
    }
    let e = this.parseExpression();
    this.pushStart();
    this.expect("EOL");
    let instrLoc = this.popLoc();
    return new ExpressionStatement(this.popLoc(), instrLoc, e);
  }
  
  parseStatements(terminators) {
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
    let x = this.expect('IDENT');
    if (this.token == '(')
      this.parseError("Methods inside classes are not (yet) supported by JLearner. Instead, define the method outside the class.");
    if (this.token == '=')
      this.parseError("Field initializers are not (yet) supported by JLearner.");
    this.expect(';');
    return new FieldDeclaration(this.popLoc(), type, x);
  }
  
  parseDeclaration() {
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
        let name = this.expect('IDENT');
        let nameLoc = this.popLoc();
        this.expect('(');
        let parameters = [];
        if (this.token != ')') {
          for (;;) {
            this.pushStart();
            let paramType = new ImplicitTypeExpression();
            this.pushStart();
            let paramName = this.expect('IDENT');
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
    }
  }
  
  parseDeclarations() {
    let declarations = [];
    while (this.token != 'EOF')
      declarations.push(this.parseDeclaration());
    return declarations;
  }
}

function parseDeclarations(locFactory, text, parseComment) {
  const parser = new Parser(locFactory, text, false, parseComment);
  return parser.parseDeclarations();
}

function parseStatements(locFactory, text) {
  const parser = new Parser(locFactory, text);
  return parser.parseStatements({'EOF': true});
}

function parseExpression(locFactory, text) {
  const parser = new Parser(locFactory, text, true);
  const result = parser.parseExpression();
  parser.expect('EOF');
  return result;
}

let lastCheckedDeclarations = null;
let classes;
let toplevelMethods;
let lawComments;
let laws;

function checkDeclarations(declarations) {
  classes = {};
  toplevelMethods = {};
  toplevelMethods['len'] = new BuiltInMethodDeclaration(['l'], async (callExpr, args) => {
    let arg = args[0];
    if (!(arg instanceof ListObject))
      throw new LocError(callExpr.loc, "len expects a list object");
    return arg.length;
  });
  for (let declaration of declarations) {
    if (declaration instanceof Class) {
      if (has(classes, declaration.name))
        throw new LocError(declaration.loc, "A class with the same name already exists");
      classes[declaration.name] = declaration;
    } else {
      if (has(toplevelMethods, declaration.name))
        throw new LocError(declaration.loc, "A method with the same name already exists");
      toplevelMethods[declaration.name] = declaration;
    }
  }
  for (let c in classes)
    classes[c].enter();
  for (let m in toplevelMethods)
    toplevelMethods[m].enter();
  for (let m in toplevelMethods)
    toplevelMethods[m].check();
}

let toplevelScope;
let mainStackFrame;
let callStack;

function resetMachine() {
  toplevelScope = new Scope(null);
  mainStackFrame = new StackFrame("(toplevel)", toplevelScope);
  callStack = [mainStackFrame];
}

resetMachine();

function push(binding) {
  callStack[callStack.length - 1].operands.push(binding);
}

function peek(N) {
  let operands = callStack[callStack.length - 1].operands;
  let result = operands.slice(operands.length - N, operands.length);
  return result.map(binding => binding.value);
}

function pop(N) {
  let operands = callStack[callStack.length - 1].operands;
  let result = operands.slice(operands.length - N, operands.length);
  operands.length -= N;
  return result.map(binding => binding.value);
}

let callStackArrows = []

function createArrow(fromNode, toNode) {
  let svg = document.getElementById('arrows-svg');
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
  arrow.style = "stroke:rgb(0,0,0);stroke-width:1";
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
    arrow.arrow.parentNode.removeChild(arrow.arrow);
    arrow.arrow = createArrow(arrow.fromNode, arrow.toNode);
  }
}

function updateArrows() {
  updateStackArrows();
  updateFieldArrows();
}

function updateCallStack() {
  for (let arrow of callStackArrows)
    arrow.arrow.parentNode.removeChild(arrow.arrow);
  callStackArrows = [];
  
  let callStackTable = document.getElementById('callstack');
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

let nbProofOutlinesChecked;

class LawInfo {
  constructor(comment, name, law) {
    this.comment = comment;
    this.name = name;
    this.law = law;
  }
}

function checkLaws() {
  laws = {};
  for (const comment of lawComments) {
    const text = comment.text;
    const wetIndex = text.indexOf('Wet');
    const colonIndex = text.indexOf(':', wetIndex + 3);
    if (colonIndex < 0)
      throw new LocError(comment.loc(), "Law must be of the form 'Wet NAME: PREMISES ==> CONCLUSION'");
    const name = text.slice(wetIndex + 3, colonIndex).trim();
    const implication = text.substring(colonIndex + 1);
    const arrowIndex = implication.indexOf('==>');
    if (arrowIndex < 0)
      throw new LocError(comment.loc(), "Law must be of the form 'Wet NAME: PREMISES ==> CONCLUSION'");
    const premiseText = implication.slice(0, arrowIndex);
    const premisePos = comment.start + colonIndex + 1;
    const premise = parseExpression((start, end) => comment.locFactory(premisePos + start, premisePos + end), premiseText);
    const conclusionText = implication.substring(arrowIndex + 3);
    const conclusionPos = premisePos + arrowIndex + 3
    const conclusion = parseExpression((start, end) => comment.locFactory(conclusionPos + start, conclusionPos + end), conclusionText);
    const scope = new Scope(null, true);
    premise.checkAgainst(scope, booleanType);
    conclusion.checkAgainst(scope, booleanType);
    laws[name] = new LawInfo(comment, name, Law(parseProofOutlineExpression(premise), parseProofOutlineExpression(conclusion)));
  }
}

function checkProofOutlines() {
  handleError(async () => {
    parseDeclarationsBox();
    checkLaws();
    nbProofOutlinesChecked = 0;
    for (let m in toplevelMethods)
      toplevelMethods[m].checkProofOutlines();
    alert(`${nbProofOutlinesChecked} proof outlines checked successfully!`);
  });
}

async function executeStatements(step) {
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

function getTextCoordsFromOffset(text, offset) {
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

let errorWidgets = [];

function clearErrorWidgets() {
  for (let widget of errorWidgets)
    widget.clear();
  errorWidgets = [];
}

function addErrorWidget(editor, line, msg) {
  var widget = document.createElement("div");
  var icon = widget.appendChild(document.createElement("span"));
  icon.innerHTML = "!";
  icon.className = "lint-error-icon";
  widget.appendChild(document.createTextNode(msg));
  widget.className = "lint-error";
  errorWidgets.push(editor.addLineWidget(line, widget, {coverGutter: false, noHScroll: true}));
}

async function handleError(body) {
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
      }
    } else {
      alert(ex);
    }
  }
}

function processComment(comment) {
  if (comment.isOnNewLine && comment.text.trim().startsWith('Wet '))
    lawComments.push(comment);
}

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

class SyntheticVariableBinding {
  constructor(name, value) {
    this.name = name;
    this.value = value;
  }

  getNameHTML() {
    return this.name;
  }
}

let syntheticVariableCount = 0;

async function evaluateExpression(step) {
  await handleError(async () => {
    parseDeclarationsBox();
    let exprText = expressionEditor.getValue();
    let e = parseExpression(mkLocFactory(expressionEditor), exprText);
    //e.check_(toplevelScope);
    currentBreakCondition = () => step;
    await e.evaluate(toplevelScope);
    let [v] = pop(1);
    let valueText;
    if (e.type instanceof ReferenceType) {
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

function markLoc(loc, className) {
  let text = loc.doc.getValue();
  return loc.doc.markText(getTextCoordsFromOffset(text, loc.start), getTextCoordsFromOffset(text, loc.end), {className});
}

let currentNode = null;
let currentBreakCondition = null;
let currentInstructionMark = null;
let resumeFunc = null;

function checkBreakpoint(node) {
  return new Promise((resolve, reject) => {
    if (currentBreakCondition(node)) {
      currentNode = node;
      currentBreakCondition = null;
      currentInstructionMark = markLoc(node.instrLoc, "current-instruction");
      resumeFunc = () => {
        currentNode = null;
        currentInstructionMark.clear();
        resolve();
      };
      updateMachineView();
    } else {
      resolve();
    }
  });
}

function resume() {
  let f = resumeFunc;
  resumeFunc = null;
  f();
}

function isDifferentLine(loc1, loc2) {
  if (loc1.doc != loc2.doc)
    return true;
  let text = loc1.doc.getValue();
  let coords1 = getTextCoordsFromOffset(text, loc1.start);
  let coords2 = getTextCoordsFromOffset(text, loc2.start);
  return coords1.line != coords2.line;
}

function step() {
  let oldNode = currentNode;
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
  let oldNode = currentNode;
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
  document.getElementById('executeButton').disabled = stepping;
  document.getElementById('resetAndExecuteButton').disabled = stepping;
  document.getElementById('stepThroughStatementsButton').disabled = stepping;
  document.getElementById('evaluateButton').disabled = stepping;
  document.getElementById('stepThroughExpressionButton').disabled = stepping;

  document.getElementById('stepButton').disabled = !stepping;
  document.getElementById('smallStepButton').disabled = !stepping;
  document.getElementById('stepOverButton').disabled = !stepping;
  document.getElementById('stepOutButton').disabled = !stepping;
  document.getElementById('continueButton').disabled = !stepping;
}

examples = [{
  title: 'Copy a number (partial correctness)',
  declarations:
`def copy(n):

    assert True # PRECONDITION PARTIAL_CORRECTNESS
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
    assert r == n # Z op 1 # POSTCONDITION

    return r
`,
  statements:
`assert copy(2) == 2
assert copy(7) == 7`,
  expression: `copy(3)`
}, {
  title: 'Copy a number (alternative) (partial correctness)',
  declarations:
`# Wet LeAntisym: x <= y and y <= x ==> x == y

def copy(n):

    assert 0 <= n # PRECONDITION PARTIAL_CORRECTNESS
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
    assert r == n # Z op 1 # POSTCONDITION

    return r
`,
  statements:
`assert copy(2) == 2
assert copy(7) == 7`,
  expression: `copy(3)`
}, {
  title: 'Copy a number (total correctness)',
  declarations:
`# Wet LeAntisym: x <= y and y <= x ==> x == y

def copy(n):

    assert 0 <= n # PRE CONDITION TOTAL_CORRECTNESS
    assert 0 <= n and 0 == n - n # Z
    i = n
    assert 0 <= i and 0 == n - i
    r = 0
    assert 0 <= i and r == n - i
    while 0 < i:
        oude_variant = i
        assert 0 <= i and r == n - i and 0 < i and i == oude_variant
        assert 0 < i and r + 1 == n - (i - 1) and i == oude_variant # Z op 2
        #assert r + 1 == n - (i - 1) and 0 <= i - 1 < oude_variant # Z op 1 of Z op 2
        i = i - 1
        #assert r + 1 == n - i and 0 <= i < oude_variant
        r = r + 1
        #assert r == n - i and 0 <= i < oude_variant
        #assert 0 <= i and r == n - i and 0 <= i < oude_variant
    assert 0 <= i and r == n - i and not 0 < i
    assert 0 <= i and r == n - i and i <= 0 # Z op 3
    assert r == n - i and 0 == i # LeAntisym op 1 en 3
    assert r == n - 0 # Herschrijven met 2 in 1
    assert r == n # Z op 1 # POST CONDITION

    return r
`,
  statements:
`assert copy(2) == 2
assert copy(7) == 7`,
  expression: `copy(3)`
}, {
  title: 'Faculty',
  declarations:
`# precondition: x is positive
def fac(x):
    if x == 1:
        return 1
    else:
        return x * fac(x - 1)
`,
  statements:
`assert fac(2) == 2
assert fac(4) == 24`,
  expression: `fac(3)`
}, {
  title: 'Find an element in a list',
  declarations:
`#def find(haystack, needle):
#    index = 0
#    while True:
#        if index == len(haystack):
#            return -1
#        if haystack[index] == needle:
#            return index
#        index += 1
`,
  statements:
`#numbers = [3, 13, 7, 2]
#assert find(numbers, 13) == 1
#assert find(numbers, 8) == -1`,
  expression: '' //'find(numbers, 7)'
}, {
  title: 'Bubblesort',
  declarations:
`#def bubblesort(list):
#    todo = len(list)
#    while todo > 1:
#        index = 1
#        while index < todo:
#            if list[index - 1] > list[index]:
#                tmp = list[index - 1]
#                list[index - 1] = list[index]
#                list[index] = tmp
#            index += 1
#        todo -= 1
`,
  statements:
`#numbers1 = [40, 10, 30, 20]
#numbers2 = numbers1
#numbers3 = [40, 10, 30, 20]
#bubblesort(numbers1)`,
  expression: ''
}
]

function setExample(example) {
  reset();
  declarationsEditor.setValue(example.declarations || "");
  statementsEditor.setValue(example.statements || "");
  expressionEditor.setValue(example.expression || "");
}

function initExamples() {
  setExample(examples[0]);

  let examplesNode = document.getElementById('examples');
examplesNode.onchange = event => { if (event.target.selectedOptions.length > 0) event.target.selectedOptions[0].my_onselected(); };
  for (let example of examples) {
    let exampleOption = document.createElement('option');
    examplesNode.appendChild(exampleOption);
    exampleOption.innerText = example.title;
    exampleOption.my_onselected = () => setExample(example);
  }
}

async function testPyLearner() {
  currentBreakCondition = () => false;
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
  console.log('All tests passed!');
}

if (typeof window === 'undefined') // We're being executed by Node.js.
  testPyLearner();