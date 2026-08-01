// -*- js-indent-level: 2 -*-
/*
  PyFoma → JavaScript (port)
  -------------------------
  Core finite-state toolkit in plain JS.

  Notes:
  - Labels are arrays of strings, e.g. ["a"] for acceptor, ["a","b"] for transducer.
  - Epsilon is the empty string "".
*/

// ------------------------
// Small utilities
// ------------------------

const LABEL_SEP = "\u0001";
type labelArray = string[];

export function labelKey(lbl: labelArray): string {
  return lbl.join(LABEL_SEP);
}

export function keyToLabel(k: string): labelArray {
  return k === "" ? [""] : k.split(LABEL_SEP);
}

function setUnion<T>(a: Set<T>, b: Set<T>): Set<T> {
  const out = new Set(a);
  for (const x of b) out.add(x);
  return out;
}

function setIntersection<T>(a: Set<T>, b: Set<T>): Set<T> {
  const out = new Set<T>();
  for (const x of a) if (b.has(x)) out.add(x);
  return out;
}

function setDifference<T>(a: Set<T>, b: Set<T>): Set<T> {
  const out = new Set<T>();
  for (const x of a) if (!b.has(x)) out.add(x);
  return out;
}

// @ts-ignore
function* cartesian<T, U>(a: Iterable<T>, b: Iterable<U>): Generator<[T, U]> {
  for (const x of a) for (const y of b) yield [x, y];
}

// A tiny counter helper
class Counter {
  v: number;
  constructor(start = 0) { this.v = start; }
  next(): number { return this.v++; }
}

// Min-heap priority queue
export class MinHeap<T> {
  data: [number, T][];
  constructor() { this.data = []; }
  get size(): number { return this.data.length; }
  push(item: [number, T]): void {
    const a = this.data;
    a.push(item);
    let i = a.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (a[p][0] <= a[i][0]) break;
      [a[p], a[i]] = [a[i], a[p]];
      i = p;
    }
  }
  pop(): [number, T] | undefined {
    const a = this.data;
    if (a.length == 0)
      return undefined;
    const top = a[0];
    const last: [number,  T] = a.pop()!;
    if (a.length) {
      a[0] = last;
      let i = 0;
      while (true) {
        const l = 2 * i + 1;
        const r = l + 1;
        let m = i;
        if (l < a.length && a[l][0] < a[m][0]) m = l;
        if (r < a.length && a[r][0] < a[m][0]) m = r;
        if (m === i) break;
        [a[m], a[i]] = [a[i], a[m]];
        i = m;
      }
    }
    return top;
  }
}

function floatInf(): number { return Number.POSITIVE_INFINITY; }

// ------------------------
// Core data structures
// ------------------------

export class Transition {
  targetstate: State;
  label: labelArray;
  weight: number;
  constructor(targetstate: State, label: labelArray, weight: number) {
    this.targetstate = targetstate;
    this.label = label;
    this.weight = weight;
  }
}

export class State {
  transitions: Map<string, {label: labelArray, set: Set<Transition>}>;
  _transitionsin: Map<string, Set<[labelArray, Transition]>> | null;
  _transitionsout: Map<string, Set<[labelArray, Transition]>> | null;
  finalweight: number;
  name: string | null;
  _id?: number;

  constructor({ finalweight = floatInf(), name = null }:
              {finalweight?: number, name?: string | null} = {}) {
    this.transitions = new Map();
    this._transitionsin = null;
    this._transitionsout = null;
    this.finalweight = finalweight;
    this.name = name;
  }

  _invalidateIndexes() {
    this._transitionsin = null;
    this._transitionsout = null;
  }

  // Build input-index lazily
  get transitionsin() {
    if (this._transitionsin !== null) return this._transitionsin;
    const m = new Map(); // sym -> Set<[labelArray, Transition]>
    for (const { label, set } of this.transitions.values()) {
      const insym = label[0];
      if (!m.has(insym)) m.set(insym, new Set());
      const bucket = m.get(insym);
      for (const t of set) bucket.add([label, t]);
    }
    this._transitionsin = m;
    return m;
  }

  // Build output-index lazily
  get transitionsout() {
    if (this._transitionsout !== null) return this._transitionsout;
    const m = new Map();
    for (const { label, set } of this.transitions.values()) {
      const outsym = label[label.length - 1];
      if (!m.has(outsym)) m.set(outsym, new Set());
      const bucket = m.get(outsym);
      for (const t of set) bucket.add([label, t]);
    }
    this._transitionsout = m;
    return m;
  }

  renameLabel(originalLabel: labelArray, newLabel: labelArray): void {
    const ok = labelKey(originalLabel);
    const entry = this.transitions.get(ok);
    if (!entry) return;
    const nk = labelKey(newLabel);
    for (const t of entry.set) t.label = newLabel;
    if (!this.transitions.has(nk)) this.transitions.set(nk, { label: newLabel, set: new Set() });
    const target = this.transitions.get(nk)!.set;
    if (!target) return;
    for (const t of entry.set) target.add(t);
    this.transitions.delete(ok);
    // Deduplicate merged label bucket
    const dedup = new Map();
    for (const t of target) {
      const prev = dedup.get(t.targetstate);
      if (!prev || t.weight < prev.weight) dedup.set(t.targetstate, t);
    }
    this.transitions.get(nk)!.set = new Set(dedup.values());
    this._invalidateIndexes();
  }

  removeTransitionsToTargets(targets: Set<State>): void {
    const newMap = new Map();
    for (const [k, { label, set }] of this.transitions.entries()) {
      const kept = new Set();
      for (const t of set) if (!targets.has(t.targetstate)) kept.add(t);
      if (kept.size) newMap.set(k, { label, set: kept });
    }
    this.transitions = newMap;
    this._invalidateIndexes();
  }

  addTransition(other: State, label: labelArray, weight: number): void {
    const k = labelKey(label);
    if (!this.transitions.has(k)) this.transitions.set(k, { label, set: new Set() });
    const entry = this.transitions.get(k)!;

    // Deduplicate parallel arcs with identical label and target: keep cheapest weight.
    for (const t of entry.set) {
      if (t.targetstate === other) {
        t.weight = Math.min(t.weight, weight);
        this._invalidateIndexes();
        return;
      }
    }

    entry.set.add(new Transition(other, label, weight));
    this._invalidateIndexes();
  }

  *allTransitions(): Generator<[labelArray, Transition]> {
    for (const { label, set } of this.transitions.values()) {
      for (const t of set) yield [label, t];
    }
  }

  allTargets(): Set<State> {
    const out = new Set<State>();
    for (const { set } of this.transitions.values()) for (const t of set) out.add(t.targetstate);
    return out;
  }

  allEpsilonTargetsCheapest(): Map<State, number> {
    const targets = new Map();
    for (const [k, { set }] of this.transitions.entries()) {
      const isEps = (k === "");
      if (!isEps) continue;
      for (const t of set) {
        const prev = targets.has(t.targetstate) ? targets.get(t.targetstate) : floatInf();
        targets.set(t.targetstate, Math.min(prev, t.weight));
      }
    }
    return targets;
  }

  allTargetsCheapest(): Map<State, number> {
    const targets = new Map();
    for (const { set } of this.transitions.values()) {
      for (const t of set) {
        const prev = targets.has(t.targetstate) ? targets.get(t.targetstate) : floatInf();
        targets.set(t.targetstate, Math.min(prev, t.weight));
      }
    }
    return targets;
  }
}

// ------------------------
// Partition refinement
// ------------------------

export class PartitionRefinement<T> {
  sets: Map<Set<T>, Set<T>>;
  partition: Map<T, Set<T>>;
  constructor(S: Set<Set<T>>) {
    this.sets = new Map();
    this.partition = new Map();
    for (const s of S) {
      this.sets.set(s, s);
      for (const x of s) this.partition.set(x, s);
    }
  }

  refine(S: Set<T>): [Set<T>, Set<T>][] {
    const hit = new Map();
    for (const x of S) {
      if (!this.partition.has(x)) continue;
      const Ax = this.partition.get(x);
      if (!hit.has(Ax)) hit.set(Ax, new Set());
      hit.get(Ax).add(x);
    }
    const output: [Set<T>, Set<T>][] = [];
    for (const [A, AS] of hit.entries()) {
      if (AS.size === A.size) continue;
      // Create new set AS; keep A as A- AS
      this.sets.set(AS, AS);
      for (const x of AS) this.partition.set(x, AS);
      for (const x of AS) A.delete(x);
      output.push([AS, A]);
    }
    return output;
  }

  asTuples(): Set<T[]> {
    const out: Set<T[]> = new Set();
    for (const s of this.sets.values()) out.add(Array.from(s));
    return out;
  }
}

// ------------------------------------------------------------------------
// Regex compiler (shunting-yard + Thompson-style construction)
// ------------------------------------------------------------------------

type FunctionObject = {name: string, fn: Function};
type Token = [string, any, number, number];
type DefinedMapping = {[name: string]: FST};
type FunctionMapping = {[name: string]: Function};
type FunctionSet = Set<Function | FunctionObject>;
type FinalFFunction = (x: [boolean, boolean]) => boolean;
type OPlusFunction = (x: number, y: number) => number;
type PathFollowFunction = (x: Set<string>, y: Set<string>) => Set<string>;
type ModLabelFunction = (lbl: labelArray, w: number) => labelArray;
type ModWeightFunction = (lbl: labelArray, w: number) => number;
type StateRepFunction = (s: State, w: number) => [State, number];

export class RegexParse {
  static shortops: {[op: string]: string} = {
    "|": "UNION",
    "-": "MINUS",
    "&": "INTERSECTION",
    "*": "STAR",
    "+": "PLUS",
    "(": "LPAREN",
    ")": "RPAREN",
    "?": "OPTIONAL",
    ":": "CP",
    ":?": "CPOPTIONAL",
    "~": "COMPLEMENT",
    "@": "COMPOSE",
    ",": "COMMA",
    "/": "CONTEXT",
    "_": "PAIRUP",
  };

  static builtins: {[name: string]: Function} = {
    reverse: (x: FST) => x.copyMod().reverse(),
    invert: (x: FST) => x.copyMod().invert(),
    minimize: (x: FST) => x.copyMod().minimize(),
    determinize: (x: FST) => x.copyMod().determinize(),
    ignore: (x: FST, y: FST) => x.copyMod().ignore(y),
    rewrite: (...args: FST[]) => args[0].copyMod().rewrite(...args.slice(1)),
    restrict: (x: FST, ...args: FST[]) => x.copyMod().contextRestrict(...args),
    project: (x: FST, kwargs: {[key: string]: any} = {}) => x.copyMod().project(parseInt(kwargs.dim ?? "-1", 10)),
    input: (x: FST) => x.copyMod().project(0),
    output: (x: FST) => x.copyMod().project(-1),
  };

  static precedence: {[op: string]: number} = {
    FUNC: 11,
    COMMA: 1,
    PARAM: 1,
    COMPOSE: 3,
    UNION: 5,
    INTERSECTION: 5,
    MINUS: 5,
    CONCAT: 6,
    STAR: 9,
    PLUS: 9,
    OPTIONAL: 9,
    WEIGHT: 9,
    CP: 10,
    CPOPTIONAL: 10,
    RANGE: 9,
    CONTEXT: 1,
    PAIRUP: 2,
    COMPLEMENT: 9,
  };

  static operands = new Set(["SYMBOL", "VARIABLE", "ANY", "EPSILON", "CHAR_CLASS"]);
  static operators = new Set(Object.keys(RegexParse.precedence));
  static unarypost = new Set(["STAR", "PLUS", "WEIGHT", "OPTIONAL", "RANGE"]);
  static unarypre = new Set(["COMPLEMENT"]);

  expression: string;
  defined: DefinedMapping;
  functions: FunctionMapping;
  tokenized: Token[];
  parsed: Token[];
  compiled: FST;

  constructor(regExp: string, defined: {[name: string]: FST}, functions: FunctionSet) {
    this.defined = defined;
    this.functions = {};
    // Custom functions are passed in as an iterable. We accept either:
    //   - a callable function (uses f.name)
    //   - an object { name: string, fn: function }
    for (const f of functions) {
      if (typeof f === 'function') {
        if (!f.name) continue;
        this.functions[f.name] = f;
      } else if (f && typeof f === 'object' && typeof f.name === 'string' && typeof f.fn === 'function') {
        this.functions[f.name] = f.fn;
      }
    }
    this.expression = regExp;
    this.tokenized = this._insertInvisibles(this.tokenize());
    this.parsed = this.parse();
    this.compiled = this.compile();
  }

  _errorReport(ErrorType: ErrorConstructor, message: string, lineNum: number, column: number): never {
    const e = new ErrorType(message);
    // @ts-ignore
    e.lineNum = lineNum;
    // @ts-ignore
    e.column = column;
    // @ts-ignore
    e.expression = this.expression;
    throw e;
  }

  characterClassParse(charclass: string): [[number, number][], boolean] {
    let negated = false;
    if (charclass.startsWith("^")) {
      negated = true;
      charclass = charclass.slice(1);
    }

    const cln = [];
    const escaped = new Set();
    let j = 0;
    for (let i = 0; i < charclass.length; i++) {
      const ch = charclass[i];
      if (ch !== "\\") {
        cln.push(ch);
        j += 1;
      } else {
        escaped.add(j);
      }
    }

    const marks = cln.map((c, i) => c === "-" && !escaped.has(i) && i !== 0 && i !== cln.length - 1);
    const ranges: [number, number][] = [];
    for (let i = 0; i < marks.length; i++) {
      // FIXME: This is broken for surrogate pairs
      if (marks[i]) ranges.push([cln[i - 1].codePointAt(0)!, cln[i + 1].codePointAt(0)!]);
    }

    // singles are those not participating in ranges
    const singles = [];
    for (let i = 0; i < marks.length; i++) {
      const m0 = marks[i];
      const m1 = (i + 1 < marks.length) ? marks[i + 1] : false;
      const m_1 = (i - 1 >= 0) ? marks[i - 1] : false;
      singles.push(m0 || m1 || m_1);
    }
    for (let i = 0; i < singles.length; i++) {
      if (!singles[i]) {
        const cp = cln[i].codePointAt(0);
        // FIXME: This is broken for surrogate pairs
        ranges.push([cp!, cp!]);
      }
    }

    for (const [start, end] of ranges) {
      if (start > end) throw new SyntaxError("End must be larger than start in character class range.");
    }
    return [ranges, negated];
  }

  tokenize(): Token[] {
    // JS doesn't support Python's (?P<name>) groups; we implement sequential scanning.
    // We mimic the token list in pyfoma.py.
    const s = this.expression;
    const tokens: Token[] = [];
    let i = 0;
    let lineNum = 1;
    let lineStart = 0;

    const pushTok = (op: string, value: any, startIdx: number) => {
      const col = startIdx - lineStart;
      tokens.push([op, value, lineNum, col]);
    };

    while (i < s.length) {
      const ch = s[i];

      if (ch === "\n") {
        lineNum += 1;
        i += 1;
        lineStart = i;
        continue;
      }

      // whitespace
      if (ch === " " || ch === "\t") {
        i += 1;
        continue;
      }

      // escaped symbol \\.
      if (ch === "\\") {
        if (i + 1 >= s.length) this._errorReport(SyntaxError, "Dangling escape", lineNum, i - lineStart);
        pushTok("SYMBOL", s[i + 1], i);
        i += 2;
        continue;
      }

      // parameter: , key = value (only after comma)
      if (ch === ",") {
        // Try PARAM: , *\w+ *= *[+-]? *\w+
        const m = s.slice(i).match(/^,\s*(\w+)\s*=\s*([+-]?\s*\w+)/);
        if (m) {
          pushTok("PARAM", [m[1], m[2].replace(/\s+/g, "")], i);
          i += m[0].length;
          continue;
        }
        pushTok("COMMA", ",", i);
        i += 1;
        continue;
      }

      // quoted symbol '...'
      if (ch === "'") {
        const start = i;
        i += 1;
        let buf = "";
        while (i < s.length) {
          const c = s[i];
          if (c === "\\" && i + 1 < s.length && s[i + 1] === "'") {
            buf += "'";
            i += 2;
            continue;
          }
          if (c === "'") {
            i += 1;
            break;
          }
          buf += c;
          i += 1;
        }
        pushTok("SYMBOL", buf.replace(/\\/g, ""), start);
        continue;
      }

      // function $^name(...)
      if (ch === "$" && s[i + 1] === "^") {
        const start = i;
        const m = s.slice(i).match(/^\$\^(\w+)/);
        if (!m) this._errorReport(SyntaxError, "Bad function", lineNum, i - lineStart);
        const name = m[1];
        // Require lookahead for '(' like python. We'll allow optional ws.
        const rest = s.slice(i + m[0].length);
        if (!rest.match(/^\s*\(/)) this._errorReport(SyntaxError, "Function must be followed by ()", lineNum, i - lineStart);
        pushTok("FUNC", name, start);
        i += m[0].length;
        continue;
      }

      // variable $name
      if (ch === "$" && s[i + 1] !== "^") {
        const start = i;
        const m = s.slice(i).match(/^\$(\w+)/);
        if (!m) this._errorReport(SyntaxError, "Bad variable", lineNum, i - lineStart);
        pushTok("VARIABLE", m[1], start);
        i += m[0].length;
        continue;
      }

      // weight <num>
      if (ch === "<") {
        const start = i;
        const m = s.slice(i).match(/^<([+-]?[0-9]*(?:\.[0-9]+)?)>/);
        if (!m) this._errorReport(SyntaxError, "Bad weight", lineNum, i - lineStart);
        pushTok("WEIGHT", m[1], start);
        i += m[0].length;
        continue;
      }

      // range {m,n}
      if (ch === "{") {
        const start = i;
        const m = s.slice(i).match(/^\{(\d+,\d+|\d+,|,\d+|\d+)\}/);
        if (!m) this._errorReport(SyntaxError, "Bad range", lineNum, i - lineStart);
        pushTok("RANGE", m[1], start);
        i += m[0].length;
        continue;
      }

      // char class [ ... ]
      if (ch === "[") {
        const start = i;
        i += 1;
        let buf = "";
        while (i < s.length) {
          const c = s[i];
          if (c === "\\" && i + 1 < s.length && s[i + 1] === "]") {
            buf += "]";
            i += 2;
            continue;
          }
          if (c === "]") {
            i += 1;
            break;
          }
          buf += c;
          i += 1;
        }
        pushTok("CHAR_CLASS", buf, start);
        continue;
      }

      // short ops, including :?
      const two = s.slice(i, i + 2);
      if (two === ":?") {
        pushTok("CPOPTIONAL", ":?", i);
        i += 2;
        continue;
      }
      if (Object.prototype.hasOwnProperty.call(RegexParse.shortops, ch)) {
        const op = RegexParse.shortops[ch];
        pushTok(op, ch, i);
        i += 1;
        continue;
      }

      // any '.' is treated specially, but tokenizer labels it as SYMBOL and compile maps ANY.
      pushTok("SYMBOL", ch, i);
      i += 1;
    }

    // Convert '.' symbol to ANY token (like pyfoma's ANY in compile)
    return tokens.map(([op, value, ln, col]) => {
      if (op === "SYMBOL" && value === ".") return ["ANY", value, ln, col];
      return [op, value, ln, col];
    });
  }

  _insertInvisibles(tokens: Token[]): Token[] {
    const resetters = new Set([...RegexParse.operators].filter((x) => !RegexParse.unarypost.has(x)));
    let counter = 0;
    const result: Token[] = [];
    for (const [token, value, ln, col] of tokens) {
      if (counter === 1 && (token === "LPAREN" || token === "COMPLEMENT" || token === "FUNC" || RegexParse.operands.has(token))) {

        result.push(["CONCAT", "", ln, col]);
        counter = 0;
      }
      if (RegexParse.operands.has(token)) counter = 1;
      if (resetters.has(token)) counter = 0;
      result.push([token, value, ln, col]);
    }

    // epsilon insertion hack for rewrite/restrict contexts
    const newresult: Token[] = [];
    let prevt = null;
    for (const tok of result) {
      const [token, _value, ln, col] = tok;
      if (((token === "COMMA" || token === "PARAM") && prevt === "PAIRUP") ||
          (token === "PAIRUP" && (prevt === "CONTEXT" || prevt === "COMMA")) ||
          (token === "RPAREN" && prevt === "PAIRUP")) {
        newresult.push(["SYMBOL", "", ln, col]);
      }
      newresult.push(tok);
      prevt = token;
    }
    return newresult;
  }

  parse(): Token[] {
    const output: Token[] = [];
    const stack: Token[] = [];
    for (const [token, value, ln, col] of this.tokenized) {
      if (RegexParse.operands.has(token) || RegexParse.unarypost.has(token)) {
        output.push([token, value, ln, col]);
      } else if (RegexParse.unarypre.has(token) || token === "FUNC" || token === "LPAREN") {
        stack.push([token, value, ln, col]);
      } else if (token === "RPAREN") {
        while (true) {
          if (!stack.length) this._errorReport(SyntaxError, "Too many closing parentheses.", ln, col);
          if (stack[stack.length - 1][0] === "LPAREN") break;
          output.push(stack.pop()!);
        }
        stack.pop();
        if (stack.length && stack[stack.length - 1][0] === "FUNC") output.push(stack.pop()!);
      } else if (RegexParse.operators.has(token)) {
        while (stack.length && RegexParse.operators.has(stack[stack.length - 1][0]) &&
               RegexParse.precedence[stack[stack.length - 1][0]] >= RegexParse.precedence[token]) {
          output.push(stack.pop()!);
        }
        stack.push([token, value, ln, col]);
      }
    }
    while (stack.length) output.push(stack.pop()!);
    return output;
  }

  compile(): FST {
    const stack: any[] = [];
    let parameterStack = [];

    const stackCheck = (s: any[], ln: number, col: number) => {
      if (!s.length) this._errorReport(SyntaxError, "You stopped making sense!", ln, col);
      return s;
    };
    const pop1 = (ln: number, col: number) => stackCheck(stack, ln, col).pop()![0];
    const peek = (ln: number, col: number) => stackCheck(stack, ln, col)[stack.length - 1][0];
    const append = (elem: any) => { stack.push([elem]); };
    const merge = (ln: number, col: number) => {
      stackCheck(stack, ln, col);
      const one = stack.pop();
      stackCheck(stack, ln, col);
      stack.push(stack.pop().concat(one));
    };
    const pairup = (ln: number, col: number) => {
      stackCheck(stack, ln, col);
      const one = stack.pop();
      stackCheck(stack, ln, col);
      stack.push([tuple(stack.pop().concat(one))]);
    };
    const getArgs = (ln: number, col: number) => stackCheck(stack, ln, col).pop();

    const tuple = (arr: any) => arr; // JS: represent tuples as arrays

    for (const [op, value, ln, col] of this.parsed) {
      if (op === "FUNC") {
        const kwargs = Object.fromEntries(parameterStack);
        parameterStack = [];
        const args = getArgs(ln, col);
        if (Object.prototype.hasOwnProperty.call(this.functions, value)) {
          append(this.functions[value](...args, kwargs));
        } else if (Object.prototype.hasOwnProperty.call(RegexParse.builtins, value)) {
          append(RegexParse.builtins[value](...args, kwargs));
        } else {
          this._errorReport(SyntaxError, `Function \"${value}\" not defined.`, ln, col);
        }
      } else if (op === "LPAREN") {
        this._errorReport(SyntaxError, "Missing closing parenthesis.", ln, col);
      } else if (op === "COMMA") {
        merge(ln, col);
      } else if (op === "PARAM") {
        parameterStack.push(value);
      } else if (op === "PAIRUP") {
        pairup(ln, col);
      } else if (op === "CONTEXT") {
        merge(ln, col);
      } else if (op === "UNION") {
        const b = pop1(ln, col);
        const a = pop1(ln, col);
        append(a.union(b));
      } else if (op === "MINUS") {
        const b = pop1(ln, col);
        const a = pop1(ln, col);
        append(a.difference(b.determinizeUnweighted()));
      } else if (op === "INTERSECTION") {
        const b = pop1(ln, col);
        const a = pop1(ln, col);
        append(a.intersection(b).coaccessible());
      } else if (op === "CONCAT") {
        const b = pop1(ln, col);
        const a = pop1(ln, col);
        append(a.concatenate(b).accessible());
      } else if (op === "STAR") {
        const a = pop1(ln, col);
        append(a.kleeneClosure());
      } else if (op === "PLUS") {
        const a = pop1(ln, col);
        append(a.kleeneClosure("plus"));
      } else if (op === "COMPOSE") {
        const b = pop1(ln, col);
        const a = pop1(ln, col);
        append(a.compose(b).coaccessible());
      } else if (op === "OPTIONAL") {
        peek(ln, col).optional();
      } else if (op === "RANGE") {
        const rng = value.split(",");
        const lang = pop1(ln, col);
        if (rng.length === 1) {
          let out = null;
          for (let k = 0; k < parseInt(value, 10); k++) out = out ? out.concatenate(lang.copyMod()) : lang.copyMod();
          append(out ?? FST.fromLabel([""]));
        } else if (rng[0] === "") {
          const opt = lang.copyMod().optional();
          let out = null;
          for (let k = 0; k < parseInt(rng[1], 10); k++) out = out ? out.concatenate(opt.copyMod()) : opt.copyMod();
          append(out ?? FST.fromLabel([""]));
        } else if (rng[1] === "") {
          let out = null;
          for (let k = 0; k < parseInt(rng[0], 10); k++) out = out ? out.concatenate(lang.copyMod()) : lang.copyMod();
          append(out.concatenate(lang.copyMod().kleeneClosure()));
        } else {
          const m = parseInt(rng[0], 10);
          const n = parseInt(rng[1], 10);
          if (m > n) this._errorReport(SyntaxError, "n must be greater than m in {m,n}", ln, col);
          let lang1 = null;
          for (let k = 0; k < m; k++) lang1 = lang1 ? lang1.concatenate(lang.copyMod()) : lang.copyMod();
          let lang2 = null;
          for (let k = 0; k < n - m; k++) lang2 = lang2 ? lang2.concatenate(lang.copyMod().optional()) : lang.copyMod().optional();
          append(lang1.concatenate(lang2));
        }
      } else if (op === "CP") {
        const b = pop1(ln, col);
        const a = pop1(ln, col);
        append(a.crossProduct(b, false).coaccessible());
      } else if (op === "CPOPTIONAL") {
        const b = pop1(ln, col);
        const a = pop1(ln, col);
        append(a.crossProduct(b, true).coaccessible());
      } else if (op === "WEIGHT") {
        peek(ln, col).addWeight(parseFloat(value)).pushWeights();
      } else if (op === "SYMBOL") {
        append(FST.fromLabel([value]));
      } else if (op === "ANY") {
        append(FST.fromLabel(["."]));
      } else if (op === "VARIABLE") {
        if (!Object.prototype.hasOwnProperty.call(this.defined, value)) {
          this._errorReport(SyntaxError, `Defined FST \"${value}\" not found.`, ln, col);
        }
        append(this.defined[value].copyMod());
      } else if (op === "CHAR_CLASS") {
        const [ranges, negated] = this.characterClassParse(value);
        append(FST.characterRanges(ranges, negated));
      } else if (op === "COMPLEMENT") {
        const a = pop1(ln, col);
        append(a.complement());
      }
    }

    if (stack.length !== 1) {
      this._errorReport(SyntaxError, "Something's happening here, and what it is ain't exactly clear...", 1, 0);
    }
    const fst = pop1(1, 0);
    return fst.trim().epsilonRemove().pushWeights().determinizeAsDFA().minimizeAsDFA().labelStatesTopology().cleanupSigma();
  }
}

// ------------------------
// FST implementation
// ------------------------

export class FST {
  states: Set<State>;
  initialstate: State;
  finalstates: Set<State>;
  alphabet: Set<string>;

  // ----------------------------------------------------------------------
  // Macro / function registry
  //
  // Macros are user-defined regex templates that can be invoked inside
  // regexes via $^name(...), just like built-in functions.
  //
  // A macro is defined as:  def name(x, y): /regex using $x and $y/
  // and used as:            /.* - $^name(foo, bar)/
  //
  // Implementation strategy (JS-friendly): treat macros as functions that
  // compile their body with a temporary definitions environment mapping
  // param names to the argument FSTs.
  // ----------------------------------------------------------------------

  static _macros: Map<string, { params: string[], body: string }> = new Map();

  static defineMacro(name: string, params: string[], body: string): void {
    if (!name || typeof name !== 'string') throw new Error('Macro name must be a string.');
    const ps = Array.isArray(params) ? params.map((p) => String(p).trim()).filter(Boolean) : [];
    let b = String(body ?? '').trim();
    // Allow the user to provide /.../ or raw regex.
    if (b.startsWith('/') && b.endsWith('/') && b.length >= 2) b = b.slice(1, -1);
    FST._macros.set(name, { params: ps, body: b });
  }

  static listMacros() {
    return Array.from(FST._macros.keys()).sort();
  }

  static clearMacros() {
    FST._macros.clear();
  }

  static _macroFunctions(defined: DefinedMapping, functions: FunctionSet): FunctionObject[] {
    // Convert macro registry to function objects understood by RegexParse.
    // Custom functions passed by the caller should override macros.
    const overridden = new Set();
    for (const f of functions) {
      if (typeof f === 'function' && f.name) overridden.add(f.name);
      else if (f && typeof f === 'object' && typeof f.name === 'string') overridden.add(f.name);
    }
    const out = [];
    for (const [name, spec] of FST._macros.entries()) {
      if (overridden.has(name)) continue;
      out.push({
        name,
        fn: (...args: any) => {
          // const kwargs = args.length ? args[args.length - 1] : {};
          const realArgs = args.length ? args.slice(0, -1) : [];
          if (realArgs.length !== spec.params.length) {
            throw new SyntaxError(`Macro "${name}" expects ${spec.params.length} args, got ${realArgs.length}.`);
          }
          const localDefs = { ...defined };
          for (let i = 0; i < spec.params.length; i++) localDefs[spec.params[i]] = realArgs[i];
          // Compile the macro body in the caller's environment.
          return FST.re(spec.body, localDefs, functions);
        },
      });
    }
    return out;
  }

  static characterRanges(ranges: [number, number][], complement = false) {
    const newfst = new FST();
    const second = new State();
    newfst.states.add(second);
    newfst.finalstates = new Set([second]);
    second.finalweight = 0.0;

    const alphabet = new Set<string>();
    for (const [start, end] of ranges) {
      for (let cp = start; cp <= end; cp++) {
        const sym = String.fromCodePoint(cp);
        if (!alphabet.has(sym)) {
          alphabet.add(sym);
          if (!complement) newfst.initialstate.addTransition(second, [sym], 0.0);
        }
      }
    }
    if (complement) {
      newfst.initialstate.addTransition(second, ["."], 0.0);
      alphabet.add(".");
    }
    newfst.alphabet = alphabet;
    return newfst;
  }

  static regex(regExp: string, defined: DefinedMapping = {}, functions: FunctionSet = new Set()) {
    // Always include macros (as functions) unless the caller overrides them.
    const fnSet = new Set(functions);
    for (const mf of FST._macroFunctions(defined, fnSet)) fnSet.add(mf);
    const rp = new RegexParse(regExp, defined, fnSet);
    return rp.compiled;
  }

  static re(regExp: string, defined: DefinedMapping = {}, functions: FunctionSet = new Set()) {
    return FST.regex(regExp, defined, functions);
  }

  static fromLabel(label: labelArray, weight = 0.0) {
    const fst = new FST();
    // Label is array of strings; epsilon if [""]
    // FIXME: That's not the same definition used elsewhere
    if (label.length === 1 && label[0] === "") {
      fst.finalstates.add(fst.initialstate);
      fst.initialstate.finalweight = weight;
      return fst;
    }
    fst.alphabet = new Set(label.filter((s) => s !== ""));
    const target = new State();
    fst.states.add(target);
    fst.finalstates.add(target);
    target.finalweight = weight;
    fst.initialstate.addTransition(target, label, 0.0);
    return fst;
  }

  constructor({label, weight = 0.0, alphabet}:
              { label?: string | labelArray, weight?: number, alphabet?: Set<string> } = {}) {
    this.alphabet = alphabet ? new Set(alphabet) : new Set();
    this.initialstate = new State();
    this.states = new Set([this.initialstate]);
    this.finalstates = new Set();
    if (label !== undefined) {
      if (!(label instanceof Array))
        label = [label];
      const built = FST.fromLabel(label, weight);
      this.become(built);
    }
  }

  // Mutate into other
  become(other: FST): FST {
    this.alphabet = other.alphabet;
    this.initialstate = other.initialstate;
    this.states = other.states;
    this.finalstates = other.finalstates;
    return this;
  }

  get length() { return this.states.size; }

  // AT&T representation
  toATT(): string {
    const ids = [];
    for (const s of this.states) if (s !== this.initialstate) ids.push(s);
    const statenums = new Map();
    let i = 1;
    for (const s of ids) statenums.set(s, i++);
    statenums.set(this.initialstate, 0);

    let st = "";
    for (const s of this.states) {
      for (const [label, t] of s.allTransitions()) {
        const src = statenums.get(s);
        const dst = statenums.get(t.targetstate);
        st += `${src}\t${dst}\t${label.join("\t")}\t${t.weight}\n`;
      }
    }
    for (const s of this.finalstates) {
      st += `${statenums.get(s)}\t${s.finalweight}\n`;
    }
    return st;
  }

  // ------------------------------------------------------------
  // Foma string representation (writer)
  // ------------------------------------------------------------
  // Port of pyfoma.FST.to_fomastring (see fomastring.py).
  // Limitations match the Python version: only 1- or 2-tape FSTs.
  toFomastring(fstname: string | null = null): string {
    const NO = 0, YES = 1, UNKNOWN = 2;

    // Deterministic, stable state numbering: BFS from initial.
    const orderedStates = [];
    {
      const q = [this.initialstate];
      const seen = new Set([this.initialstate]);
      while (q.length) {
        const s = q.shift()!;
        orderedStates.push(s);
        for (const [_, t] of s.allTransitions()) {
          const dst = t.targetstate;
          if (!seen.has(dst)) { seen.add(dst); q.push(dst); }
        }
      }
      // Include any disconnected states (should be rare after trimming).
      for (const s of this.states) if (!seen.has(s)) orderedStates.push(s);
    }

    const stateId = new Map();
    for (let i = 0; i < orderedStates.length; i++) stateId.set(orderedStates[i], i);

    // Compute arity (max label length), counts, and quick feature flags.
    let arity_ = 1;
    let arccount_ = 0;
    let hasEps = false;
    let hasDot = this.alphabet.has('.');
    let weighted_ = false;
    for (const s of orderedStates) {
      if (this.finalstates.has(s) && s.finalweight !== 0.0) weighted_ = true;
      for (const [label, tr] of s.allTransitions()) {
        arccount_ += 1;
        if (tr.weight !== 0.0) weighted_ = true;
        if (label.length > arity_) arity_ = label.length;
        if (label.some((x) => x === '')) hasEps = true;
        if (label.some((x) => x === '.')) hasDot = true;
      }
    }
    if (arity_ > 2) {
      throw new Error(`toFomastring only supports 1- or 2-tape FSTs (got arity ${arity_}).`);
    }

    const statecount_ = orderedStates.length;
    const finalcount_ = this.finalstates.size;

    // Epsilon-free?
    const is_epsilon_free_ = hasEps ? NO : YES;

    // Deterministic? (simple check: no eps on input tape and no duplicate input labels per state)
    let is_deterministic_ = YES;
    {
      for (const s of orderedStates) {
        const seenIn = new Set();
        // FIXME: Don't need allTransitions here! Quite inefficient!
        for (const [label, _] of s.allTransitions()) {
          const inSym = label[0];
          if (inSym === '') { is_deterministic_ = NO; break; }
          const key = `${inSym}`;
          if (seenIn.has(key)) { is_deterministic_ = NO; break; }
          seenIn.add(key);
        }
        if (is_deterministic_ === NO) break;
      }
    }

    // Pathcount and loop-free detection (count paths if DAG; else -1).
    const pathcount_ = (() => {
      // DFS cycle detect.
      const temp = new Set();
      const perm = new Set();
      let cyclic = false;
      const dfs = (s: State) => {
        if (cyclic) return;
        if (perm.has(s)) return;
        if (temp.has(s)) { cyclic = true; return; }
        temp.add(s);
        for (const [_, tr] of s.allTransitions()) dfs(tr.targetstate);
        temp.delete(s);
        perm.add(s);
      };
      dfs(this.initialstate);
      if (cyclic) return -1;

      // DAG DP in reverse topological order via finishing order in perm.
      // We'll just use a memoized recursion since it's acyclic.
      const memo = new Map();
      const countFrom = (s: State) => {
        if (memo.has(s)) return memo.get(s);
        let total = this.finalstates.has(s) ? 1n : 0n;
        for (const [_, tr] of s.allTransitions()) {
          total += countFrom(tr.targetstate);
        }
        memo.set(s, total);
        return total;
      };
      const n = countFrom(this.initialstate);
      // Clamp to Number when safe; otherwise return -1 (foma expects int; huge counts aren’t useful).
      const maxSafe = BigInt(Number.MAX_SAFE_INTEGER);
      if (n > maxSafe) return -1;
      return Number(n);
    })();

    const is_loop_free_ = (pathcount_ === -1) ? NO : YES;

    // Properties we don't track precisely in the JS port.
    const is_pruned_ = UNKNOWN;
    const is_minimized_ = UNKNOWN;

    const extras_ = (weighted_ ? YES : NO) << 6;

    // Sigma mapping.
    const sigmamap = new Map();
    let cntr = 3;
    const alphaSyms = Array.from(this.alphabet).slice().sort();
    for (const sym of alphaSyms) {
      if (sym !== '' && sym !== '.') {
        sigmamap.set(sym, cntr);
        cntr += 1;
      }
    }
    if (hasDot) {
      sigmamap.set('@_UNKNOWN_SYMBOL_@', 1);
      sigmamap.set('@_IDENTITY_SYMBOL_@', 2);
    }
    if (hasEps) sigmamap.set('@_EPSILON_SYMBOL_@', 0);

    const sigmastr = ['##sigma##'];
    for (const [name, num] of Array.from(sigmamap.entries()).sort((a, b) => a[1] - b[1])) {
      sigmastr.push(`${num} ${name}`);
    }

    // Build ##states## and (optionally) ##weights##
    const statestr = ['##states##'];
    const weightstr = ['##weights##'];
    let linecount_ = 1; // foma expects 1 + number of lines in ##states## section (excluding sentinel)

    const mapLabelForFoma = (label: labelArray) => {
      let out = label.slice();
      if (out.includes('.')) {
        if (out.length === 1) {
          out = ['@_IDENTITY_SYMBOL_@'];
        } else {
          out = out.map((x) => (x === '.' ? '@_UNKNOWN_SYMBOL_@' : x));
        }
      }
      if (out.includes('')) {
        out = out.map((x) => (x === '' ? '@_EPSILON_SYMBOL_@' : x));
      }
      return out;
    };

    for (const s of orderedStates) {
      const ts = Array.from(s.allTransitions());
      const finalstate = this.finalstates.has(s) ? 1 : 0;
      const sid = stateId.get(s);
      if (ts.length === 0) {
        statestr.push(`${sid} -1 -1 ${finalstate}`);
        if (weighted_) weightstr.push(`${s.finalweight}`);
        linecount_ += 1;
        continue;
      }

      let first = true;
      for (const [label0, tr] of ts) {
        const label = mapLabelForFoma(label0);
        const ins = sigmamap.get(label[0]);
        if (ins === undefined) throw new Error(`Missing sigma symbol for: ${label[0]}`);
        let sigstr;
        if (label.length === 2) {
          const outs = sigmamap.get(label[1]);
          if (outs === undefined) throw new Error(`Missing sigma symbol for: ${label[1]}`);
          sigstr = `${ins} ${outs}`;
        } else {
          sigstr = `${ins}`;
        }
        const tid = stateId.get(tr.targetstate);
        if (first) {
          statestr.push(`${sid} ${sigstr} ${tid} ${finalstate}`);
          if (weighted_) weightstr.push(`${tr.weight} ${s.finalweight}`);
        } else {
          statestr.push(`${sigstr} ${tid}`);
          if (weighted_) weightstr.push(`${tr.weight}`);
        }
        linecount_ += 1;
        first = false;
      }
    }
    statestr.push('-1 -1 -1 -1 -1');

    // Name
    if (fstname == null) {
      if (FST._fomaNameCounter == null) FST._fomaNameCounter = 0;
      FST._fomaNameCounter = (FST._fomaNameCounter + 1) >>> 0;
      fstname = FST._fomaNameCounter.toString(16).toUpperCase().padStart(8, '0');
    }

    const intro = ['##foma-net 1.0##', '##props##'];
    intro.push([
      arity_, arccount_, statecount_, linecount_, finalcount_, pathcount_,
      is_deterministic_, is_pruned_, is_minimized_, is_epsilon_free_, is_loop_free_, extras_, fstname,
    ].join(' '));

    const parts = weighted_ ? (intro.concat(weightstr, sigmastr, statestr, ['##end##']))
                            : (intro.concat(sigmastr, statestr, ['##end##']));
    return parts.join('\n') + '\n';
  }
  static _fomaNameCounter: number | null = null;

  numberUnnamedStates(force = false) {
    const c = new Counter();
    const ordered = [this.initialstate, ...Array.from(setDifference(this.states, new Set([this.initialstate])))];
    const mapping = new Map();
    for (const s of ordered) {
      mapping.set(s, (s.name === null || force) ? String(c.next()) : String(s.name));
    }
    return mapping;
  }

  // DOT graph for viz.js
  toDot({ raw = false, showWeights = false, showAlphabet = true } = {}) {
    const floatFormat = (num: number) => {
      if (!showWeights) return "";
      let s = num.toFixed(2).replace(/0+$/, "").replace(/\.$/, "");
      if (s === "-0") s = "0";
      return "/" + s;
    };
    const fmtLabel = (lbl: labelArray) => lbl.map((x) => (x === "" ? "ε" : x)).join(":");

    const statenums = this.numberUnnamedStates();
    const sigma = showAlphabet ? `Σ: {${Array.from(this.alphabet).sort().join(",")}}` : "";
    const lines = [];
    lines.push("digraph FST {");
    lines.push('  rankdir=LR;');
    if (sigma) lines.push(`  label="${sigma.replace(/\"/g, '\\"')}";`);

    const anyWeights = (!showWeights) && (
      Array.from(this.states).some((s) => Array.from(s.allTransitions()).some(([_, t]) => t.weight !== 0.0)) ||
      Array.from(this.finalstates).some((s) => s.finalweight !== 0.0)
    );
    if (anyWeights) showWeights = true;

    // Nodes
    for (const s of this.states) {
      const isFinal = this.finalstates.has(s);
      const isInit = s === this.initialstate;
      const base = statenums.get(s);
      const name = isFinal ? `${base}${floatFormat(s.finalweight)}` : base;
      const shape = isFinal ? "doublecircle" : "circle";
      const style = isInit ? "filled,bold" : "filled";
      lines.push(`  "${name}" [shape=${shape}, style="${style}"];`);
    }

    // Edges grouped by target
    for (const s of this.states) {
      const grouped = new Map();
      for (const [label, t] of s.allTransitions()) {
        if (!grouped.has(t.targetstate)) grouped.set(t.targetstate, []);
        grouped.get(t.targetstate).push([label, t.weight]);
      }
      for (const [target, arr] of grouped.entries()) {
        const labellist = arr.map(([lbl, w]: [labelArray, number]) => {
          if (raw) return `${JSON.stringify(lbl)}/${w}`;
          return `${fmtLabel(lbl)}${floatFormat(w)}`;
        }).sort();
        const printLabel = labellist.join(", ").replace(/\"/g, '\\"');
        const srcName = this.finalstates.has(s) ? `${statenums.get(s)}${floatFormat(s.finalweight)}` : statenums.get(s);
        const dstName = this.finalstates.has(target) ? `${statenums.get(target)}${floatFormat(target.finalweight)}` : statenums.get(target);
        lines.push(`  "${srcName}" -> "${dstName}" [label="${printLabel}"];`);
      }
    }

    lines.push("}");
    return lines.join("\n");
  }

  // ------------------------
  // Copy helpers
  // ------------------------

  copyFiltered(filterStates: Set<State> | null = null): [FST, Map<any, any>] {
    const mapping = new Map();
    const newfst = new FST();
    const statesToCopy: Set<State> = filterStates ? new Set(filterStates) : new Set(this.states);

    // Ensure initial present
    if (!statesToCopy.has(this.initialstate)) statesToCopy.add(this.initialstate);

    for (const s of statesToCopy) mapping.set(s, new State({ finalweight: s.finalweight, name: s.name }));
    newfst.initialstate = mapping.get(this.initialstate);
    newfst.states = new Set(mapping.values());
    newfst.finalstates = new Set();
    for (const s of this.finalstates) if (mapping.has(s)) newfst.finalstates.add(mapping.get(s));

    for (const s of statesToCopy) {
      for (const [label, t] of s.allTransitions()) {
        if (!mapping.has(t.targetstate)) continue;
        mapping.get(s).addTransition(mapping.get(t.targetstate), label.slice(), t.weight);
      }
    }
    newfst.alphabet = new Set(this.alphabet);
    return [newfst, mapping];
  }

  copyMod({modLabel, modWeight}: { modLabel?: ModLabelFunction, modWeight?: ModWeightFunction } = {}): FST {
    const [newfst] = this.copyFiltered();
    if (!modLabel && !modWeight) return newfst;

    for (const s of newfst.states) {
      const newTrans = new Map();
      for (const { label, set } of s.transitions.values()) {
        for (const t of set) {
          const nl = modLabel ? modLabel(label.slice(), t.weight) : label.slice();
          const nw = modWeight ? modWeight(label.slice(), t.weight) : t.weight;
          const k = labelKey(nl);
          if (!newTrans.has(k)) newTrans.set(k, { label: nl, set: new Set() });
          newTrans.get(k).set.add(new Transition(t.targetstate, nl, nw));
        }
      }
      s.transitions = newTrans;
      s._invalidateIndexes();
      if (s === newfst.initialstate) {
        // nothing
      }
    }
    // Alphabet adjustment is left to caller.
    return newfst;
  }

  // ------------------------
  // Graph algorithms
  // ------------------------

  *allTransitions(states: Set<State>): Generator<[State, labelArray, Transition]> {
    for (const s of states) {
      for (const [label, t] of s.allTransitions()) {
        yield [s, label, t];
      }
    }
  }

  accessible() {
    const Q = [this.initialstate];
    const seen = new Set([this.initialstate]);
    while (Q.length) {
      const s = Q.pop()!;
      for (const [, t] of s.allTransitions()) {
        if (!seen.has(t.targetstate)) {
          seen.add(t.targetstate);
          Q.push(t.targetstate);
        }
      }
    }
    const [newfst] = this.copyFiltered(seen);
    return this.become(newfst);
  }

  coaccessible() {
    // reverse edges by scanning
    const rev = new Map();
    for (const s of this.states) rev.set(s, new Set());
    for (const [s, , t] of this.allTransitions(this.states)) {
      rev.get(t.targetstate).add(s);
    }
    const Q = [...this.finalstates];
    const seen = new Set(Q);
    while (Q.length) {
      const s = Q.pop();
      for (const p of rev.get(s) ?? []) {
        if (!seen.has(p)) {
          seen.add(p);
          Q.push(p);
        }
      }
    }
    const [newfst] = this.copyFiltered(seen);
    return this.become(newfst);
  }

  trim() {
    return this.accessible().coaccessible();
  }

  // ------------------------
  // Basic constructions
  // ------------------------

  addWeight(w: number): FST {
    for (const s of this.finalstates) s.finalweight += w;
    return this;
  }

  pushWeights(): FST {
    // Weight pushing / reweighting (tropical).
    // We use potentials p(s)=shortest distance from s to a final (including finalweights).
    // To avoid needing a separate "initial weight" field, we normalize by p0=p(initial)
    // and keep costs exactly preserved by adjusting final weights by +p0.
    const dist = this._shortestDistancesToFinal();
    const p0 = dist.get(this.initialstate);
    if (p0 === undefined || p0 === floatInf()) return this;

    for (const s of this.states) {
      const ds = dist.get(s);
      if (ds === undefined || ds === floatInf()) continue;

      const newMap = new Map();
      for (const { label, set } of s.transitions.values()) {
        for (const t of set) {
          const dt = dist.get(t.targetstate);
          const nw = (dt === undefined || dt === floatInf()) ? t.weight : (t.weight + dt - ds);
          const k = labelKey(label);
          if (!newMap.has(k)) newMap.set(k, { label, set: new Set() });
          newMap.get(k).set.add(new Transition(t.targetstate, label, nw));
        }
      }
      s.transitions = newMap;
      s._invalidateIndexes();

      if (this.finalstates.has(s) && s.finalweight !== floatInf()) {
        // final'(s) = final(s) - p(s) + p0  (preserves path weights from initial)
        s.finalweight = s.finalweight - ds + p0;
      }
    }
    return this;
  }

  _shortestDistancesToFinal() {
    // Dijkstra on reversed graph with weights.
    const rev = new Map();
    for (const s of this.states) rev.set(s, []);
    for (const [s, _, t] of this.allTransitions(this.states)) {
      rev.get(t.targetstate).push([s, t.weight]);
    }

    const dist = new Map();
    const heap = new MinHeap<State>();
    for (const f of this.finalstates) {
      const d0 = f.finalweight;
      dist.set(f, d0);
      heap.push([d0, f]);
    }

    while (heap.size) {
      const [d, v] = heap.pop()!;
      if (d !== dist.get(v)) continue;
      for (const [u, w] of rev.get(v)) {
        const nd = d + w;
        const prev = dist.has(u) ? dist.get(u) : floatInf();
        if (nd < prev) {
          dist.set(u, nd);
          heap.push([nd, u]);
        }
      }
    }

    // unreachable => inf
    for (const s of this.states) if (!dist.has(s)) dist.set(s, floatInf());
    return dist;
  }

  epsilonRemove(): FST {
    // Port of epsilon_remove (epsilon-free). This is a simplified but compatible version.
    // Compute epsilon-closure with cheapest epsilon paths.
    // Works for the use cases in test_pyfoma.py.

    const eps = "";

    // Precompute epsilon closures with Dijkstra per state (only eps transitions).
    const closures = new Map(); // state -> Map<state, cost>

    const epsNeighbors = (s: State) => {
      const out: [State, number][] = [];
      for (const [label, t] of s.allTransitions()) {
        if (label.every((x) => x === eps)) out.push([t.targetstate, t.weight]);
      }
      return out;
    };

    for (const s of this.states) {
      const dist = new Map();
      const heap = new MinHeap<State>();
      dist.set(s, 0.0);
      heap.push([0.0, s]);
      while (heap.size) {
        const [d, v] = heap.pop()!;
        if (d !== dist.get(v)) continue;
        for (const [nxt, w] of epsNeighbors(v)) {
          const nd = d + w;
          const prev = dist.has(nxt) ? dist.get(nxt) : floatInf();
          if (nd < prev) {
            dist.set(nxt, nd);
            heap.push([nd, nxt]);
          }
        }
      }
      closures.set(s, dist);
    }

    // Build new transitions without eps.
    for (const s of this.states) {
      const clos = closures.get(s);
      // if closure reaches finals, s becomes final with adjusted weight
      let bestFinal = floatInf();
      for (const f of this.finalstates) {
        if (clos.has(f)) {
          bestFinal = Math.min(bestFinal, clos.get(f) + f.finalweight);
        }
      }
      if (bestFinal < floatInf()) {
        this.finalstates.add(s);
        s.finalweight = Math.min(s.finalweight, bestFinal);
      }

      const newMap = new Map();
      for (const [mid, ecost] of clos.entries()) {
        for (const [label, t] of mid.allTransitions()) {
          if (label.every((x: string) => x === eps)) continue;
          const k = labelKey(label);
          if (!newMap.has(k)) newMap.set(k, { label, set: new Set() });
          newMap.get(k).set.add(new Transition(t.targetstate, label, ecost + t.weight));
        }
      }
      s.transitions = newMap;
      s._invalidateIndexes();
    }

    // Remove unreachable epsilon-only states by trimming.
    return this.trim();
  }

  optional() {
    // Make initial state final (epsilon accepted)
    this.finalstates.add(this.initialstate);
    this.initialstate.finalweight = Math.min(this.initialstate.finalweight, 0.0);
    return this;
  }
  kleeneClosure(mode = "star") {
    // Epsilon-free closure as in pyfoma.py: replicate initial transitions,
    // and from each final state add transitions that mimic the initial state's outgoing arcs.
    const q1 = new Map();
    for (const s of this.states) q1.set(s, new State({ finalweight: 0.0, name: s.name }));

    const newfst = new FST({ alphabet: new Set(this.alphabet) });

    // Copy transitions from old initial to new initial
    for (const [lbl, t] of this.initialstate.allTransitions()) {
      newfst.initialstate.addTransition(q1.get(t.targetstate), lbl.slice(), t.weight);
    }

    // Copy all transitions among mapped states
    for (const [s, lbl, t] of this.allTransitions(this.states)) {
      q1.get(s).addTransition(q1.get(t.targetstate), lbl.slice(), t.weight);
    }

    // For each final, add initial transitions (loop-back), and preserve final weights
    for (const s of this.finalstates) {
      for (const [lbl, t] of this.initialstate.allTransitions()) {
        q1.get(s).addTransition(q1.get(t.targetstate), lbl.slice(), t.weight);
      }
      q1.get(s).finalweight = s.finalweight;
    }

    newfst.finalstates = new Set();
    for (const s of this.finalstates) newfst.finalstates.add(q1.get(s));

    // Star adds epsilon acceptance at initial. Plus keeps it only if original accepted epsilon.
    if (mode !== "plus" || this.finalstates.has(this.initialstate)) {
      newfst.finalstates.add(newfst.initialstate);
      newfst.initialstate.finalweight = 0.0;
    }

    newfst.states = new Set(q1.values());
    newfst.states.add(newfst.initialstate);
    return this.become(newfst);
  }
  concatenate(other: FST): FST {
    // Epsilon-free concatenation (ported from pyfoma.py).
    this._harmonizeAlphabet(other);
    const [ocopy] = other.copyFiltered(); // copy since self may equal other

    const unionStates = new Set([...this.states, ...ocopy.states]);
    const q1q2 = new Map();
    for (const s of unionStates) q1q2.set(s, new State({ name: s.name }));

    // Copy all transitions from both machines into the cloned state set.
    for (const s of unionStates) {
      for (const [lbl, t] of s.allTransitions()) {
        if (!q1q2.has(t.targetstate)) continue;
        q1q2.get(s).addTransition(q1q2.get(t.targetstate), lbl, t.weight);
      }
    }

    // Connect final states of self to the outgoing transitions of other's initial state.
    for (const s of this.finalstates) {
      for (const [lbl2, t2] of ocopy.initialstate.allTransitions()) {
        q1q2.get(s).addTransition(q1q2.get(t2.targetstate), lbl2, t2.weight + s.finalweight);
      }
    }

    const newfst = new FST({ alphabet: new Set([...this.alphabet, ...ocopy.alphabet]) });
    newfst.initialstate = q1q2.get(this.initialstate);

    // Finals are finals of other (in the copied machine).
    newfst.finalstates = new Set([...ocopy.finalstates].map((f) => q1q2.get(f)));
    for (const s of ocopy.finalstates) q1q2.get(s).finalweight = s.finalweight;

    // If other accepts epsilon, then finals of self are also finals (with combined weight).
    if (ocopy.finalstates.has(ocopy.initialstate)) {
      for (const f of this.finalstates) {
        newfst.finalstates.add(q1q2.get(f));
        q1q2.get(f).finalweight = f.finalweight + ocopy.initialstate.finalweight;
      }
    }

    newfst.states = new Set(q1q2.values());
    newfst.alphabet = new Set([...this.alphabet, ...ocopy.alphabet]);
    return this.become(newfst);
  }

  union(other: FST): FST {
    this._harmonizeAlphabet(other);
    const [A] = this.copyFiltered();
    const [B] = other.copyFiltered();
    const mapping = new Map();
    const newfst = new FST();

    // Map old states to new copies
    for (const s of setUnion(A.states, B.states)) mapping.set(s, new State({ finalweight: s.finalweight, name: s.name }));

    newfst.states = new Set(mapping.values());
    newfst.states.add(newfst.initialstate);
    newfst.finalstates = new Set();

    // Copy transitions from old initial states to new initial
    for (const [label, t] of A.initialstate.allTransitions()) newfst.initialstate.addTransition(mapping.get(t.targetstate), label, t.weight);
    for (const [label, t] of B.initialstate.allTransitions()) newfst.initialstate.addTransition(mapping.get(t.targetstate), label, t.weight);

    // Copy all other transitions
    for (const [s, label, t] of A.allTransitions(A.states)) {
      mapping.get(s).addTransition(mapping.get(t.targetstate), label, t.weight);
    }
    for (const [s, label, t] of B.allTransitions(B.states)) {
      mapping.get(s).addTransition(mapping.get(t.targetstate), label, t.weight);
    }

    for (const s of setUnion(A.finalstates, B.finalstates)) {
      newfst.finalstates.add(mapping.get(s));
      mapping.get(s).finalweight = s.finalweight;
    }

    if (A.finalstates.has(A.initialstate) || B.finalstates.has(B.initialstate)) {
      newfst.finalstates.add(newfst.initialstate);
      const w = Math.min(A.initialstate.finalweight ?? floatInf(), B.initialstate.finalweight ?? floatInf());
      newfst.initialstate.finalweight = w;
    }

    newfst.alphabet = new Set([...A.alphabet, ...B.alphabet]);
    return this.become(newfst);
  }

  intersection(other: FST): FST {
    return this.product(other, {
      finalf: (x) => x[0] && x[1],
      oplus: (x, y) => x + y,
      pathfollow: setIntersection,
    });
  }

  difference(other: FST): FST {
    return this.product(other, {
      finalf: (x) => x[0] && !x[1],
      oplus: (x, _y) => x,
      pathfollow: (x, _y) => x,
    });
  }

  complement(): FST {
    return FST.re(".* - $X", { X: this });
  }

  product(other: FST,
          { finalf = (x) => x[0] || x[1], oplus = Math.min, pathfollow = setUnion }:
          {finalf?: FinalFFunction, oplus?: OPlusFunction, pathfollow?: PathFollowFunction} = {}): FST {
    this._harmonizeAlphabet(other);
    const newfst = new FST();
    const Q = [[this.initialstate, other.initialstate]];
    const S = new Map();
    S.set(`${this.initialstate._id ?? 0}|${other.initialstate._id ?? 0}`, newfst.initialstate);

    // Assign stable ids for keying
    const idMap1 = new Map<State, number>();
    const idMap2 = new Map<State, number>();
    let idc = 0;
    for (const s of this.states) idMap1.set(s, idc++);
    for (const s of other.states) idMap2.set(s, idc++);
    const key = (a: State, b: State) => `${idMap1.get(a)}|${idMap2.get(b)}`;

    S.clear();
    S.set(key(this.initialstate, other.initialstate), newfst.initialstate);

    const dead1 = new State({ finalweight: floatInf() });
    const dead2 = new State({ finalweight: floatInf() });

    while (Q.length) {
      const [t1s, t2s] = Q.pop()!;
      const current = S.get(key(t1s, t2s));
      current.name = [t1s.name, t2s.name];
      if (finalf([this.finalstates.has(t1s), other.finalstates.has(t2s)])) {
        newfst.finalstates.add(current);
        current.finalweight = oplus(t1s.finalweight, t2s.finalweight);
      }
      const labels1 = new Set([...t1s.transitions.values()].map((e) => labelKey(e.label)));
      const labels2 = new Set([...t2s.transitions.values()].map((e) => labelKey(e.label)));
      const follow = pathfollow(labels1, labels2);
      for (const lblKeyStr of follow) {
        const lbl = keyToLabel(lblKeyStr);
        const outs = t1s.transitions.get(lblKeyStr)?.set ?? new Set([new Transition(dead1, lbl, floatInf())]);
        const ins = t2s.transitions.get(lblKeyStr)?.set ?? new Set([new Transition(dead2, lbl, floatInf())]);
        for (const outtr of outs) {
          for (const intr of ins) {
            const nextKey = key(outtr.targetstate, intr.targetstate);
            if (!S.has(nextKey)) {
              const ns = new State();
              S.set(nextKey, ns);
              newfst.states.add(ns);
              Q.push([outtr.targetstate, intr.targetstate]);
            }
            current.addTransition(S.get(nextKey), lbl, oplus(outtr.weight, intr.weight));
          }
        }
      }
    }
    newfst.alphabet = new Set([...this.alphabet, ...other.alphabet]);
    return this.become(newfst);
  }

  invert(): FST {
    for (const s of this.states) {
      const newMap = new Map();
      for (const { label, set } of s.transitions.values()) {
        const nl = label.slice().reverse();
        const k = labelKey(nl);
        if (!newMap.has(k)) newMap.set(k, { label: nl, set: new Set() });
        for (const t of set) {
          t.label = nl;
          newMap.get(k).set.add(t);
        }
      }
      s.transitions = newMap;
      s._invalidateIndexes();
    }
    return this;
  }

  ignore(other: FST): FST {
    const newfst = FST.re("$^output($A @ ('.'|'':$B)*)", { A: this, B: other });
    return this.become(newfst);
  }

  project(dim = 0): FST {
    const sl = (dim === -1) ? (lbl: labelArray) => [lbl[lbl.length - 1]] : (lbl: labelArray) => [lbl[dim]];
    const newAlphabet = new Set<string>();
    const newfst = this.copyMod();
    for (const s of newfst.states) {
      const newTrans = new Map();
      for (const { label, set } of s.transitions.values()) {
        const nl = sl(label);
        const k = labelKey(nl);
        if (!newTrans.has(k)) newTrans.set(k, { label: nl, set: new Set() });
        for (const t of set) {
          t.label = nl;
          newTrans.get(k).set.add(t);
          for (const sym of nl) if (sym !== "") newAlphabet.add(sym);
        }
      }
      s.transitions = newTrans;
      s._invalidateIndexes();
    }
    if (!newAlphabet.has(".")) newfst.alphabet = newAlphabet;
    return this.become(newfst);
  }

  reverse(): FST {
    // epsilon-free reverse
    const newfst = new FST({ alphabet: this.alphabet });
    const mapping = new Map();
    for (const s of this.states) mapping.set(s, new State({ name: s.name }));
    newfst.states = new Set(mapping.values());
    newfst.states.add(newfst.initialstate);

    newfst.finalstates = new Set([mapping.get(this.initialstate)]);
    if (this.finalstates.has(this.initialstate)) {
      newfst.finalstates.add(newfst.initialstate);
      newfst.initialstate.finalweight = this.initialstate.finalweight;
    }
    mapping.get(this.initialstate).finalweight = 0.0;

    for (const [s, lbl, t] of this.allTransitions(this.states)) {
      mapping.get(t.targetstate).addTransition(mapping.get(s), lbl, t.weight);
      if (this.finalstates.has(t.targetstate)) {
        newfst.initialstate.addTransition(mapping.get(s), lbl, t.weight + t.targetstate.finalweight);
      }
    }
    newfst.alphabet = new Set(this.alphabet);
    return this.become(newfst);
  }

  reverseE(): FST {
    // reverse with epsilons (rarely used in tests)
    const newfst = new FST({ alphabet: this.alphabet });
    newfst.initialstate = new State({ name: Array.from(this.finalstates).map((k) => k.name).join(",") });
    const mapping = new Map();
    for (const s of this.states) mapping.set(s, new State({ name: s.name }));
    for (const t of this.finalstates) {
      newfst.initialstate.addTransition(mapping.get(t), [""], t.finalweight);
    }
    for (const [s, lbl, t] of this.allTransitions(this.states)) {
      mapping.get(t.targetstate).addTransition(mapping.get(s), lbl, t.weight);
    }
    newfst.states = new Set(mapping.values());
    newfst.states.add(newfst.initialstate);
    newfst.finalstates = new Set([mapping.get(this.initialstate)]);
    mapping.get(this.initialstate).finalweight = 0.0;
    return this.become(newfst);
  }

  // Cross product: implemented via composition (as in pyfoma.py)
  crossProduct(other: FST, optional = false): FST {
    this._harmonizeAlphabet(other);

    // Pad self with an empty output tape, pad other with an empty input tape, then compose.
    const a = this.copyMod({
      modLabel: (lbl: labelArray, _w: number) => lbl.concat([""]),
      modWeight: (_lbl: labelArray, w: number) => w,
    });
    const b = other.copyMod({
      modLabel: (lbl: labelArray, _w: number) => [""].concat(lbl),
      modWeight: (_lbl: labelArray, w: number) => w,
    });

    const composed = a.compose(b);
    if (optional) {
      return this.become(composed.union(this));
    }
    return this.become(composed);
  }

  compose(other: FST): FST {
    this._harmonizeAlphabet(other);

    // Composition with epsilon filtering (ported from pyfoma.py).
    // Supports k-tape labels represented as arrays.
    const mergeTuples = (x: labelArray, y: labelArray) => {
      let t: labelArray;
      if (x.length === 1) {
        // expand acceptor x into 2-tape-on-the-fly
        t = x.concat(y.slice(1));
      } else if (y.length === 1) {
        // expand acceptor y into 2-tape-on-the-fly
        t = x.slice(0, -1).concat(y);
      } else {
        t = x.slice(0, -1).concat(y.slice(1));
      }
      // If all tapes equal, collapse to a 1-tape acceptor label.
      if (t.length > 0 && t.every((s) => s === t[0])) return [t[0]];
      return t;
    };

    const newfst = new FST();
    // Preserve the full sigma from both operands.
    // This matters for expressions like [^a]:'' where excluded symbols (e.g. 'a')
    // may not appear on any arc label but must remain in the alphabet so '.'
    // expands/behaves correctly later.
    for (const sym of this.alphabet) if (sym !== "") newfst.alphabet.add(sym);
    for (const sym of other.alphabet) if (sym !== "") newfst.alphabet.add(sym);
    const Q: [State, State, number][] = [[this.initialstate, other.initialstate, 0]];
    let qh = 0;

    const idMap1 = new Map<State, number>();
    const idMap2 = new Map<State, number>();
    let idc = 0;
    for (const s of this.states) idMap1.set(s, idc++);
    for (const s of other.states) idMap2.set(s, idc++);
    const key = (a: State, b: State, m: number) => `${idMap1.get(a)}|${idMap2.get(b)}|${m}`;

    const S = new Map<string, State>();
    S.set(key(...Q[0]), newfst.initialstate);

    while (qh < Q.length) {
      const [A, B, mode] = Q[qh++];
      const currKey = key(A, B, mode);
      const current = S.get(currKey);
      if (current === undefined) // Should not happen?
        throw `Undefined state ${currKey}`;
      current.name = [A.name, B.name, mode].toString();

      // In pyfoma, finality does not depend on the epsilon-filter mode.
      if (this.finalstates.has(A) && other.finalstates.has(B)) {
        newfst.finalstates.add(current);
        current.finalweight = A.finalweight + B.finalweight;
      }

      // Match on output of A (last tape) with input of B (first tape).
      for (const matchSym of A.transitionsout.keys()) {
        // Only allow epsilon matching (matchSym === "") in mode 0.
        if (!(mode === 0 || matchSym !== "")) continue;

        const outs = A.transitionsout.get(matchSym) ?? new Set();
        const ins = B.transitionsin.get(matchSym) ?? new Set();

        for (const [outlbl, outtrans] of outs) {
          for (const [inlbl, intrans] of ins) {
            const target1 = outtrans.targetstate;
            const target2 = intrans.targetstate;
            const nextKey = key(target1, target2, 0);
            if (!S.has(nextKey)) {
              const ns = new State();
              S.set(nextKey, ns);
              newfst.states.add(ns);
              Q.push([target1, target2, 0]);
            }
            const newLabel = mergeTuples(outlbl, inlbl);
            current.addTransition(S.get(nextKey)!, newLabel, outtrans.weight + intrans.weight);
            for (const sym of newLabel) if (sym !== "") newfst.alphabet.add(sym);
          }
        }
      }

      // Epsilon-handling (Mohri-style 3-state filter).
      // Mode 1: B waits (A took eps output).
      for (const [outlbl, outtrans] of A.transitionsout.get("") ?? []) {
        if (mode === 2) break;
        const target1 = outtrans.targetstate;
        const target2 = B;
        const nextKey = key(target1, target2, 1);
        if (!S.has(nextKey)) {
          const ns = new State();
          S.set(nextKey, ns);
          newfst.states.add(ns);
          Q.push([target1, target2, 1]);
        }
        current.addTransition(S.get(nextKey)!, outlbl, outtrans.weight);
        for (const sym of outlbl) if (sym !== "") newfst.alphabet.add(sym);
      }

      // Mode 2: A waits (B took eps input).
      for (const [inlbl, intrans] of B.transitionsin.get("") ?? []) {
        if (mode === 1) break;
        const target1 = A;
        const target2 = intrans.targetstate;
        const nextKey = key(target1, target2, 2);
        if (!S.has(nextKey)) {
          const ns = new State();
          S.set(nextKey, ns);
          newfst.states.add(ns);
          Q.push([target1, target2, 2]);
        }
        current.addTransition(S.get(nextKey)!, inlbl, intrans.weight);
        for (const sym of inlbl) if (sym !== "") newfst.alphabet.add(sym);
      }
    }

    return this.become(newfst);
  }


  // ------------------------------
  // Context restriction + rewrite
  // ------------------------------

  contextRestrict(...contexts: any): FST {
    let rewrite = false;
    // last arg could be kwargs object
    if (contexts.length && typeof contexts[contexts.length - 1] === "object" && !Array.isArray(contexts[contexts.length - 1])) {
      const kwargs = contexts.pop();
      rewrite = Boolean(kwargs.rewrite);
    }

    for (const pair of contexts) {
      for (const fsm of pair) fsm.alphabet.add("@=@");
    }
    const fst = this.copyMod();
    fst.alphabet.add("@=@");

    const cs = [];
    for (const [lc, rc] of contexts) {
      if (!rewrite) {
        cs.push(FST.re("$lc '@=@' (.-'@=@')* '@=@' $rc", {
          lc: lc.copyMod().mapLabels({ "#": "@#@" }),
          rc: rc.copyMod().mapLabels({ "#": "@#@" }),
        }));
      } else {
        cs.push(FST.re("$lc '@=@' (.-'@=@')* '@=@' $rc", { lc, rc }));
      }
    }

    let cunion = cs[0];
    for (let i = 1; i < cs.length; i++) cunion = cunion.union(cs[i]);
    cunion = cunion.determinize().minimize();

    let r = FST.re("(.-'@=@')* '@=@' $c '@=@' (.-'@=@')* - ((.-'@=@')* $cunion (.-'@=@')*)", { c: fst, cunion });
    r = r.mapLabels({ "@=@": "" }).epsilonRemove().determinizeAsDFA().minimize();

    for (const pair of contexts) {
      for (const fsm of pair) fsm.alphabet.delete("@=@");
    }

    r = FST.re(".? (.-'@#@')* .? - $r", { r });
    const newfst = r.mapLabels({ "@#@": "" }).epsilonRemove().determinizeAsDFA().minimize();
    return this.become(newfst);
  }

  rewrite(...contexts: any): FST {
    // Flags are passed as last object literal; pyfoma stores them as strings 'True'
    let flags: {longest?: boolean, leftmost?: boolean, shortest?: boolean} = {};
    if (contexts.length && typeof contexts[contexts.length - 1] === "object" && !Array.isArray(contexts[contexts.length - 1])) {
      flags = contexts.pop();
    }

    const defs: {
      crossproducts: FST, br?: FST, aux?: FST, dotted?: FST, base?: FST, rule?: FST, remrewr?: FST,
      worsen?: FST, rewr?: FST
    } = { crossproducts: this.copyMod() };
    defs.br = FST.re("'@<@'|'@>@'");
    defs.aux = FST.re(". - ($br|#)", defs);
    defs.dotted = FST.re(".*-(.* '@<@' '@>@' '@<@' '@>@' .*)");
    defs.base = FST.re("$dotted @ # ($aux | '@<@' $crossproducts '@>@')* #", defs);

    if (contexts.length > 0) {
      const center = FST.re("'@<@' (.-'@>@')* '@>@'");
      const lrpairs = contexts.map(([l, r]: [FST, FST]) => [l.ignore(defs.br!), r.ignore(defs.br!)]);
      defs.rule = center.contextRestrict(...lrpairs, { rewrite: true }).compose(defs.base);
    } else {
      defs.rule = defs.base;
    }

    defs.remrewr = FST.re("'@<@':'' (.-'@>@')* '@>@':''");
    const worseners = [FST.re(".* $remrewr (.|$remrewr)*", defs)];

    const isTrue = (x: any) => x === true || x === "True";

    if (isTrue(flags.longest)) {
      worseners.push(FST.re(".* '@<@' $aux+ '':('@>@' '@<@'?) $aux ($br:''|'':$br|$aux)* .*", defs));
    }
    if (isTrue(flags.leftmost)) {
      worseners.push(FST.re(".* '@<@':'' $aux+ ('':'@<@' $aux* '':'@>@' $aux+ '@>@':'' .* | '':'@<@' $aux* '@>@':'' $aux* '':'@>@' .*)", defs));
    }
    if (isTrue(flags.shortest)) {
      worseners.push(FST.re(".* '@<@' $aux* '@>@':'' $aux+ '':'@>@' .*", defs));
    }

    let worsen = worseners[0];
    for (let i = 1; i < worseners.length; i++) worsen = worsen.union(worseners[i]);
    defs.worsen = worsen.determinizeUnweighted().minimize();

    defs.rewr = FST.re("$^output($^input($rule) @ $worsen)", defs);
    const final = FST.re("(.* - $rewr) @ $rule", defs);

    const newfst = final
      .mapLabels({ "@<@": "", "@>@": "", "#": "" })
      .epsilonRemove()
      .determinizeAsDFA()
      .minimize();

    return newfst;
  }

  mapLabels(mapping: {[src: string]: string}): FST {
    const mp = mapping;
    for (const s of this.states) {
      const newTrans = new Map();
      for (const { label, set } of s.transitions.values()) {
        const nl = label.map((sym) => (Object.prototype.hasOwnProperty.call(mp, sym) ? mp[sym] : sym));
        const k = labelKey(nl);
        if (!newTrans.has(k)) newTrans.set(k, { label: nl, set: new Set() });
        for (const t of set) {
          t.label = nl;
          newTrans.get(k).set.add(t);
        }
      }
      s.transitions = newTrans;
      s._invalidateIndexes();
    }
    // alphabet
    const newAlpha = new Set<string>();
    for (const sym of this.alphabet) newAlpha.add(Object.prototype.hasOwnProperty.call(mp, sym) ? mp[sym] : sym);
    this.alphabet = newAlpha;
    return this;
  }

  // ------------------------------------------------
  // Determinization / Minimization
  // ------------------------------------------------

  determinizeUnweighted(): FST {
    return this.determinize((s, _w) => [s, 0.0], (..._x) => 0.0);
  }

  determinizeAsDFA(): FST {
    const newfst = this.copyMod({
      modLabel: (l, w) => l.concat([String(w)]),
      modWeight: (_l, _w) => 0.0,
    });
    const det = newfst.determinizeUnweighted();
    const back = det.copyMod({
      modLabel: (l, _w) => l.slice(0, -1),
      modWeight: (l, _w) => parseFloat(l[l.length - 1]),
    });
    return this.become(back);
  }


  determinize(staterep: StateRepFunction = (s: State, w: number) => [s, w], oplus: OPlusFunction = Math.min): FST {
    // Weighted determinization (ported from pyfoma.py).
    // IMPORTANT: We represent a determinized-state as a Map keyed by "sid:residual"
    // so duplicates are collapsed by value (JS Sets can't dedupe arrays by value).
    const newfst = new FST({ alphabet: this.alphabet });

    // Pair keying helpers
    const pairKey = (s: State, r: number) => `${this._sid(s)}:${r}`;
    const repKey = (rep: Map<State, string>) => {
      const parts = Array.from(rep.keys());
      parts.sort();
      return parts.join(",");
    };

    const firstRep = new Map();
    {
      const pr = staterep(this.initialstate, 0.0);
      firstRep.set(pairKey(pr[0], pr[1]), pr);
    }

    const S = new Map();
    S.set(repKey(firstRep), newfst.initialstate);

    if (this.finalstates.has(this.initialstate)) {
      newfst.finalstates.add(newfst.initialstate);
      newfst.initialstate.finalweight = this.initialstate.finalweight;
    }

    const Q = [firstRep];
    while (Q.length) {
      const currentRep = Q.pop()!;
      const currentKey = repKey(currentRep);
      const srcState = S.get(currentKey);

      // Collect outgoing transitions by label.
      // Map<labelKey, {label, set: Array<[srcState, transition]>}>
      const collect = new Map();
      for (const [s, _r] of currentRep.values()) {
        for (const { label, set } of s.transitions.values()) {
          const lk = labelKey(label);
          if (!collect.has(lk)) collect.set(lk, { label, set: [] });
          const bucket = collect.get(lk).set;
          for (const t of set) bucket.push([s, t]);
        }
      }

      // Residual lookup for members of currentRep
      const residuals = new Map();
      for (const [s, r] of currentRep.values()) residuals.set(s, r);

      for (const { label, set: tset } of collect.values()) {
        // Compute wprime
        let wprime = floatInf();
        for (const [src, tr] of tset) {
          wprime = oplus(wprime, residuals.get(src) + tr.weight);
        }

        // Compute next-state representation (deduped by value)
        const nextRep = new Map();
        for (const [src, tr] of tset) {
          const rprime = residuals.get(src) + tr.weight - wprime;
          const pr = staterep(tr.targetstate, rprime);
          nextRep.set(pairKey(pr[0], pr[1]), pr);
        }

        const nextKey = repKey(nextRep);
        if (!S.has(nextKey)) {
          const ns = new State();
          S.set(nextKey, ns);
          newfst.states.add(ns);
          Q.push(nextRep);
        }

        srcState.addTransition(S.get(nextKey), label, wprime);

        // Final weights for the destination determinized state
        let bestFinal = floatInf();
        for (const [tstate, r] of nextRep.values()) {
          if (this.finalstates.has(tstate)) {
            bestFinal = Math.min(bestFinal, r + tstate.finalweight);
          }
        }
        const dest = S.get(nextKey);
        if (bestFinal < floatInf()) {
          newfst.finalstates.add(dest);
          dest.finalweight = Math.min(dest.finalweight, bestFinal);
        }
      }
    }

    newfst.alphabet = new Set(this.alphabet);
    return this.become(newfst);
  }

  // FIXME: This is one of several state to number mappings!
  __sidMap: Map<State, number> | null = null;

  _sid(s: State): number | undefined {
    if (!this.__sidMap) {
      this.__sidMap = new Map();
      let i = 0;
      for (const st of this.states) this.__sidMap.set(st, i++);
    }
    return this.__sidMap.get(s);
  }

  minimizeAsDFA(): FST {
    // Hopcroft-like DFA minimization (ported from pyfoma.py).
    // Assumes epsilon-free, deterministic machine.

    // Build reverse index: labelKey -> targetState -> Set(sourceStates)
    const reverseIndex = new Map();
    for (const s of this.states) {
      for (const [lbl, t] of s.allTransitions()) {
        const lk = labelKey(lbl);
        if (!reverseIndex.has(lk)) reverseIndex.set(lk, new Map());
        const m = reverseIndex.get(lk);
        if (!m.has(t.targetstate)) m.set(t.targetstate, new Set());
        m.get(t.targetstate).add(s);
      }
    }

    // Initial partition: finals (split by finalweight) vs nonfinals
    const finalsByWeight = new Map<number, Set<State>>();
    for (const f of this.finalstates) {
      const w = f.finalweight;
      if (!finalsByWeight.has(w)) finalsByWeight.set(w, new Set());
      finalsByWeight.get(w)!.add(f);
    }
    const nonfinals = setDifference(this.states, this.finalstates);

    const initialPartition = new Set<Set<State>>();
    for (const block of finalsByWeight.values()) if (block.size) initialPartition.add(block);
    if (nonfinals.size) initialPartition.add(nonfinals);

    const P = new PartitionRefinement(initialPartition);
    const agenda = new Set(initialPartition);

    const findSourceStates = (block: Set<State>) => {
      const out = [];
      for (const [lk, targetMap] of reverseIndex.entries()) {
        const sources = new Set();
        for (const tstate of block) {
          const srcs = targetMap.get(tstate);
          if (!srcs) continue;
          for (const s of srcs) sources.add(s);
        }
        if (sources.size) out.push([lk, sources]);
      }
      return out;
    };

    while (agenda.size) {
      const iter = agenda.values().next().value!;
      agenda.delete(iter);
      for (const [, sourcestates] of findSourceStates(iter)) {
        const splits = P.refine(sourcestates);
        for (const [newSet] of splits) agenda.add(newSet);
      }
    }

    const blocks = Array.from(P.sets.values());
    if (blocks.length === this.states.size) return this;

    // Representative for each state
    const rep = new Map();
    for (const block of blocks) {
      const first = block.values().next().value;
      for (const s of block) rep.set(s, first);
    }

    const representers = new Set(rep.values());
    const statemap = new Map();
    for (const s of representers) {
      statemap.set(s, new State({ finalweight: s.finalweight, name: s.name }));
    }

    const newfst = new FST({ alphabet: new Set(this.alphabet) });
    newfst.initialstate = statemap.get(rep.get(this.initialstate));

    // Copy transitions from representers only
    for (const s of representers) {
      const srcNew = statemap.get(s);
      for (const [lbl, t] of s.allTransitions()) {
        const dstNew = statemap.get(rep.get(t.targetstate));
        srcNew.addTransition(dstNew, lbl, t.weight);
      }
    }

    newfst.states = new Set(statemap.values());
    newfst.finalstates = new Set();
    for (const f of this.finalstates) {
      const rf = statemap.get(rep.get(f));
      newfst.finalstates.add(rf);
      // (Final weights are preserved by initial partition split.)
      rf.finalweight = rep.get(f).finalweight;
    }
    newfst.alphabet = new Set(this.alphabet);
    return this.become(newfst);
  }

  minimize(): FST {
    // For our purposes, minimize as DFA after determinizeAsDFA.
    return this.determinizeAsDFA().minimizeAsDFA();
  }

  // ------------------------
  // Labeling / cleanup
  // ------------------------

  labelStatesTopology(): FST {
    const Q = [this.initialstate];
    const inqueue = new Set([this.initialstate]);
    const c = new Counter();
    while (Q.length) {
      const s = Q.shift()!;
      s.name = String(c.next());
      for (const [, t] of s.allTransitions()) {
        if (!inqueue.has(t.targetstate)) {
          Q.push(t.targetstate);
          inqueue.add(t.targetstate);
        }
      }
    }
    return this;
  }

  cleanupSigma(): FST {
    const seen = new Set<string>();
    for (const [, lbl, ] of this.allTransitions(this.states)) {
      for (const sym of lbl) seen.add(sym);
    }
    if (!seen.has(".")) {
      this.alphabet = setIntersection(this.alphabet, seen);
    }
    return this;
  }

  // ------------------------
  // Apply / enumerate
  // ------------------------

  tokenizeAgainstAlphabet(word: string): string[] {
    const tokens = [];
    let start = 0;
    while (start < word.length) {
      let t = word[start];
      for (let len = 1; start + len <= word.length; len++) {
        const cand = word.slice(start, start + len);
        if (this.alphabet.has(cand)) t = cand;
      }
      tokens.push(t);
      start += t.length;
    }
    return tokens;
  }

  *apply(word: string,
         {inverse = false, weights = false}:
         {inverse?: boolean, weights?: boolean} = {}): Generator<[string, number] | string> {
    const IN = inverse ? (this._tapeCount() - 1) : 0;
    const OUT = inverse ? 0 : (this._tapeCount() - 1);

    const w = this.tokenizeAgainstAlphabet(word);
    const heap = new MinHeap<[number, number, string[], State | null]>();
    const cntr = new Counter();
    heap.push([0.0, [0, cntr.next(), [], this.initialstate]]); // cost, payload

    while (heap.size) {
      const [cost, payload] = heap.pop()!;
      const [negpos, _id, output, state] = payload;

      if (state === null && -negpos === w.length) {
        const outStr = output.join("");
        yield weights ? [outStr, cost] : outStr;
        continue;
      }
      if (state !== null) {
        if (this.finalstates.has(state)) {
          heap.push([cost + state.finalweight, [negpos, cntr.next(), output, null]]);
        }
        for (const [lbl, t] of state.allTransitions()) {
          const inSym = (lbl.length === 1) ? lbl[0] : lbl[IN];
          const outSym = (lbl.length === 1) ? lbl[0] : lbl[OUT];
          if (inSym === "") {
            heap.push([cost + t.weight, [negpos, cntr.next(), output.concat([outSym]), t.targetstate]]);
          } else if (-negpos < w.length) {
            const sym = w[-negpos];
            const nextsym = this.alphabet.has(sym) ? sym : ".";
            const appended = nextsym === "." ? sym : outSym;
            if (nextsym === inSym) {
              heap.push([cost + t.weight, [negpos - 1, cntr.next(), output.concat([appended]), t.targetstate]]);
            }
          }
        }
      }
    }
  }

  generate(word: string, {weights = false}: {weights?: boolean} = {}): Generator<[string, number] | string> {
    return this.apply(word, { inverse: false, weights });
  }

  analyze(word: string, {weights = false}: {weights?: boolean} = {}): Generator<[string, number] | string> {
    return this.apply(word, { inverse: true, weights });
  }

  _tapeCount(): number {
    // infer tape count from the maximum label length (labels may be mixed when acceptor arcs are collapsed)
    let m = 1;
    for (const s of this.states) {
      for (const { label } of s.transitions.values()) {
        if (label.length > m) m = label.length;
      }
    }
    return m;
  }

  *wordsCheapest(): Generator<[number, labelArray[]]> {
    const cntr = new Counter();
    const heap = new MinHeap<[number, State | null, labelArray[]]>();
    heap.push([0.0, [cntr.next(), this.initialstate, []]]);
    while (heap.size) {
      const [cost, payload] = heap.pop()!;
      const [_id, state, seq] = payload;
      if (state === null) {
        yield [cost, seq];
        continue;
      }
      if (this.finalstates.has(state)) {
        heap.push([cost + state.finalweight, [cntr.next(), null, seq]]);
      }
      for (const [label, t] of state.allTransitions()) {
        heap.push([cost + t.weight, [cntr.next(), t.targetstate, seq.concat([label])]]);
      }
    }
  }

  words() {
    // Alias for wordsCheapest
    return this.wordsCheapest();
  }

  // ------------------------------------------------
  // Alphabet harmonization (. expansion)
  // ------------------------------------------------


  _harmonizeAlphabet(other: FST): void {
    // Port of pyfoma.py's @harmonize_alphabet decorator:
    // If either machine contains '.' (sigma-wildcard), expand transitions that contain '.'
    // to explicitly cover symbols present in the other machine's alphabet.
    const setsEqual = <T>(A: Set<T>, B: Set<T>) => {
      if (A.size !== B.size) return false;
      for (const x of A) if (!B.has(x)) return false;
      return true;
    };

    const expandDots = (A: FST, B: FST) => {
      if (!A.alphabet.has('.')) return;

      const Ad = setDifference(A.alphabet, new Set(['.']));
      const Bd = setDifference(B.alphabet, new Set(['.']));
      if (setsEqual(Ad, Bd)) return;

      const Aexpand = setDifference(setDifference(B.alphabet, A.alphabet), new Set(['.', '']));
      if (!Aexpand.size) return;

      // Snapshot the transitions to expand so we don't mutate while iterating.
      const toExpand: [State, labelArray, Transition][] = [];
      for (const s of A.states) {
        for (const { label, set } of s.transitions.values()) {
          if (!label.includes('.')) continue;
          for (const t of set) toExpand.push([s, label, t]);
        }
      }

      for (const sym of Aexpand) {
        for (const [s, label, t] of toExpand) {
          const newLabel = label.map((lbl) => (lbl === '.' ? sym : lbl));
          s.addTransition(t.targetstate, newLabel, t.weight);
        }
        A.alphabet.add(sym);
      }
    };

    expandDots(this, other);
    expandDots(other, this);
  }
}

// Convenience exports
export const re = FST.re;
export const regex = FST.regex;
