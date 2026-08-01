// -*- js-indent-level: 2 -*-
/**
 * Lexd → PyFoma compiler

A JavaScript implementation of the Lexd formalism (inspired by Apertium's C++ lexd),
allowing compilation of Lexd grammars into finite-state transducers (FSTs)
using the PyFoma library.

Lexd is a concise, two-level description language that supports:
  - Multi-segment lexicon entries (for reduplication, circumfixation, etc.)
  - Pattern-based concatenation with alignment (:Lex, Lex:, Lex(i))
  - Tag-based selection/filtering ([count], [-mass], |[a,b], ^[x,y])
  - Anonymous lexicons and patterns
  - Quantifiers (?, *, +) and alternation (|)
  - Sieve operators (<, >)
  - Regular expressions in lexicon entries (/.../)

See: https://github.com/apertium/lexd/blob/main/Usage.md

Main entry point:

    compile(grammar: string) -> FST
        Compile a Lexd grammar string into a (minimized) PyFoma FST.

        Args:
            grammar: The full Lexd source code as a string.

        Returns:
            A pyfoma.FST representing the compiled transducer.


Usage example:


import { lexd_compile } from "pyfoma-js";

const grammar = `
PATTERNS
Prefix? NounStem NounNumber

LEXICON Prefix
ex-
anti-

LEXICON NounStem
cat
dog

LEXICON NounNumber
<sg>:
<pl>:s
`;

const myfst = lexd_compile(grammar);

# Generate surface forms
console.log(Array.from(myfst.generate("cat<pl>")));
# → ['cats']

# Analyze
console.log(Array.from(myfst.analyze("ex-dogs")));
# → ['ex-dog<pl>']

console.log(Array.from(myfst.analyze("cats")));
# → ['cat<pl>']
*/

import { FST, State, type Label } from "./pyfoma.js";

function epsilon_fst(): FST {
    return new FST({label: [""]});
}

/**
 * An empty-language FST with no transitions and no final states.
 * Avoids using empty_fst(), which introduces '[' and ']' into the alphabet.
 */
function empty_fst(): FST {
    return new FST();
}

function _normalize_label(label: Label): Label {
  if (label.length === 2 && label[0] === label[1]) {
    return [label[0]];
  }
  return label;
}

function union_all(fsts: FST[]): FST {
  let out: FST | null = null;
  for (const f of fsts) {
    if (out === null)
      out = f;
    else
      out = out.union(f);
  }
  return out || new FST();
}

/**
 * Create FST from list of list of labels (tuples of symbols).
 */
function from_tuples(tuples_iter: Label[][]): FST {
  const newfst = new FST();
  for (const tpls of tuples_iter) {
    let currstate = newfst.initialstate;
    for (const raw_label of tpls) {
      const label = _normalize_label(raw_label);
      for (const sym of label) {
        if (sym && !newfst.alphabet.has(sym))
          newfst.alphabet.add(sym);
      }
      const targetstate = new State();
      newfst.states.add(targetstate);
      currstate.addTransition(targetstate, label, 0.0);
      currstate = targetstate;
    }
    newfst.finalstates.add(currstate)
    currstate.finalweight = 0.0
  }
  return newfst;
}

/* ----------------------------------------
 * Tag selectors (DNF: OR of AND-clauses)
 * ----------------------------------------
 */

class TagSelector {
  clauses: [Set<string>, Set<string>][];

  constructor(clauses: [Set<string>, Set<string>][]) {
    this.clauses = clauses;
  }

  static make_any(): TagSelector {
    return new TagSelector([[new Set(), new Set()]]);
  }

  // Necessary because JSON.stringify always returns {} for a Set!
  toArray(): string {
    return JSON.stringify(this,
                          (_key, value) => {
                            if (value instanceof Set)
                              return Array.from(value);
                            return value;
                          });
  }

  matches(tags: Set<string>): boolean {
    for (const [must, mustnot] of this.clauses)
      if (isSubset(must, tags) && isDisjoint(mustnot, tags))
        return true;
    return false;
  }

  and_selector(other: TagSelector): TagSelector {
    const new_clauses: Array<[Set<string>, Set<string>]> = [];
    for (const [m1, n1] of this.clauses)
      for (const [m2, n2] of other.clauses)
        new_clauses.push([union_sets(m1, m2), union_sets(n1, n2)]);
    return new TagSelector(new_clauses);
  }
}

function isSubset<T>(a: Set<T>, b: Set<T>): boolean {
  for (const item of a)
    if (!b.has(item)) return false;
  return true;
}

function isDisjoint<T>(a: Set<T>, b: Set<T>): boolean {
  for (const item of a)
    if (b.has(item)) return false;
  return true;
}

function union_sets<T>(a: Set<T>, b: Set<T>): Set<T> {
  const result = new Set(a);
  for (const item of b)
    result.add(item);
  return result;
}

function _split_top_level_commas(s: string): string[] {
  const parts: string[] = [];
  let buf: string[] = [];
  let depth = 0;
  for (const ch of s) {
    if (ch === "[") {
      depth++;
    } else if (ch === "]") {
      depth--;
    }
    if (ch === "," && depth === 0) {
      const part = buf.join("").trim();
      if (part) parts.push(part);
      buf = [];
    } else {
      buf.push(ch);
    }
  }
  const tail = buf.join("").trim();
  if (tail) parts.push(tail);
  return parts;
}

/**
 * Split a trailing tag-selector suffix '[...]' from a token, supporting nested brackets.
 *
 * Examples:
 *   'A[count]' -> ('A', '[count]')
 *   'A[|[a,b]]' -> ('A', '[|[a,b]]')
 *   '(A B)[^[x,y]]' (handled at expr level, but same logic)
*/
function _split_selector_suffix(tok: string): [string, string | null] {
  tok = tok.trim();
  if (!tok.endsWith("]")) {
    return [tok, null];
  }
  let depth = 0;
  for (let i = tok.length - 1; i >= 0; i--) {
    const c = tok[i];
    if (c === "]") {
      depth++;
    } else if (c === "[") {
      depth--;
      if (depth === 0) {
        return [tok.substring(0, i), tok.substring(i)];
      }
    }
  }
  return [tok, null];
}

function parse_tag_selector(raw: string): TagSelector {
  raw = raw.trim();
  if (!raw)
    return TagSelector.make_any();

  const components = _split_top_level_commas(raw);
  let sel = TagSelector.make_any();

  for (const comp of components) {
    const trimmedComp = comp.trim();
    if (!trimmedComp) continue;

    const matchOr = trimmedComp.match(/^\|\[(.*)\]$/);
    if (matchOr) {
      const items = matchOr[1].split(",").map(x => x.trim()).filter(x => x);
      const comp_sel = new TagSelector(items.map(it => [new Set([it]), new Set()]))
      sel = sel.and_selector(comp_sel);
      continue;
    }

    const matchXor = trimmedComp.match(/^\^\[(.*)\]$/);
    if (matchXor) {
      const items = matchXor[1].split(",").map(x => x.trim()).filter(x => x);
      const clauses: Array<[Set<string>, Set<string>]> = [];
      for (const it of items) {
        const others = new Set(items);
        others.delete(it);
        clauses.push([new Set([it]), others]);
      }
      const comp_sel = new TagSelector(clauses);
      sel = sel.and_selector(comp_sel);
      continue;
    }

    let comp_sel: TagSelector;
    if (trimmedComp.startsWith("-"))
      comp_sel = new TagSelector([[new Set(), new Set([trimmedComp.substring(1)])]]);
    else 
      comp_sel = new TagSelector([[new Set([trimmedComp]), new Set()]]);
    sel = sel.and_selector(comp_sel);
  }
  return sel;
}

/* ----------------------------------------
 * Lexicon parsing helpers
 * ----------------------------------------
 */

const _TAG_RE = /\[([^\]]*)\]\s*$/;

function _split_tags(s: string): [string, Set<string>] {
  s = s.trimEnd();
  const m = _TAG_RE.exec(s);
  if (!m) {
    return [s, new Set()];
  }
  const tagraw = m[1];
  const base = s.substring(0, m.index).trimEnd();
  const tags = new Set(tagraw.split(",").map(t => t.trim()).filter(t => t));
  return [base, tags];
}

/**
 * Rewrite lexd-style <...> and {...} tokens into PyFoma multichar symbols for regex compilation.
 *
 *  PyFoma treats anything inside single quotes as a multichar symbol, so we rewrite:
 *    <sent>  -> '<sent>'
 *    {A}     -> '{A}'
 *  but we do NOT touch content already inside single quotes.
 */
function _quote_multichar_for_pyfoma_regex(regex: string): string {
  const out: string[] = [];
  let i = 0;
  let in_q = false;
  while (i < regex.length) {
    const ch = regex[i];
    if (ch === "'") {
      in_q = !in_q;
      out.push(ch);
      i++;
      continue;
    }
    if (!in_q && ch === "<") {
      const j = regex.indexOf(">", i + 1);
      if (j === -1) {
        throw new Error(`Unclosed <...> in regex: ${regex}`);
      }
      const token = regex.substring(i, j + 1);
      out.push("'" + token + "'");
      i = j + 1;
      continue;
    }
    if (!in_q && ch === "{") {
      const j = regex.indexOf("}", i + 1);
      if (j === -1) {
        throw new Error(`Unclosed {...} in regex: ${regex}`);
      }
      const token = regex.substring(i, j + 1);
      out.push("'" + token + "'");
      i = j + 1;
      continue;
    }
    out.push(ch);
    i++;
  }
  return out.join("");
}

/**
 * Split regex at the first top-level ':' (not inside quotes or parentheses/brackets).
 *
 * Returns (left, right) or None if no top-level ':' exists.
 */
function _split_top_level_colon(regex: string): [string, string] | null {
  let in_q = false;
  let depth_paren = 0;
  let depth_brack = 0;
  let esc = false;
  for (let i = 0; i < regex.length; i++) {
    const ch = regex[i];
    if (esc) {
      esc = false;
      continue;
    }
    if (ch === "\\") {
      esc = true;
      continue;
    }
    if (ch === "'") {
      in_q = !in_q;
      continue;
    }
    if (in_q) {
      continue;
    }
    if (ch === "(") {
      depth_paren++;
      continue;
    }
    if (ch === ")") {
      depth_paren = Math.max(0, depth_paren - 1);
      continue;
    }
    if (ch === "[") {
      depth_brack++;
      continue;
    }
    if (ch === "]") {
      depth_brack = Math.max(0, depth_brack - 1);
      continue;
    }
    if (ch === ":" && depth_paren === 0 && depth_brack === 0) {
      return [regex.substring(0, i), regex.substring(i + 1)];
    }
  }
  return null;
}

/**
 * Ensure correct precedence for a single top-level cross-product operator ':'.
 *
 * PyFoma's ': ' binds tighter than concatenation. Lexd users typically intend
 * the whole expression left of ':' and the whole expression right of ':' to be the operands.
 *
 * Notes for PyFoma:
 *   * A missing left or right operand(e.g. 'a:' or ':b') should be treated as epsilon (''), but
 *     PyFoma's regex parser does not accept a bare missing operand, so we insert '' explicitly.
 *   * We only rewrite when there is a * top - level * ':' in the regex.
 */
function _wrap_top_level_colon_operands(regex: string): string {
  const split = _split_top_level_colon(regex);
  if (split === null) {
    return regex;
  }
  let [left, right] = split;
  left = left.trim();
  right = right.trim();

  if (left === "") {
    left = "''";
  } else if (!(left.startsWith("(") && left.endsWith(")"))) {
    left = `(${left})`;
  }

  if (right === "") {
    right = "''";
  } else if (!(right.startsWith("(") && right.endsWith(")"))) {
    right = `(${right})`;
  }

  return `${left}:${right}`;
}

function _tokenize_symbols(x: string, strict_quoted: boolean = false): string[] {
  x = x.trim();
  const out: string[] = [];
  let i = 0;
  while (i < x.length) {
    if (x[i] === "'") {
      // Single-quoted multichar symbol in plain lexicon entries.
      // Tolerant default: if unmatched, keep "'" as a literal symbol.
      const buf: string[] = [];
      let j = i + 1;
      let closed = false;
      while (j < x.length) {
        const ch = x[j];
        if (ch === "\\") {
          if (j + 1 >= x.length) {
            throw new Error(`Dangling escape in single-quoted symbol in ${x}`);
          }
          const nxt = x[j + 1];
          if (nxt === "\\" || nxt === "'") {
            buf.push(nxt);
          } else {
            // Preserve other escaped chars literally (without backslash).
            buf.push(nxt);
          }
          j += 2;
          continue;
        }
        if (ch === "'") {
          closed = true;
          break;
        }
        buf.push(ch);
        j++;
      }
      if (closed) {
        out.push(buf.join(""));
        i = j + 1;
        continue;
      }
      if (strict_quoted) {
        throw new Error(`Unclosed single-quoted symbol in ${x}`);
      }
      out.push("'");
      i++;
      continue;
    }
    if (x[i] === "<") {
      const j = x.indexOf(">", i + 1);
      if (j === -1) {
        throw new Error(`Unclosed <...> tag in ${x}`);
      }
      out.push(x.substring(i, j + 1));
      i = j + 1;
      continue;
    }
    if (x[i] === "{") {
      const j = x.indexOf("}", i + 1);
      if (j === -1) {
        throw new Error(`Unclosed {...} archisymbol in ${x}`);
      }
      out.push(x.substring(i, j + 1));
      i = j + 1;
      continue;
    }
    out.push(x[i]);
    i++;
  }
  return out;
}

interface LexEntry {
  cols: string[];
  tags: Set<string>;
}

interface LexiconDef {
  name: string;
  arity: number;
  entries: LexEntry[];
}

type TokRefKind = "lex" | "anonlex" | "pair";
type TokRefSide = "both" | "in" | "out";

interface TokRef {
  kind: TokRefKind;
  name: string;
  // For kind == 'lex': col is Optional[int] or Optional[tuple[int,int]] (for X(i):X(j) same-lex dual-col)
  // For kind == 'pair': col is tuple[int,int] = (left_col, right_col) and left/right store lexicon names.
  col: number | [number, number] | null;
  side: TokRefSide;
  selector: TagSelector;
  left?: string;
  right?: string;
}

abstract class PatExpr {}

class Seq extends PatExpr {
  constructor(public parts: PatExpr[]) {
    super();
  }
}

class Alt extends PatExpr {
  constructor(public alts: PatExpr[]) {
    super();
  }
}

class Ref extends PatExpr {
  constructor(public token: TokRef) {
    super();
  }
}

class Quant extends PatExpr {
  constructor(public expr: PatExpr, public q: string) {
    super();
  }
}

class Tagged extends PatExpr {
  constructor(public expr: PatExpr, public selector: TagSelector) {
    super();
  }
}

interface ParsedLexd {
  patterns: Map<string, PatExpr>;
  top_patterns: PatExpr[];
  lexicons: Map<string, LexiconDef>;
  aliases: Map<string, string>;
}

/* ----------------------------------------
 * Pattern tokenizer / parser
 * ----------------------------------------
 */

function _tokenize_pattern_line(line: string): string[] {
  const s = line.trim();
  const out: string[] = [];
  let i = 0;
  const n = s.length;

  function skip_ws(k: number): number {
    while (k < n && /\s/.test(s[k])) {
      k++;
    }
    return k;
  }

  function read_balanced_brackets(k: number): [string, number] {
    let depth = 0;
    let j = k;
    while (j < n) {
      if (s[j] === "[") {
        depth++;
      } else if (s[j] === "]") {
        depth--;
        if (depth === 0) {
          return [s.substring(k, j + 1), j + 1];
        }
      }
      j++;
    }
    throw new Error("Unclosed [...] in pattern line");
  }

  while (true) {
    i = skip_ws(i);
    if (i >= n) {
      break;
    }
    const c = s[i];

    if (/^[|?\*+<>]$/.test(c)) {
      // lexd quirk: '|' can be used without surrounding whitespace (e.g. X(1)|Y(1)),
      // and in that case it groups tighter than whitespace concatenation. We encode this
      // as a distinct token so the parser can give it higher precedence.
      if (c === "|") {
        const prev = i > 0 ? s[i - 1] : " ";
        const nxt = i + 1 < n ? s[i + 1] : " ";
        out.push(!/^\s/.test(prev) && !/^\s/.test(nxt) ? "__TIGHTOR__" : "|");
      } else {
        out.push(c);
      }
      i++;
      continue;
    }
    if (c === "(" || c === ")") {
      out.push(c);
      i++;
      continue;
    }
    if (c === "[") {
      const [bracket, j] = read_balanced_brackets(i);
      const content = bracket.substring(1, bracket.length - 1).trim();
      // Disambiguation:
      //   * If '[' is preceded by whitespace (or is at start), treat as an anonymous lexicon atom: [ ... ]
      //   * Otherwise (e.g. immediately after ')'), treat as a selector postfix on the previous expression.
      if (i === 0 || /^\s/.test(s[i - 1])) {
        out.push("[");
        if (content) {
          out.push(content);
        }
        out.push("]");
      } else {
        out.push(`__POSTSEL__:${content}`);
      }
      i = j;
      continue;
    }

    // TODO: This could all be done with regexps
    let j = i;
    while (j < n && !/^[\s|?*+<>\[\]()]/.test(s[j])) j++;
    let tok = s.substring(i, j);

    // Special lexd syntax: NAME?(N) means the NAME(N) token is optional.
    // We tokenize it as: NAME(N) followed by '?' so the parser sees a Ref with column,
    // then applies the '?' quantifier to that Ref.
    if (j < n && s[j] === "?" && j + 1 < n && s[j + 1] === "(") {
      let k = j + 2;
      while (k < n && /^\d/.test(s[k])) {
        k++;
      }
      if (k > j + 2 && k < n && s[k] === ")") {
        tok = tok + s.substring(j + 1, k + 1);
        j = k + 1;
        out.push(tok);
        out.push("?");
        i = j;
        continue;
      }
    }

    if (j < n && s[j] === "(") {
      let k = j + 1;
      while (k < n && /^\d/.test(s[k])) {
        k++;
      }
      if (k > j + 1 && k < n && s[k] === ")") {
        tok = tok + s.substring(j, k + 1);
        j = k + 1;
      }
    }

    if (j < n && s[j] === "[") {
      const [bracket, j2] = read_balanced_brackets(j);
      tok = tok + bracket;
      j = j2;
    }

    // A ':' immediately after a token can be either:
    //  - a one-sided marker (e.g. Lex:) when followed by whitespace/end/operator, OR
    //  - an internal ':' (e.g. x(1):y(2)) which must remain inside the token.
    if (j < n && s[j] === ":") {
      // Suffix ':' (one-sided marker)
      const nxt = j + 1 < n ? s[j + 1] : "";
      if (j + 1 === n || /^[\s|?*+<>\[\]()]/.test(nxt)) {
        tok = tok + ":";
        j++;
      } else {
        // Internal ':': keep consuming ':' + following segment(s) as part of this token.
        while (j < n && s[j] === ":") {
          tok += ":";
          j++;
          let k = j;
          while (k < n && !/^[\s|?*+<>\[\]]/.test(s[k])) k++;
          tok += s.substring(j, k);
          j = k;
        }
      }
    }

    out.push(tok);
    i = j;
  }

  return out;
}

function _expand_sieve_line(line: string): string[] {
  const s = line.trim();
  if (!/[<>]/.test(s))
    return [s];

  function has_toplevel_or(seg: string): boolean {
    let depth_par = 0;
    let depth_sq = 0;
    let in_regex = false;
    let esc = false;
    for (const ch of seg) {
      if (esc) {
        esc = false;
        continue;
      }
      if (ch === "\\") { // escape
        esc = true;
        continue;
      }
      if (in_regex) {
        if (ch === "/") {
          in_regex = false;
        }
        continue;
      }
      if (ch === "/") {
        in_regex = true;
        continue;
      }
      if (ch === "(") {
        depth_par++;
        continue;
      }
      if (ch === ")") {
        depth_par = Math.max(0, depth_par - 1);
        continue;
      }
      if (ch === "[") {
        depth_sq++;
        continue;
      }
      if (ch === "]") {
        depth_sq = Math.max(0, depth_sq - 1);
        continue;
      }
      if (ch === "|" && depth_par === 0 && depth_sq === 0) {
        return true;
      }
    }
    return false;
  }

  function protect(seg: string): string {
    seg = seg.trim();
    if (has_toplevel_or(seg)) {
      return `(${seg})`;
    }
    return seg;
  }

  const segs: string[] = [];
  const ops: string[] = [];

  const buf: string[] = [];
  let depth_par = 0;
  let depth_sq = 0;
  let in_regex = false;
  let esc = false;

  function flush_buf(): void {
    const seg = buf.join("").trim();
    buf.length = 0;
    if (seg) {
      segs.push(seg);
    }
  }

  let i = 0;
  const n = s.length;
  while (i < n) {
    const ch = s[i];
    if (esc) {
      buf.push(ch);
      esc = false;
      i++;
      continue;
    }
    if (ch === "\\") { // escape
      buf.push(ch);
      esc = true;
      i++;
      continue;
    }
    if (in_regex) {
      buf.push(ch);
      if (ch === "/") {
        in_regex = false;
      }
      i++;
      continue;
    }
    if (ch === "/") {
      buf.push(ch);
      in_regex = true;
      i++;
      continue;
    }
    if (ch === "(") {
      depth_par++;
      buf.push(ch);
      i++;
      continue;
    }
    if (ch === ")") {
      depth_par = Math.max(0, depth_par - 1);
      buf.push(ch);
      i++;
      continue;
    }
    if (ch === "[") {
      depth_sq++;
      buf.push(ch);
      i++;
      continue;
    }
    if (ch === "]") {
      depth_sq = Math.max(0, depth_sq - 1);
      buf.push(ch);
      i++;
      continue;
    }

    // Detect sieve operator at top level, requiring whitespace around.
    if (depth_par === 0 && depth_sq === 0 && /^[<>]/.test(ch)) {
      const prev = i > 0 ? s[i - 1] : " ";
      const nxt = i + 1 < n ? s[i + 1] : " ";
      if (/^\s/.test(prev) && /^\s/.test(nxt)) {
        flush_buf();
        ops.push(ch);
        i++;
        continue;
      }
    }

    buf.push(ch);
    i++;
  }

  flush_buf();

  if (ops.length === 0) return [s];
  if (ops.length !== Math.max(0, segs.length - 1))
    return [s];

  const out_lines: string[] = [];
  const k = segs.length;
  for (let start = 0; start < k; start++) {
    if (start > 0 && ops[start - 1] === ">") {
      continue;
    }
    for (let end = start; end < k; end++) {
      if (end < k - 1 && ops[end] === "<") {
        continue;
      }
      const pieces = segs.slice(start, end + 1).map(protect);
      out_lines.push(pieces.join(" "));
    }
  }
  return out_lines;
}

function _parse_token_ref(tok: string): TokRef {
  let side: TokRefSide = "both";
  if (tok.startsWith(":")) {
    side = "out";
    tok = tok.substring(1);
  }
  if (tok.endsWith(":")) {
    if (side === "both") {
      side = "in";
    }
    tok = tok.substring(0, tok.length - 1);
  }

  let selector = TagSelector.make_any();
  const [base, sel] = _split_selector_suffix(tok);
  if (sel !== null) {
    tok = base;
    selector = parse_tag_selector(sel.substring(1, sel.length - 1));
  }

  // Special lexd syntax: X(1):X(2) binds the same lexicon entry while using different columns
  // on the input/output side. (This is NOT the regex cross-product operator.)
  if (tok.includes(":")) {
    const [left, right] = tok.split(":", 2);
    const m1 = left.match(/^(.+?)\((\d+)\)$/);
    const m2 = right.match(/^(.+?)\((\d+)\)$/);
    if (m1 && m2 && m1[1] === m2[1]) {
      const name = m1[1];
      const col_in = parseInt(m1[2], 10);
      const col_out = parseInt(m2[2], 10);
      return {
        kind: "lex",
        name,
        col: [col_in, col_out],
        side: "both",
        selector
      };
    }
  }

  // Cross-lexicon pairing syntax: x(i):y(j)
  const mxy = tok.match(/^(.+?)\((\d+)\):(.+?)\((\d+)\)$/);
  if (mxy) {
    const lx = mxy[1];
    const ci = parseInt(mxy[2], 10);
    const ly = mxy[3];
    const co = parseInt(mxy[4], 10);
    return {
      kind: "pair",
      name: `${lx}:${ly}`,
      col: [ci, co],
      side: "both",
      selector,
      left: lx,
      right: ly
    };
  }

  let col: number | null = null;
  const m = tok.match(/^(.+?)\((\d+)\)$/);
  if (m) {
    tok = m[1];
    col = parseInt(m[2], 10);
  }

  return {
    kind: "lex",
    name: tok,
    col,
    side,
    selector
  };
}

function _parse_pattern_expr(tokens: string[], pos: number = 0): [PatExpr, number] {
  function parse_atom(p: number): [PatExpr, number] {
    if (tokens[p] === "(") {
      const [e, p2] = parse_alt(p + 1);
      if (p2 >= tokens.length || tokens[p2] !== ")") {
        throw new Error("missing )");
      }
      return [e, p2 + 1];
    }

    if (tokens[p] === "[") {
      let raw = "";
      if (p + 1 < tokens.length && tokens[p + 1] !== "]") {
        raw = tokens[p + 1];
        p = p + 1;
      }
      if (p + 1 >= tokens.length || tokens[p + 1] !== "]") {
        throw new Error("missing ] in anonymous lexicon");
      }
      const anon_name = `__ANONLEX__:${raw.trim()}`;
      return [new Ref({ kind: "anonlex", col: null, name: anon_name, side: "both", selector: TagSelector.make_any() }), p + 2];
    }

    return [new Ref(_parse_token_ref(tokens[p])), p + 1];
  }

  function parse_postfix(p: number): [PatExpr, number] {
    let [e, p_] = parse_atom(p);
    while (p_ < tokens.length && /^[?*+]$/.test(tokens[p_])) {
      e = new Quant(e, tokens[p_]);
      p_++;
    }
    return [e, p_];
  }

  function parse_concat(p: number): [PatExpr, number] {
    const parts: PatExpr[] = [];
    while (p < tokens.length && !/^[)|<>]$/.test(tokens[p])) {
      let [e, p_] = parse_postfix(p);
      // Higher-precedence OR for '|' with no surrounding whitespace (tokenized as __TIGHTOR__).
      if (p_ < tokens.length && tokens[p_] === "__TIGHTOR__") {
        const alts = [e];
        while (p_ < tokens.length && tokens[p_] === "__TIGHTOR__") {
          const [e2, p2] = parse_postfix(p_ + 1);
          alts.push(e2);
          p_ = p2;
        }
        e = new Alt(alts);
      }

      while (p_ < tokens.length && tokens[p_].startsWith("__POSTSEL__:")) {
        const raw = tokens[p_].substring("__POSTSEL__:".length);
        const sel = parse_tag_selector(raw.trim());
        e = new Tagged(e, sel);
        p_++;
      }

      parts.push(e);
      p = p_;
    }

    if (parts.length === 0)
      return [new Seq([]), p];
    if (parts.length === 1)
      return [parts[0], p];
    return [new Seq(parts), p];
  }

  function parse_alt(p: number): [PatExpr, number] {
    let e;
    [e, p] = parse_concat(p);
    const alts = [e];
    while (p < tokens.length && tokens[p] === "|") {
      let e2;
      [e2, p] = parse_concat(p + 1);
      alts.push(e2);
    }
    if (alts.length === 1)
      return [alts[0], p];
    return [new Alt(alts), p];
  }

  return parse_alt(pos);
}

/* ----------------------------------------
 * Selector distribution
 * ----------------------------------------
 */

function _selector_to_atomic_and_list(selector: TagSelector): TagSelector[] {
  if (selector.clauses.length !== 1)
    return [selector];
  const [must, mustnot] = selector.clauses[0];
  const atoms: TagSelector[] = [];
  const mustArray = Array.from(must).sort();
  const mustnotArray = Array.from(mustnot).sort();
  for (const t of mustArray)
    atoms.push(new TagSelector([[new Set([t]), new Set()]]));
  for (const t of mustnotArray)
    atoms.push(new TagSelector([[new Set(), new Set([t])]]));
  return atoms;
}

function _apply_selector_distribution(expr: PatExpr, selector: TagSelector): PatExpr {
  if (selector.clauses.length > 1) {
    return new Alt(
      selector.clauses.map(cl => _apply_selector_distribution(expr, new TagSelector([cl])))
    );
  }
  let out: PatExpr = expr;
  for (const atom of _selector_to_atomic_and_list(selector))
    out = _apply_selector_distribution_single(out, atom);
  return out;
}

function _apply_selector_distribution_single(expr: PatExpr, selector: TagSelector): PatExpr {
  const [must, mustnot] = selector.clauses[0];
  if (must.size === 0 && mustnot.size === 0)
    return expr;

  function apply_to_ref(r: Ref): Ref {
    const t = r.token;
    return new Ref({
      kind: t.kind,
      name: t.name,
      col: t.col,
      side: t.side,
      selector: t.selector.and_selector(selector)
    });
  }

  if (expr instanceof Ref)
    return apply_to_ref(expr);
  if (expr instanceof Quant)
    return new Quant(_apply_selector_distribution_single(expr.expr, selector), expr.q);
  if (expr instanceof Alt)
    return new Alt(expr.alts.map(a => _apply_selector_distribution_single(a, selector)));

  if (expr instanceof Seq) {
    if (mustnot.size > 0 && must.size === 0)
      return new Seq(expr.parts.map(p => _apply_selector_distribution_single(p, selector)));
    if (must.size > 0 && mustnot.size === 0) {
      const alts: PatExpr[] = [];
      for (let i = 0; i < expr.parts.length; i++) {
        const new_parts: PatExpr[] = [];
        for (let j = 0; j < expr.parts.length; j++) {
          new_parts.push(j === i ? _apply_selector_distribution_single(expr.parts[j], selector) : expr.parts[j]);
        }
        alts.push(new Seq(new_parts));
      }
      return new Alt(alts);
    }
    return new Seq(expr.parts.map(p => _apply_selector_distribution_single(p, selector)));
  }

  return expr;
}

/* ----------------------------------------
 * parse_lexd
 * ----------------------------------------
 */

const _SECTION_RE = /^(PATTERNS|PATTERN|LEXICON|ALIAS)\b/;

/**
 * Strip an inline '#' comment, but only when the '#' is not escaped.

 * IMPORTANT: we *preserve* backslash escapes in the returned string (e.g. "ya\ ngáí"),
 * because later parsing needs to see them to keep escaped spaces inside a single column.
 */
function _strip_inline_comment(s: string): string {
  const out: string[] = [];
  let esc = false;
  for (const ch of s) {
    if (esc) {
      // keep the escaped character, and keep the preceding backslash as well
      out.push("\\");
      out.push(ch);
      esc = false;
      continue;
    }
    if (ch === "\\") {
      esc = true;
      continue;
    }
    if (ch === "#") break;
    out.push(ch);
  }
  if (esc)
    out.push("\\");
  return out.join("").trimEnd();
}

/**
 * Expand lexd syntax NAME?(N) meaning the whole lexicon NAME is optional in this PATTERNS line.
 */
function _expand_optional_segmented_lexicons(line: string): string[] {
  const rx = /(:?)([A-Za-z_][\w\-]*)\?\((\d+)\)(:?)/g;
  const bases = Array.from(new Set(Array.from(line.matchAll(rx)).map(m => m[2]))).sort();
  if (bases.length === 0)
    return [line];
  let expanded = [line];
  for (const base of bases) {
    const new_expanded: string[] = [];
    function incl(match: RegExpMatchArray): string {
      const [, pre, name, idx, post] = match;
      if (name !== base)
        return match[0];
      return `${pre}${name}(${idx})${post}`;
    }
    function excl(match: RegExpMatchArray): string {
      if (match[2] !== base)
        return match[0];
      return "";
    }
    for (const ln of expanded) {
      const inc = ln.replace(
        rx,
        (_, pre, name, idx, post) => incl([_, pre, name, idx, post]))
            .split(/\s+/).filter((x) => x).join(" ");
      const exc = ln.replace(
        rx,
        (_, pre, name, idx, post) => excl([_, pre, name, idx, post]))
            .split(/\s+/).filter((x) => x).join(" ");
      if (inc) new_expanded.push(inc);
      if (exc) new_expanded.push(exc);
    }
    expanded = new_expanded;
  }
  // dedupe preserve order
  const out: string[] = [];
  const seen = new Set<string>();
  for (const ln of expanded) {
    if (!seen.has(ln)) {
      seen.add(ln);
      out.push(ln);
    }
  }
  return out;
}

/**
 * Split a line into whitespace-separated fields, honoring backslash escapes.

 * Example: 'ya\ ngáí <tag>:' -> ['ya ngáí', '<tag>:']
 * Backslash escapes the next character (space, '#', backslash, etc.).
 */
function _split_escaped_fields(line: string): string[] {
  const fields: string[] = [];
  const buf: string[] = [];
  let in_quote = false;
  let in_ws = true;
  let i = 0;
  while (i < line.length) {
    const ch = line[i];

    if (in_quote) {
      if (ch === "\\") {
        if (i + 1 < line.length) {
          // Preserve backslash escapes verbatim inside quoted symbols;
          // quote parsing is handled in _tokenize_symbols().
          buf.push("\\");
          buf.push(line[i + 1]);
          i += 2;
        } else {
          buf.push("\\");
          i++;
        }
        in_ws = false;
        continue;
      }
      if (ch === "'") {
        in_quote = false;
        buf.push(ch);
        i++;
        in_ws = false;
        continue;
      }
      buf.push(ch);
      i++;
      in_ws = false;
      continue;
    }

    if (ch === "'") {
      in_quote = true;
      buf.push(ch);
      i++;
      in_ws = false;
      continue;
    }
    if (ch === "\\") {
      if (i + 1 < line.length) {
        // Outside quotes, backslash escapes the next char into the same field.
        buf.push(line[i + 1]);
        i += 2;
      } else {
        buf.push("\\");
        i++;
      }
      in_ws = false;
      continue;
    }
    if (/\s/.test(ch)) {
      if (!in_ws) {
        fields.push(buf.join(""));
        buf.length = 0;
        in_ws = true;
      }
      i++;
      continue;
    }
    buf.push(ch);
    i++;
    in_ws = false;
  }
  if (buf.length > 0) {
    fields.push(buf.join(""));
  }
  return fields;
}

function _parse_line_to_exprs(line: string, for_patterns_section: boolean): PatExpr[] {
  const exprs: PatExpr[] = [];
  const linesToProcess = for_patterns_section ? _expand_optional_segmented_lexicons(line) : [line];
  for (const ln of linesToProcess) {
    for (const ln2 of _expand_sieve_line(ln)) {
      const toks = _tokenize_pattern_line(ln2);
      const [expr, p] = _parse_pattern_expr(toks, 0);
      if (p !== toks.length) {
        const sect = for_patterns_section ? "PATTERNS" : "PATTERN";
        throw new Error(`Could not parse full ${sect} line: ${ln}`);
      }
      exprs.push(expr);
    }
  }
  return exprs;
}

export function parse_lexd(lexdstring: string): ParsedLexd {
  const lines = lexdstring.split("\n");
  let mode: "PATTERNS" | "PATTERN" | "LEXICON" | "ALIAS" | null = null;
  let curr_name: string | null = null;
  let curr_block_default_tags = new Set<string>();

  const patterns = new Map<string, PatExpr>();
  const top_patterns: PatExpr[] = [];
  const lexicons = new Map<string, LexiconDef>();
  const aliases = new Map<string, string>();

  let i = 0;
  while (i < lines.length) {
    const raw = lines[i];
    let line = raw.trim();
    i++;
    line = _strip_inline_comment(line);
    if (!line || line.startsWith("#")) {
      continue;
    }

    const m = _SECTION_RE.exec(line);
    if (m) {
      const head = m[1];
      if (head === "PATTERNS") {
        mode = "PATTERNS";
        curr_name = null;
        continue;
      }
      if (head === "PATTERN") {
        mode = "PATTERN";
        curr_name = line.split(/\s+/)[1];
        patterns.set(curr_name, new Seq([]));
        continue;
      }
      if (head === "LEXICON") {
        mode = "LEXICON";
        const rest_raw = line.split(/\s+/, 2)[1];

        // Lexicon definition tags may appear as:
        //   LEXICON A[x]
        // or with side - specific defaults:
        //   LEXICON B[x]: [y]
        // These tags are defaults for the block(not emitted as symbols).
        let out_tags = new Set<string>();
        const idxc = rest_raw.indexOf(":["); // sad robot
        let rest: string;
        if (idxc != -1) {
          const left_raw = rest_raw.substring(0, idxc);
          const right_raw = rest_raw.substring(idxc + 1);  // starts with '[...]'
          [, out_tags] = _split_tags(right_raw);
          rest = left_raw;
        }
        else
          rest = rest_raw;

        let [name_part, default_tags] = _split_tags(rest);
        for (const tag of out_tags)
          default_tags.add(tag);

        let arity = 1;
        const m2 = name_part.match(/^(.+?)\((\d+)\)$/);
        if (m2) {
          name_part = m2[1];
          arity = parseInt(m2[2], 10);
        }

        if (!lexicons.has(name_part))
          lexicons.set(name_part, { name: name_part, arity, entries: [] });
        else if (lexicons.get(name_part)!.arity != arity)
          throw new Error(`Lexicon ${name_part} arity mismatch across blocks.`);

        curr_name = name_part;
        curr_block_default_tags = default_tags;
        continue;
      }
      if (head === "ALIAS") {
        const [, src, dst] = line.split(/\s+/);
        aliases.set(dst, src);
        continue;
      }
    }
    if (mode === "PATTERNS") {
      top_patterns.push(..._parse_line_to_exprs(line, true));
      continue;
    }
    if (mode === "PATTERN") {
      const exprs = _parse_line_to_exprs(line, false);
      const expr = exprs.length == 1 ? exprs[0] : new Alt(exprs);
      if (curr_name === null)
        throw new Error(`PATTERN section with no name`);
      const prev = patterns.get(curr_name);
      if (prev === undefined)
        throw new Error(`Undefined pattern ${curr_name}`);
      if (prev instanceof Seq && prev.parts.length == 0)
        patterns.set(curr_name, expr);
      else {
        if (prev instanceof Alt)
          patterns.set(curr_name, new Alt(prev.alts.concat([expr])));
        else
          patterns.set(curr_name, new Alt([prev, expr]));
      }
      continue;
    }
    if (mode === "LEXICON") {
      const [base, tags] = _split_tags(line);
      if (curr_name === null)
        throw new Error(`LEXICON section with no name`);
      const lex = lexicons.get(curr_name);
      if (lex === undefined)
        throw new Error(`Undefined lexicon ${curr_name}`);

      const merged = new Set(curr_block_default_tags);
      // FIXME: Could probably merge these two loops
      for (const t of tags) {
        if (!t.startsWith("-"))
          merged.add(t)
      }
      for (const t of tags) {
        if (t.startsWith("-"))
          merged.delete(t.substring(1))
      }
      let cols: string[] = base ? _split_escaped_fields(base) : [];
      // Lexicon-side tags: tags can appear attached to individual columns like "a[tag]  b".
      // These tags should NOT be part of the symbol string; they only constrain combinations.
      if (cols.length) {
        const new_cols: string[] = [];
        for (const c of cols) {
          const [c_base, c_tags] = _split_tags(c);
          new_cols.push(c_base);
          for (const t of c_tags) {
            if (!t.startsWith("-"))
              merged.add(t)
          }
          for (const t of c_tags) {
            if (t.startsWith("-"))
              merged.delete(t.substring(1))
          }
        }
        cols = new_cols;
      }
      if (lex.arity != 1 && cols.length && cols.length != lex.arity) {
        throw new Error(
          `Lexicon ${lex.name} expects ${lex.arity} columns, got ${cols.length} in ${line}`
        );
      }
      if (lex.arity == 1 && cols.length)
        cols = [cols.join(" ")];
      lex.entries.push({cols, tags: merged})
      continue;
    }
    throw new Error(`Line outside a section (mode ${mode}): ${line}`);
  }

  return {patterns, top_patterns, lexicons, aliases};
}

/* ----------------------------------------
 * Lexicon compilation
 * ----------------------------------------
 */

function _compile_lexicon_entry_variant(
  lex: LexiconDef,
  entry: LexEntry,
  col: number | null,
  side: string,
  strict_quoted: boolean = false
): FST {
  let content: string;
  if (lex.arity === 1) {
    content = entry.cols.length > 0 ? entry.cols[0] : "";
  } else {
    if (col === null) {
      content = entry.cols.join("");
    } else {
      if (!(1 <= col && col <= lex.arity)) {
        throw new Error(`Column ${col} out of range for ${lex.name}(${lex.arity})`);
      }
      content = entry.cols[col - 1];
    }
  }
  content = content.trim();

  if (content.startsWith("/") && content.endsWith("/")) {
    let regex = content.substring(1, content.length - 1);
    // Rewrite lexd multichar tokens (<...>, {...}) into PyFoma-quoted multichar symbols,
    // and fix precedence around a top-level ':' (cross-product binds tighter than concat).
    regex = _quote_multichar_for_pyfoma_regex(regex);
    regex = _wrap_top_level_colon_operands(regex);
    return FST.re(regex);
  }

  let lexside: string, surfside: string;
  if (content.includes(":")) {
    [lexside, surfside] = content.split(":", 2);
  } else {
    lexside = surfside = content;
  }
  lexside = lexside.trim();
  surfside = surfside.trim();

  let labels: Label[];
  if (side === "both") {
    let L = _tokenize_symbols(lexside, strict_quoted);
    let R = _tokenize_symbols(surfside, strict_quoted);
    const n = Math.max(L.length, R.length);
    L = L.concat(Array(n - L.length).fill(""));
    R = R.concat(Array(n - R.length).fill(""));
    labels = L.map((a, i) => _normalize_label([a, R[i]]));
  } else if (side === "out") {
    const use = surfside !== "" ? surfside : lexside;
    labels = _tokenize_symbols(use, strict_quoted).map(s => _normalize_label(["", s]));
  } else if (side === "in") {
    labels = _tokenize_symbols(lexside, strict_quoted).map(l => _normalize_label([l, ""]));
  } else {
    throw new Error(side);
  }

  let fst = from_tuples([labels]);
  try {
    return fst.determinize().minimizeAsDFA();
  } catch (e) {
    return fst.determinize();
  }
}

function _compile_lexicon_variant(
  lex: LexiconDef,
  col: number | [number, number] | null,
  side: string,
  selector: TagSelector,
  strict_quoted: boolean = false
): FST {
  const paths: Label[][] = [];
  let regex_union: FST | null = null;

  // Support lexd syntax X(i):X(j) where a single lexicon entry is used,
  // but its (i)th column is placed on the input side and its (j)th column on the output side.
  // We encode this by compiling a temporary 1-column entry of the form "L:R" and compiling it normally.
  if (col !== null && typeof col !== "number") {
    const [col_in, col_out] = col;
    if (!(1 <= col_in && col_in <= lex.arity) || !(1 <= col_out && col_out <= lex.arity)) {
      throw new Error(`Column pair ${col} out of range for ${lex.name}(${lex.arity})`);
    }

    const tmp_lex: LexiconDef = { name: lex.name, arity: 1, entries: [] };
    const variants: FST[] = [];

    for (const e of lex.entries) {
      if (!selector.matches(e.tags)) continue;
      const left = col_in - 1 < e.cols.length ? e.cols[col_in - 1] : "";
      const right = col_out - 1 < e.cols.length ? e.cols[col_out - 1] : "";
      const tmp_entry: LexEntry = { cols: [`${left}:${right}`], tags: new Set(e.tags) };
      variants.push(
        _compile_lexicon_entry_variant(tmp_lex, tmp_entry, 1, "both", strict_quoted)
      );
    }

    const f = variants.length > 0 ? union_all(variants) : new FST();
    return f.determinize().minimizeAsDFA();
  }

  for (const e of lex.entries) {
    if (!selector.matches(e.tags)) continue;

    let content: string;
    if (lex.arity === 1) {
      content = e.cols.length > 0 ? e.cols[0] : "";
    } else {
      if (col === null) {
        content = e.cols.join("");
      } else {
        if (!(1 <= (col as number) && (col as number) <= lex.arity)) {
          throw new Error(`Column ${col} out of range for ${lex.name}(${lex.arity})`);
        }
        content = e.cols[(col as number) - 1];
      }
    }
    content = content.trim();

    if (content.startsWith("/") && content.endsWith("/")) {
      const rf = _compile_lexicon_entry_variant(lex, e, col as number | null, side, strict_quoted);
      regex_union = regex_union === null ? rf : regex_union.union(rf);
      continue;
    }

    let lexside: string, surfside: string;
    if (content.includes(":")) {
      [lexside, surfside] = content.split(":", 2);
    } else {
      lexside = surfside = content;
    }

    lexside = lexside.trim();
    surfside = surfside.trim();

    let labels: Label[];
    if (side === "both") {
      let L = _tokenize_symbols(lexside, strict_quoted);
      let R = _tokenize_symbols(surfside, strict_quoted);
      const n = Math.max(L.length, R.length);
      L = L.concat(Array(n - L.length).fill(""));
      R = R.concat(Array(n - R.length).fill(""));
      labels = L.map((a, i) => _normalize_label([a, R[i]]));
    } else if (side === "out") {
      const use = surfside !== "" ? surfside : lexside;
      labels = _tokenize_symbols(use, strict_quoted).map(s => _normalize_label(["", s]));
    } else if (side === "in") {
      labels = _tokenize_symbols(lexside, strict_quoted).map(l => _normalize_label([l, ""]));
    } else {
      throw new Error(side);
    }

    paths.push(labels);
  }

  let outfst: FST | null = null;
  if (paths.length > 0) {
    outfst = from_tuples(paths);
  }
  if (regex_union !== null) {
    outfst = outfst === null ? regex_union : outfst.union(regex_union);
  }

  if (outfst === null) {
    return empty_fst();
  }

  try {
    return outfst.determinize().minimizeAsDFA();
  } catch (e) {
    return outfst.determinize();
  }
}

/**
 * ----------------------------------------
 * Compilation
 * ----------------------------------------
 */

/**
 * Compile a lexd grammar and return a pyfoma FST.
 *
 * strict_quoted controls single-quote behavior in plain lexicon entries:
 *   - False (default): unmatched single quote is treated as a literal symbol
 *   - True: unmatched single quote raises ValueError
 */
export function compile(grammar: string, strict_quoted: boolean = false): FST {
  return compile_lexd(parse_lexd(grammar), strict_quoted);
}

export function compile_lexd(parsed: ParsedLexd, strict_quoted: boolean = false): FST {
  function resolve_name(name: string): string {
    return parsed.aliases.get(name) ?? name;
  }

  let anon_counter = 0;
  const anon_map = new Map<string, string>();
  const lex_cache = new Map<string, FST>();
  const pat_cache = new Map<string, FST>();

  function compile_tok(tok: TokRef): FST {
    let name: string | undefined;
    if (tok.kind === "anonlex") {
      const raw = tok.name.split(":", 2)[1];
      name = anon_map.get(tok.name);
      if (name === undefined) {
        anon_counter++;
        const anon_name = `__anonlex_${anon_counter}`;
        const [base, tags] = _split_tags(raw);
        parsed.lexicons.set(anon_name, {
          name: anon_name,
          arity: 1,
          entries: [{ cols: [base], tags: new Set(tags) }]
        });
        anon_map.set(tok.name, anon_name);
        name = anon_name;
      }
    }
    else name = tok.name;

    // Cross-lexicon paired reference: x(i):y(j)
    // Handled in compile_seq_aligned so we can bind the paired row index across multiple occurrences.
    if (tok.kind === "pair")
      throw new Error("Internal: pair tokens must be compiled in compile_seq_aligned()");

    if (parsed.patterns.has(name) && !(parsed.lexicons.has(resolve_name(name)))) {
      const key = JSON.stringify([name, ...tok.selector.toArray()]);
      const pattern = pat_cache.get(key);
      if (pattern !== undefined)
        return pattern;
      let expr = parsed.patterns.get(name);
      if (expr === undefined)
        throw new Error(`Undefined pattern ${name}`);
      expr = _apply_selector_distribution(expr, tok.selector);
      const f = compile_expr(expr, new Map(), null);
      pat_cache.set(key, f);
      return f;
    }

    const base = resolve_name(name);
    const base_lex = parsed.lexicons.get(base);
    if (base_lex === undefined) {
      // Internal: some anon-pattern expansions use a __POSTSEL__: prefix for temporary atoms.
      // Treat these as anonymous literal patterns (identity transducer).
      // See test-anonpat-modifier for the type of pattern where this is needed
      if (name.startsWith("__POSTSEL__:")) {
        const lit = name.substring("__POSTSEL__:".length);
        const syms = _tokenize_symbols(lit, strict_quoted);
        const labels: Label[] = syms.map(s => [s, s]);
        let fst = from_tuples([labels]);
        return fst.determinize().minimizeAsDFA();
      }
      throw new Error(`Unknown lexicon/pattern: ${name}`);
    }

    const cache_key = JSON.stringify([base, tok.col, tok.side, ...tok.selector.toArray()]);
    const lex = lex_cache.get(cache_key);
    if (lex !== undefined)
      return lex;

    const f = _compile_lexicon_variant(
      base_lex, tok.col ?? null, tok.side, tok.selector, strict_quoted
    );
    lex_cache.set(cache_key, f);
    return f;
  }

  function should_bind(lexdef: LexiconDef, tok: TokRef, force: Set<string>): boolean {
    // Bind if:
    //  - explicitly column-referenced (tok.col set), OR
    //  - this lexicon repeats in the current sequence scope (__FORCE_BIND__), OR
    //  - one-sided binding is in effect (tok.side != 'both')
    if (force.has(tok.name)) return true;
    if (tok.col !== null) return true;
    if (tok.side !== "both") return true;
    // multi-column lexicons are bound by construction
    return lexdef.arity > 1;
  }

  function compile_seq_aligned(parts: PatExpr[], env: Map<string, number>, force: Set<string> | null): FST {
    // Binding: if a lexicon name appears multiple times in the *current* sequence scope,
    // its choice must be coherent across those occurrences.
    if (force === null) {
      const counts = new Map<string, number>();
      for (const e of parts) {
        if (e instanceof Ref) {
          const t = e.token;
          let key: string | null = null;
          if (t.kind === "lex")
            key = t.name;
          else if (t.kind === "pair" && t.left && t.right)
            // This is never checked, but use the same key anyway
            key = "__PAIR__:" + t.left + ":" + t.right;
          if (key !== null) {
            const count = counts.get(key) ?? 0;
            counts.set(key, count + 1);
          }
        }
      }
      force = new Set<string>;
      for (const [k, c] of counts) {
        if (c > 1)
          force.add(k);
      }
    }

    if (parts.length === 0)
      return epsilon_fst();

    const [head, ...tail] = parts;

    if (head instanceof Ref) {
      const tok = head.token;
      if (tok.kind === "lex" || tok.kind === "anonlex") {
        // FIXME: Are we sure it can't ever be a pair here?
        if (tok.col instanceof Array)
          throw new Error(`Found pair of columns where there should not be: ${tok}`);
        const base = resolve_name(tok.name);
        const lexdef = parsed.lexicons.get(base);
        if (lexdef !== undefined) {
          if (should_bind(lexdef, tok, force)) {
            const idx = env.get(base);
            if (idx !== undefined) {
              const entry = lexdef.entries[idx];
              if (!tok.selector.matches(entry.tags)) {
                return empty_fst();
              }
              const fst_head = _compile_lexicon_entry_variant(
                lexdef, entry, tok.col, tok.side, strict_quoted
              );
              return fst_head.concatenate(compile_seq_aligned(tail, env, force));
            }

            let out: FST | null = null;
            for (let idx = 0; idx < lexdef.entries.length; idx++) {
              const entry = lexdef.entries[idx];
              if (!tok.selector.matches(entry.tags)) {
                continue;
              }
              const fst_head = _compile_lexicon_entry_variant(
                lexdef, entry, tok.col, tok.side, strict_quoted
              );
              const env2 = new Map(env);
              env2.set(base, idx);
              const path = fst_head.concatenate(compile_seq_aligned(tail, env2, force));
              out = out ? out.union(path) : path;
            }
            return out || empty_fst();
          }
        }
      }
    }

    // Special: paired token x(i):y(j) binds a row index across occurrences.
    if (head instanceof Ref && head.token.kind === "pair") {
      const tok = head.token;
      if (!(tok.col instanceof Array))
        throw new Error(`Found single columns where there should be a pair: ${tok}`);
      if (!tok.left || !tok.right) {
        throw new Error(`Malformed pair token: ${JSON.stringify(tok)}`);
      }
      const lx = resolve_name(tok.left);
      const ly = resolve_name(tok.right);
      const lex_x = parsed.lexicons.get(lx);
      const lex_y = parsed.lexicons.get(ly);
      if (lex_x === undefined || lex_y === undefined) {
        throw new Error(`Unknown lexicon in pair: ${tok.left}:${tok.right}`);
      }

      const [ci, co] = tok.col;
      if (typeof ci !== 'number' || typeof co !== 'number') {
        throw new Error(`Bad pair columns in ${JSON.stringify(tok)}`);
      }
      if (ci < 1 || ci > lex_x.arity || co < 1 || co > lex_y.arity) {
        throw new Error(
          `Pair columns out of range in ${JSON.stringify(tok)}: ${tok.left}(${lex_x.arity}) ${tok.right}(${lex_y.arity})`
        );
      }

      const pair_key = "__PAIR__:" + tok.left + ":" + tok.right;
      // If already bound, compile only that paired row.
      const k = env.get(pair_key);
      if (k !== undefined) {
        const ex = lex_x.entries[k];
        const ey = lex_y.entries[k];
        const tag_union = new Set([...ex.tags, ...ey.tags]);
        if (tok.selector && !tok.selector.matches(tag_union))
          return empty_fst();
        const left_str = ex.cols[ci - 1] || "";
        const right_str = ey.cols[co - 1] || "";
        const left_syms = _tokenize_symbols(left_str, strict_quoted);
        const right_syms = _tokenize_symbols(right_str, strict_quoted);
        const L = Math.max(left_syms.length, right_syms.length);
        const labels: Label[] = [];
        for (let i = 0; i < L; i++) {
          const a = i < left_syms.length ? left_syms[i] : "";
          const b = i < right_syms.length ? right_syms[i] : "";
          labels.push([a, b]);
        }
        const fst_head = from_tuples([labels]);
        return fst_head.concatenate(compile_seq_aligned(tail, env, force));
      }

      // Otherwise, branch over paired rows (zip semantics).
      let out: FST | null = null;
      const max_k = Math.min(lex_x.entries.length, lex_y.entries.length);
      for (let k = 0; k < max_k; k++) {
        const ex = lex_x.entries[k];
        const ey = lex_y.entries[k];
        const tag_union = new Set([...ex.tags, ...ey.tags]);
        if (tok.selector && !tok.selector.matches(tag_union)) {
          continue;
        }
        const left_str = ex.cols[ci - 1] || "";
        const right_str = ey.cols[co - 1] || "";
        const left_syms = _tokenize_symbols(left_str, strict_quoted);
        const right_syms = _tokenize_symbols(right_str, strict_quoted);
        const L = Math.max(left_syms.length, right_syms.length);
        const labels: Label[] = [];
        for (let i = 0; i < L; i++) {
          const a = i < left_syms.length ? left_syms[i] : "";
          const b = i < right_syms.length ? right_syms[i] : "";
          labels.push([a, b]);
        }
        const fst_head = from_tuples([labels]);
        const env2 = new Map(env);
        env2.set(pair_key, k);
        const path = fst_head.concatenate(compile_seq_aligned(tail, env2, force));
        out = out ? out.union(path) : path;
      }

      return out || empty_fst();
    }

    const fst_head = compile_expr(head, env, force);
    return fst_head.concatenate(compile_seq_aligned(tail, env, force));
  }

  function compile_expr(expr: PatExpr, env: Map<string, number>, force: Set<string> | null): FST {
    if (expr instanceof Ref)
      return compile_tok(expr.token);

    if (expr instanceof Seq)
      return compile_seq_aligned(expr.parts, env, force);

    if (expr instanceof Alt) {
      let out: FST | null = null;
      for (const a of expr.alts) {
        const af = compile_expr(a, new Map(env), force ? new Set(force) : null);
        out = out ? out.union(af) : af;
      }
      return out || empty_fst();
    }

    if (expr instanceof Quant) {
      const base = compile_expr(expr.expr, new Map(), null);
      if (expr.q === "?")
        return epsilon_fst().union(base);
      if (expr.q === "*")
        return base.kleeneClosure("star");
      if (expr.q === "+")
        return base.kleeneClosure("plus");
      throw new Error(`Unknown quantifier: ${expr.q}`);
    }

    if (expr instanceof Tagged) {
      const distributed = _apply_selector_distribution(expr.expr, expr.selector);
      return compile_expr(distributed, env, force);
    }

    throw new Error(`Unhandled node: ${JSON.stringify(expr)}`);
  }

  let outfst: FST | null = null;
  for (const expr of parsed.top_patterns) {
    const f = compile_expr(expr, new Map(), null);
    outfst = outfst ? outfst.union(f) : f;
  }

  if (!outfst) {
    outfst = empty_fst();
  }

  // FIXME: Weighted determinization doesn't seem to work correctly in
  // pyfoma-js but lexd is unweighted anyway!
  /*try {
    outfst = outfst.determinize().minimizeAsDFA();
  } catch (e) {
    outfst = outfst.determinize();
    }*/
  // So this does unweighted determinization and minimization
  outfst.minimize();
  return outfst;
}
