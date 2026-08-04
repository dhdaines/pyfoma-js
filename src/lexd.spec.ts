// -*- js-indent-level: 2 -*-
import { describe, expect, test } from 'vitest';
import { compile, compile_lexd, parse_lexd  } from "./lexd.js";
// import type { InspectOptions } from 'util';

describe("Test lexd compiler", () => {
    test("parse a basic grammar", () => {
        const grammar = `
PATTERNS
Word

LEXICON Word
hello
world
`;
        const parsed = parse_lexd(grammar);
        expect(parsed).toBeTruthy();
        expect(parsed.top_patterns).toHaveLength(1);
        expect(parsed.lexicons.has("Word")).toBeTruthy();
        expect(parsed.lexicons.get("Word")!.entries).toHaveLength(2);
    });

    test("basic example from documentation", () => {
    const grammar = `
PATTERNS
pattern1

PATTERN pattern1
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
        const myfst = compile(grammar);
        expect(Array.from(myfst.generate("cat<pl>"))).toEqual(["cats"]);
        expect(Array.from(myfst.analyze("ex-dogs"))).toEqual(["ex-dog<pl>"]);
        expect(Array.from(myfst.analyze("cats"))).toEqual(["cat<pl>"]);
    });
});

/* lexd test suite from test_lexd_suite.py:

Regression test suite for Lexd implementation:
- 7 hand-written tests from lexd usage documentation 
- +36 feature tests embedded from the reference C++ test bundle (self-contained here)

Usage documentation tests from:
https://github.com/apertium/lexd/blob/main/Usage.md

Feature tests from:
https://github.com/apertium/lexd/tree/main/tests/feature
*/   

type Test = {
  name: string;
  grammar: string;
};

type PairTest = Test & {
  // One per line, either "A:B" or "A/B" (we infer which side is the input by probing fst.apply).
  expected_lines: string[];
  forbidden_alphabet_symbols?: Set<string>;
};

type AcceptRejectTest = Test & {
  cases: { [key: string]: boolean };
  require_identity_outputs: boolean;
};

/**
 * Compare the transducer language serialized in foma-like 'string' form.

    The gold files in the C++ suite are lists of strings where each path is serialized by concatenating
    per-arc labels:
      - identity pair (a,a) is printed as 'a'
      - (a,ε) is printed as 'a:'
      - (ε,b) is printed as ':b'
      - (a,b) is printed as 'a:b'
    with multichar symbols kept intact (e.g. '<sent>').
*/
type GoldStringsTest = Test & {
  gold_strings: string[];
  max_depth?: number;
};

const HAND_TESTS: (PairTest | AcceptRejectTest)[] = [
  {
    name: "Test 1",
    grammar: `PATTERNS
VerbRoot VerbInfl

LEXICON VerbRoot
sing
walk
dance

LEXICON VerbInfl
<v><pres>:
<v><pres><p3><sg>:s
`,
    expected_lines: [
      "sing<v><pres>:sing",
      "sing<v><pres><p3><sg>:sings",
      "walk<v><pres>:walk",
      "walk<v><pres><p3><sg>:walks",
      "dance<v><pres>:dance",
      "dance<v><pres><p3><sg>:dances",
    ],
  },
  {
    name: "Test 2",
    grammar: `PATTERNS
:VerbInfl VerbRoot VerbInfl:
:VerbInfl :VerbRoot VerbRoot VerbInfl: Redup

LEXICON VerbRoot
bloop
vroom

LEXICON VerbInfl
<v><pres>:en

LEXICON Redup
<redup>:
`,
    expected_lines: [
      "enbloop/bloop<v><pres>",
      "envroom/vroom<v><pres>",
      "enbloopbloop/bloop<v><pres><redup>",
      "envroomvroom/vroom<v><pres><redup>",
    ],
  },
  {
    name: "Test 3",
    grammar: `PATTERNS
C(1) :V(1) C(2) :V(2) C(3) V(2):

LEXICON C(3)
sh m r
y sh v

LEXICON V(2)
:a <v><p3><sg>:a
:o <v><pprs>:e
`,
    expected_lines: [
      "shamar/shmr<v><p3><sg>",
      "shomer/shmr<v><pprs>",
      "yashav/yshv<v><p3><sg>",
      "yoshev/yshv<v><pprs>",
    ],
  },
  {
    name: "Test 4",
    grammar: `PATTERNS
NounStem NounInfl
NounStem NounInflComp Comp NounStem2 NounInfl

LEXICON Comp
<comp>+:

LEXICON NounStem
shoop
blarg

ALIAS NounStem NounStem2

LEXICON NounInfl
<n><sg>:
<n><pl>:ah

LEXICON NounInflComp
<n>:a
`,
    expected_lines: [
      "shoop/shoop<n><sg>",
      "shoopah/shoop<n><pl>",
      "shoopashoop/shoop<n><comp>+shoop<n><sg>",
      "shoopashoopah/shoop<n><comp>+shoop<n><pl>",
      "shoopablarg/shoop<n><comp>+blarg<n><sg>",
      "shoopablargah/shoop<n><comp>+blarg<n><pl>",
      "blarg/blarg<n><sg>",
      "blargah/blarg<n><pl>",
      "blargashoop/blarg<n><comp>+shoop<n><sg>",
      "blargashoopah/blarg<n><comp>+shoop<n><pl>",
      "blargablarg/blarg<n><comp>+blarg<n><sg>",
      "blargablargah/blarg<n><comp>+blarg<n><pl>",
    ],
  },
  {
    name: "Test 5",
    grammar: `PATTERNS
NounStem [<n>:] NounNumber

LEXICON NounStem
sock
ninja

LEXICON NounNumber
<sg>:
<pl>:s
`,
    expected_lines: [
      "ninja/ninja<n><sg>",
      "ninjas/ninja<n><pl>",
      "sock/sock<n><sg>",
      "socks/sock<n><pl>",
    ],
  },
  {
    name: "Test 6",
    grammar: `PATTERNS
(NounStem CaseEnding)[^[Decl1,Decl2],^[N,M,F]]

LEXICON NounStem
mensa:mens[Decl1,F]     # table
poeta:poet[Decl1,M]     # poet
dominus:domin[Decl2,M]  # master
bellum:bell[Decl2,N]    # war

LEXICON CaseEnding[Decl2]
<nom>:>us[M]
<nom>:>um[N]
<acc>:>um    # M or N

LEXICON CaseEnding[Decl1]
<nom>:>a     # any gender
<acc>:>am    # any gender
`,
    expected_lines: [
      "poeta<nom>/poet>a",
      "poeta<acc>/poet>am",
      "mensa<nom>/mens>a",
      "mensa<acc>/mens>am",
      "bellum<nom>/bell>um",
      "bellum<acc>/bell>um",
      "dominus<nom>/domin>us",
      "dominus<acc>/domin>um",
    ],
    forbidden_alphabet_symbols: new Set(["Decl1", "Decl2", "M", "F", "N", "[", "]"]),
  },
  {
    name: "Test 7",
    grammar: `PATTERNS
SomeLexicon

LEXICON SomeLexicon
/x(y|zz)?[n-p]/
`,
    cases: {
      "xn": true,
      "xo": true,
      "xp": true,
      "xyn": true,
      "xyo": true,
      "xyp": true,
      "xzzn": true,
      "xzzo": true,
      "xzzp": true,
    },
    require_identity_outputs: true,
  },
];


/* -------------------------
 * Helpers
 * -------------------------
 */

function _split_pair_line(line: string): [string, string] {
  if (line.includes("/")) {
    const [a, b] = line.split("/", 2);
    return [a, b];
  }
  if (line.includes(":")) {
    const [a, b] = line.split(":", 2);
    return [a, b];
  }
  throw new Error(`Expected pair line with '/' or ':': ${line}`);
}

/**
 * Serialize a path to the C++ gold format.

  - Pure identity(inp == out) -> inp
  - Input - only(out == '') -> inp + ':'
  - Output - only(inp == '') -> ':' + out
  - General -> inp + ':' + out
*/
function _serialize_path(inp: string, out: string): string {
  if (inp === out)
    return inp;
  if (out === "")
    return inp + ":";
  if (inp === "")
    return ":" + out;
  return inp + ":" + out;
}

/**
 * Enumerate strings from fst in the same format as the C++ gold suite.

    We accumulate the full input and output strings along each path, then serialize with minimal colons:
    - identity: 'abc'
    - input - only: 'abc:'
    - output - only: ':abc'
    - general: 'in:out'
    This matches the lexd C++ test gold files(e.g. 'xX:Yy', not 'x:YX:y').
*/
function _enumerate_gold_strings(fst: any, maxDepth: number, maxStrings: number): Set<string> {
  const initial = fst.initialstate;
  const finals = new Set(fst.finalstates);

  const out = new Set<string>();

  // stack items: (state, in_str, out_str, depth)
  type StackItem = [any, string, string, number];
  const stack: StackItem[] = [[initial, "", "", 0]];

  while (stack.length > 0) {
    const [st, ins, outs, d] = stack.pop()!;

    if (finals.has(st)) {
      out.add(_serialize_path(ins, outs));
      if (out.size >= maxStrings) {
        break;
      }
    }

    if (d >= maxDepth) {
      continue;
    }

    for (const { label, set } of st.transitions.values()) {
      for (const tr of set) {
        let in2 = ins;
        let out2 = outs;
        if (label.length === 1) {
          const a = label[0];
          in2 += a;
          out2 += a;
        } else if (label.length === 2) {
          const [a, b] = label;
          if (a !== "") in2 += a;
          if (b !== "") out2 += b;
        } else {
          throw new Error(`Unexpected label tuple length: ${JSON.stringify(label)}`);
        }
        stack.push([tr.targetstate, in2, out2, d + 1]);
      }
    }

    if (out.size >= maxStrings) {
      break;
    }
  }

  return out;
}

function _infer_max_depth_from_gold(gold: string[]): number {
  // crude but safe: allow some headroom
  const maxLen = Math.max(0, ...gold.map(x => x.length));
  return Math.max(10, maxLen + 10);
}


const CPP_TESTS: GoldStringsTest[] = [
  {
    name: "cpp:test-alt",
    grammar: `PATTERNS
pattern1

PATTERN pattern1
A | B
C:|:D

LEXICON A
a

LEXICON B
b

LEXICON C
c

LEXICON D
d
`,
    gold_strings: [
      ":d",
      "a",
      "b",
      "c:"
    ],
  },
  {
    name: "cpp:test-anonlex",
    grammar: `PATTERNS
[ a ]
`,
    gold_strings: [
      "a"
    ],
  },
  {
    name: "cpp:test-anonlex-modifier",
    grammar: `PATTERNS
[a] [b]? [c]
`,
    gold_strings: [
      "abc",
      "ac"
    ],
  },
  {
    name: "cpp:test-anonpat",
    grammar: `PATTERNS
( a b ) | c

LEXICON a
a

LEXICON b
b

LEXICON c
c
`,
    gold_strings: [
      "ab",
      "c"
    ],
  },
  {
    name: "cpp:test-anonpat-filter",
    grammar: `PATTERNS
(Adj Noun)[nofruit,-nocolor]
(Adj Noun)[-nofruit,nocolor]

LEXICON Adj
bright[nofruit]
green
tasty[nocolor]
impetuous[nofruit,nocolor]

LEXICON Noun
apple[nocolor]
orange
green[nofruit]
cat[nofruit,nocolor]
`,
    gold_strings: [
      "brightgreen",
      "brightorange",
      "greenapple",
      "greengreen",
      "tastyapple",
      "tastyorange"
    ],
  },
  {
    name: "cpp:test-anonpat-filter-ops",
    grammar: `PATTERNS
(A)[^[a,b]]

LEXICON A
apple[a]
banana[b]
orange[a,b]
`,
    gold_strings: [
      "apple",
      "banana"
    ],
  },
  {
    name: "cpp:test-anonpat-modifier",
    grammar: `PATTERNS
[a] ([b])? [c]
`,
    gold_strings: [
      "abc",
      "ac"
    ],
  },
  {
    name: "cpp:test-anonpat-nospaces",
    grammar: `PATTERNS
(A)

LEXICON A
a
`,
    gold_strings: [
      "a"
    ],
  },
  {
    name: "cpp:test-anonpat-ops",
    grammar: `PATTERNS
A|(C?)

LEXICON A
a

LEXICON C
c
`,
    gold_strings: [
      "",
      "a",
      "c"
    ],
  },
  {
    name: "cpp:test-conflicting-tags",
    grammar: `PATTERNS
Verbs-IV

PATTERN VerbStemBase
V-IV [<v><iv>:>[nonpunct]] V-Aspect-Hab
V-IV [<v><iv>:>[punct]] V-Aspect-Punct   # error reported here

PATTERN VerbStem
VerbStemBase[^[A1,A2]]

PATTERN Verbs-IV
:V-Agent VerbStem[-nonpunct] V-Agent:
:V-Agent VerbStem[stat] V-Agent:

LEXICON V-IV
stem

LEXICON V-Aspect-Hab
<hab>:{a}haʔ[A1]
<hab>:{a}s[A2]

LEXICON V-Aspect-Punct
<punct>:{a}{ʔ}[A1]
<punct>:{a}{ʔ}[A2]

LEXICON V-Agent
<a1sg>:{G}{e}
<a1duexcl>:{y}ag{n}{I}
`,
    gold_strings: [
      "stem<v><iv><punct><a1duexcl>:{y}ag{n}{I}stem>{a}{ʔ}",
      "stem<v><iv><punct><a1sg>:{G}{e}stem>{a}{ʔ}"
    ],
  },
  {
    name: "cpp:test-diacritic",
    grammar: `PATTERNS
X
Y(2)

LEXICON X
\\ַ
:ֶ
:\\ֻ
x\\ַ

LEXICON Y(2)
a ַ
`,
    gold_strings: [
      ":\u05b6",
      ":\u05bb",
      "x\u05b7",
      "\u05b7"
    ],
  },
  {
    name: "cpp:test-disjoint-opt",
    grammar: `PATTERNS
A?(1) B A?(1)

LEXICON A
a
aa

LEXICON B
b
bb
`,
    gold_strings: [
      "aabaa",
      "aabbaa",
      "aba",
      "abba",
      "b",
      "bb"
    ],
  },
  {
    name: "cpp:test-empty",
    grammar: `
`,
    gold_strings: [],
  },
  {
    name: "cpp:test-empty-patterns",
    grammar: `PATTERNS
Case[t]
Case[s] # comment to get the correct answer

LEXICON Obl
<suff>

LEXICON OblCase
<case>[t]

PATTERN Case
Obl OblCase
`,
    gold_strings: [
      "<suff><case>"
    ],
  },
  {
    name: "cpp:test-filter-crosstalk",
    grammar: `PATTERNS
Phrase[nofruit,-nocolor]
Phrase[-nofruit,nocolor]

PATTERN Phrase
Adj Noun

LEXICON Adj
bright[nofruit]

LEXICON Noun
apple[nocolor]
orange[nofruit]
`,
    gold_strings: [
      "brightorange"
    ],
  },
  {
    name: "cpp:test-lexdeftag",
    grammar: `PATTERNS
A[x]
B[x]

LEXICON A[x]
apple
banana[-x]

LEXICON A
orange
pear[x]

LEXICON B[x]:[y]
nope[-x]
yep:yep[-y,x] # left side gets x
`,
    gold_strings: [
      "apple",
      "pear",
      "yep"
    ],
  },
  {
    name: "cpp:test-lexicon-side-tags",
    grammar: `PATTERNS
X(1):X(2)[tag]


LEXICON X(2)
a[tag]	b
`,
    gold_strings: [
      "a:b"
    ],
  },
  {
    name: "cpp:test-lexname-space",
    grammar: `PATTERNS
[a]

LEXICON X
blah

LEXICON Y 
bloop

LEXICON Z(2)
x y

LEXICON W(3) 
a b c
`,
    gold_strings: [
      "a"
    ],
  },
  {
    name: "cpp:test-lexnegtag",
    grammar: `PATTERNS
[a] A[s,-r]
[b] A[-t,s]
[c] A[-s]

LEXICON A
a[t,s]
b[s,r]
c[t,r]
`,
    gold_strings: [
      "aa",
      "bb",
      "cc"
    ],
  },
  {
    name: "cpp:test-lextag",
    grammar: `PATTERNS
[a] A[t]
[b] A[r]
[ab] A[s]

LEXICON A
a[t,s]
b[s,r]
`,
    gold_strings: [
      "aa",
      "aba",
      "abb",
      "bb"
    ],
  },
  {
    name: "cpp:test-nontree",
    grammar: `PATTERNS
parentpat
parentpat2

PATTERN parentpat
childpat

PATTERN parentpat2
childpat

PATTERN childpat
child

LEXICON child
x
`,
    gold_strings: [
      "x"
    ],
  },
  {
    name: "cpp:test-oneside",
    grammar: `PATTERNS
A:
:A

LEXICON A
a1:a2
`,
    gold_strings: [
      ":a2",
      "a1:"
    ],
  },
  {
    name: "cpp:test-opt",
    grammar: `PATTERNS
pattern1

PATTERN pattern1
A? B?
C:? :D?

LEXICON A
a

LEXICON B
b

LEXICON C
c

LEXICON D
d
`,
    gold_strings: [
      "",
      ":d",
      "a",
      "ab",
      "b",
      "c:",
      "c:d"
    ],
  },
  {
    name: "cpp:test-or-filter",
    grammar: `PATTERNS
A[|[a,b]]

LEXICON A
apple[a]
banana[b]
orange
delaware[notafruit]
`,
    gold_strings: [
      "apple",
      "banana"
    ],
  },
  {
    name: "cpp:test-pairs",
    grammar: `PATTERNS
pattern

PATTERN pattern
x(1):y(2) x(2):y(1)

LEXICON x(2)
x X

LEXICON y(2)
y Y
`,
    gold_strings: [
      "xX:Yy"
    ],
  },
  {
    name: "cpp:test-pattag",
    grammar: `PATTERNS
[t] A[t]
[nott] A[-t]

PATTERN A
B
C

LEXICON B
a[t]

LEXICON C
b[s]
`,
    gold_strings: [
      "nottb",
      "ta"
    ],
  },
  {
    name: "cpp:test-pattag-coherent",
    grammar: `PATTERNS

B(1)[x] A(1)[x] B(1)
B(1)[-x] A(1)[-x] B(1)

LEXICON A

a-no-x
a-x[x]

LEXICON B

b-no-x
b-x[x]
`,
    gold_strings: [
      "b-no-xa-no-xb-no-x",
      "b-xa-xb-x"
    ],
  },
  {
    name: "cpp:test-pattag-details",
    grammar: `PATTERNS
X[t,-s]

PATTERN X
A B
C

LEXICON A
a
at[t]
as[s]
ast[s,t]

LEXICON B
b
bt[t]
bs[s]
bst[t,s]

LEXICON C
ct[t]
cs[s]
cst[t,s]
`,
    gold_strings: [
      "abt",
      "atb",
      "atbt",
      "ct"
    ],
  },
  {
    name: "cpp:test-pattern-independence",
    grammar: `PATTERNS
X A
B B

PATTERN X
A A

LEXICON A
a1
a2

LEXICON B
b1
b2
`,
    gold_strings: [
      "a1a1a1",
      "a1a1a2",
      "a2a2a1",
      "a2a2a2",
      "b1b1",
      "b2b2"
    ],
  },
  {
    name: "cpp:test-regex",
    grammar: `PATTERNS
[/a/]
RE
COLRE(1) COLRE(2)
TWOSIDED

LEXICON RE
/<b>/
/c[d-f]g/
/h(i)?/
/j|k/
/(l(m)?)?/

LEXICON COLRE(2)
/n[op]/ q
r /[s-u]v/

LEXICON TWOSIDED
/w:x[yz]/
`,
    gold_strings: [
      "",
      "<b>",
      "a",
      "cdg",
      "ceg",
      "cfg",
      "h",
      "hi",
      "j",
      "k",
      "l",
      "lm",
      "noq",
      "npq",
      "rsv",
      "rtv",
      "ruv",
      "w:xy",
      "w:xz"
    ],
  },
  {
    name: "cpp:test-revsieve",
    grammar: `PATTERNS
b(1) < b(2) < b(3)

LEXICON b(3)
b1 b2 b3
`,
    gold_strings: [
      "b1b2b3",
      "b2b3",
      "b3"
    ],
  },
  {
    name: "cpp:test-sieve",
    grammar: `PATTERNS
pattern

LEXICON f(3)
f1 f2 f3
g1 g2 g3

LEXICON b(3)
b1 b2 b3
c1 c2 c3

LEXICON m
m

PATTERN pattern
f(1) > f(2) > f(3)
b(1) < b(2) < b(3)
b(1) < m > f(1)
`,
    gold_strings: [
      "b1b2b3",
      "b1m",
      "b1mf1",
      "b1mg1",
      "b2b3",
      "b3",
      "c1c2c3",
      "c1m",
      "c1mf1",
      "c1mg1",
      "c2c3",
      "c3",
      "f1",
      "f1f2",
      "f1f2f3",
      "g1",
      "g1g2",
      "g1g2g3",
      "m",
      "mf1",
      "mg1"
    ],
  },
  {
    name: "cpp:test-sieveopt",
    grammar: `PATTERNS
A > B|C

LEXICON A
a

LEXICON B
b

LEXICON C
c
`,
    gold_strings: [
      "a",
      "ab",
      "ac"
    ],
  },
  {
    name: "cpp:test-slots-and-operators-nospace",
    grammar: `PATTERNS
X(1)|Y(1) [z]

LEXICON X(2)
x1 x2

LEXICON Y(2)
y1 y2
`,
    gold_strings: [
      "x1z",
      "y1z"
    ],
  },
  {
    name: "cpp:test-xor-filter",
    grammar: `PATTERNS
A[^[a,b]]

LEXICON A
apple[a]
banana[b]
orange[a,b]
`,
    gold_strings: [
      "apple",
      "banana"
    ],
  },
  {
    name: "cpp:test-xor-multi",
    grammar: `PATTERNS
Phrase[^[nofruit,nocolor]]

PATTERN Phrase
Adj Noun

LEXICON Adj
bright[nofruit]
green
tasty[nocolor]
impetuous[nofruit,nocolor]

LEXICON Noun
apple[nocolor]
orange
green[nofruit]
cat[nofruit,nocolor]
`,
    gold_strings: [
      "brightgreen",
      "brightorange",
      "greenapple",
      "greengreen",
      "tastyapple",
      "tastyorange"
    ],
  },
];

/* -------------------------
 * Runners
 * -------------------------
 */

function run_pair_test(test: PairTest): boolean {
  const parsed = parse_lexd(test.grammar);
  // const opts: InspectOptions = {showHidden: true, depth: 10};
  // console.dir(parsed, opts);
  const fst = compile_lexd(parsed);
  /*
  console.log(fst.toATT());
  for (const [_, pairs] of fst.words()) {
    console.log(pairs);
    }
  */

  if (test.forbidden_alphabet_symbols) {
    const bad = new Set([...test.forbidden_alphabet_symbols].filter(x => fst.alphabet.has(x)));
    if (bad.size > 0) {
      throw new Error(`${test.name}: forbidden symbols in alphabet: ${Array.from(bad).sort()}`);
    }
  }

  const expectedMap: { [key: string]: Set<string> } = {};
  for (const line of test.expected_lines) {
    const [left, right] = _split_pair_line(line);
    const outsLeft = new Set(fst.apply(left));
    if (outsLeft.has(right)) {
      expectedMap[left] = expectedMap[left] || new Set();
      expectedMap[left].add(right);
    } else {
      const outsRight = new Set(fst.apply(right));
      if (outsRight.has(left)) {
        expectedMap[right] = expectedMap[right] || new Set();
        expectedMap[right].add(left);
      } else {
        throw new Error(
          `${test.name} FAILED: neither apply("${left}") contains "${right}" nor apply("${right}") contains "${left}".`
        );
      }
    }
  }

  const missingLines: string[] = [];
  const extraLines: string[] = [];
  for (const [inp, expOuts] of Object.entries(expectedMap)) {
    const gotOuts = new Set(Array.from(fst.apply(inp)).map(x => x instanceof Array ? x[0]: x));
    const missing = new Set([...expOuts].filter(x => !gotOuts.has(x)));
    const extra = new Set([...gotOuts].filter(x => !expOuts.has(x)));
    for (const m of missing) {
      missingLines.push(`${inp} -> ${m}`);
    }
    for (const e of extra) {
      extraLines.push(`${inp} -> ${e}`);
    }
  }

  if (missingLines.length > 0 || extraLines.length > 0) {
    const msg: string[] = [`${test.name} FAILED`];
    if (missingLines.length > 0) {
      msg.push("Missing:");
      msg.push(...missingLines.map(x => `  ${x}`));
    }
    if (extraLines.length > 0) {
      msg.push("Extra:");
      msg.push(...extraLines.map(x => `  ${x}`));
    }
    throw new Error(msg.join("\n"));
  }
  return true;
}

function run_accept_reject_test(test: AcceptRejectTest): boolean {
  const fst = compile(test.grammar);

  for (const [inp, shouldAccept] of Object.entries(test.cases)) {
    const outs = Array.from(fst.apply(inp));
    const accepted = outs.length > 0;
    if (accepted !== shouldAccept) {
      throw new Error(
        `${test.name} FAILED on "${inp}": expected accept=${shouldAccept}, got accept=${accepted}, outs=${JSON.stringify(outs)}`
      );
    }
    if (shouldAccept && test.require_identity_outputs) {
      if (!outs.includes(inp)) {
        throw new Error(
          `${test.name} FAILED on "${inp}": expected identity output "${inp}" among outs=${JSON.stringify(outs)}`
        );
      }
    }
  }
  return true;
}

function run_gold_strings_test(test: GoldStringsTest): boolean {
  const parsed = parse_lexd(test.grammar);
  const fst = compile_lexd(parsed);

  const gold = new Set(test.gold_strings);
  const maxDepth = test.max_depth || _infer_max_depth_from_gold(test.gold_strings);
  const got = _enumerate_gold_strings(fst, maxDepth, 20000); // hard code max_strings

  if (got.size !== gold.size || ![...gold].every(x => got.has(x))) {
    const missing = [...gold].filter(x => !got.has(x)).sort();
    const extra = [...got].filter(x => !gold.has(x)).sort();
    const msg: string[] = [`${test.name} FAILED (gold strings mismatch)`];
    if (missing.length > 0) {
      msg.push("Missing:");
      msg.push(...missing.slice(0, 200).map(m => `  ${m}`));
      if (missing.length > 200) {
        msg.push(`  ... (${missing.length - 200} more)`);
      }
    }
    if (extra.length > 0) {
      msg.push("Extra:");
      msg.push(...extra.slice(0, 200).map(e => `  ${e}`));
      if (extra.length > 200) {
        msg.push(`  ... (${extra.length - 200} more)`);
      }
    }
    throw new Error(msg.join("\n"));
  }
  return true;
}


describe("Hand Tests", () => {
  HAND_TESTS.forEach((test_case, index) => {
    test(`Hand Test ${index + 1}: ${test_case.name}`, () => {
      if ('expected_lines' in test_case) {
        expect(run_pair_test(test_case)).toBeTruthy();
      }
      else {
        expect(run_accept_reject_test(test_case)).toBeTruthy();
        }
    });
  });
});

describe("C++ Feature Tests", () => {
  CPP_TESTS.forEach((test_case) => {
    test(`C++ Test: ${test_case.name}`, () => {
      expect(run_gold_strings_test(test_case)).toBeTruthy();
    });
  });
});
