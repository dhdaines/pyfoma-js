// -*- js-indent-level: 2 -*-
import { describe, expect, test } from 'vitest';
import { compile, parse_lexd } from "./lexd.js";

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
