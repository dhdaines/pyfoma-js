// -*- js-indent-level: 2 -*-
import { describe, expect, test } from 'vitest'
import { MinHeap, PartitionRefinement, Transition, State, labelKey } from './pyfoma.js';

describe('MinHeap', () => {
  test('initializion of an empty heap', () => {
    const heap = new MinHeap();
    expect(heap.size).toBe(0);
    expect(heap.pop()).toBeUndefined();
  });

  test('pushing and popping a single element', () => {
    const heap = new MinHeap();
    heap.push([10, 'a']);
    expect(heap.size).toBe(1);
    expect(heap.pop()).toEqual([10, 'a']);
    expect(heap.size).toBe(0);
  });

  test('that min-heap property is maintained with multiple elements', () => {
    const heap = new MinHeap();
    heap.push([3, 'c']);
    heap.push([1, 'a']);
    heap.push([2, 'b']);
    heap.push([0, 'd']);
    heap.push([5, 'e']);

    expect(heap.pop()).toEqual([0, 'd']);
    expect(heap.pop()).toEqual([1, 'a']);
    expect(heap.pop()).toEqual([2, 'b']);
    expect(heap.pop()).toEqual([3, 'c']);
    expect(heap.pop()).toEqual([5, 'e']);
    expect(heap.size).toBe(0);
  });

  test('that elements with the same priority function are retained properly', () => {
    const heap = new MinHeap();
    heap.push([1, 'a']);
    heap.push([1, 'b']);
    heap.push([1, 'c']);

    const results = [];
    while (heap.size > 0) {
      results.push(heap.pop()![1]);
    }
    expect(results).toContain("a");
    expect(results).toContain("b");
    expect(results).toContain("c");
  });


  test('that complex data types as values can work', () => {
    const heap = new MinHeap();
    const obj1 = { id: 1, data: 'test' };
    const obj2 = { id: 2, data: 'example' };
    const arr1 = [1, 2, 3];
    const arr2 = [4, 5, 6];

    heap.push([10, obj1]);
    heap.push([5, obj2]);
    heap.push([15, arr1]);
    heap.push([0, arr2]);

    expect(heap.pop()![1]).toBe(arr2);
    expect(heap.pop()![1]).toBe(obj2);
    expect(heap.pop()![1]).toBe(obj1);
    expect(heap.pop()![1]).toBe(arr1);
  });

  test('heap property is retained after mixed push and pop operations', () => {
    const heap = new MinHeap();
    heap.push([10, 'a']);
    heap.push([20, 'b']);
    expect(heap.pop()).toEqual([10, 'a']);
    heap.push([5, 'c']);
    heap.push([1, 'd']);
    expect(heap.pop()).toEqual([1, 'd']);
    expect(heap.pop()).toEqual([5, 'c']);
    expect(heap.pop()).toEqual([20, 'b']);
  });

  test('handling a large number of elements', () => {
    const heap = new MinHeap();
    const elements = [];

    for (let i = 1000; i >= 0; i--) {
      elements.push(i);
      heap.push([i, `item${i}`]);  // the actual value is irrelevant here
    }

    const result = [];
    while (heap.size > 0) {
      result.push(heap.pop()![0]);
    }

    expect(result).toEqual(elements.sort((a, b) => a - b));
  });
});

describe("Transition", () => {
  test("constructor initializes properties correctly", () => {
    const targetState = new State();
    const label = ["a", "b"];
    const weight = 2.5;
    const transition = new Transition(targetState, label, weight);

    expect(transition.targetstate).toBe(targetState);
    expect(transition.label).toEqual(label);
    expect(transition.weight).toBe(weight);
  });
});

describe("State", () => {
  test("constructor initializes with default values", () => {
    const state = new State();

    expect(state.transitions).toEqual(new Map());
    expect(state._transitionsin).toBeNull();
    expect(state._transitionsout).toBeNull();
    expect(state.finalweight).toBe(Number.POSITIVE_INFINITY);
    expect(state.name).toBeNull();
  });

  test("constructor accepts custom finalweight and name", () => {
    const state = new State({ finalweight: 5.0, name: "test" });

    expect(state.finalweight).toBe(5.0);
    expect(state.name).toBe("test");
  });

  test("transitionsin returns transitions for input labels", () => {
    const state = new State();
    const targetState = new State();
    state.addTransition(targetState, ["a", "b"], 1.0);
    state.addTransition(targetState, ["c", "b"], 1.0);

    const transitionsIn = state.transitionsin;

    expect(transitionsIn).toBeInstanceOf(Map);
    expect(transitionsIn.has("a")).toBe(true);
    expect(transitionsIn.get("a").size).toBe(1);
    expect(transitionsIn.has("c")).toBe(true);
    expect(transitionsIn.get("c").size).toBe(1);
  });

  test("transitionsout returns transitions for output labels", () => {
    const state = new State();
    const targetState = new State();
    state.addTransition(targetState, ["a", "b"], 1.0);
    state.addTransition(targetState, ["c", "b"], 1.0);

    const transitionsOut = state.transitionsout;

    expect(transitionsOut).toBeInstanceOf(Map);
    expect(transitionsOut.has("b")).toBe(true);
    expect(transitionsOut.get("b").size).toBe(2);
  });

  test("renameLabel updates label and merges transitions", () => {
    const state = new State();
    const targetState = new State();
    const originalLabel = ["a", "b"];
    const newLabel = ["b", "c"];

    state.addTransition(targetState, ["a", "b"], 0);
    state.renameLabel(originalLabel, newLabel);

    expect(state.transitions.size).toBe(1);
    expect(state.transitions.has(labelKey(originalLabel))).toBe(false);
    expect(state.transitions.has(labelKey(newLabel))).toBe(true);
  });

  test("removeTransitionsToTargets removes transitions to specified targets", () => {
    const state = new State();
    const targetState1 = new State();
    const targetState2 = new State();

    state.addTransition(targetState1, ["a"], 1.0);
    state.addTransition(targetState2, ["b"], 2.0);

    state.removeTransitionsToTargets(new Set([targetState1]));

    expect(state.transitions.size).toBe(1);
    expect(state.transitions.has(labelKey(["b"]))).toBe(true);
  });

  test("addTransition adds new transition", () => {
    const state = new State();
    const targetState = new State();

    state.addTransition(targetState, ["a"], 1.0);

    expect(state.transitions.size).toBe(1);
    const transitions = state.transitions.get(labelKey(["a"]))!;
    expect(transitions.set.size).toBe(1);
    const transition = Array.from(transitions.set)[0];
    expect(transition.targetstate).toBe(targetState);
    expect(transition.weight).toBe(1.0);
  });

  test("addTransition deduplicates parallel arcs with same label and target", () => {
    const state = new State();
    const targetState = new State();
    const label = ["a"];

    state.addTransition(targetState, label, 3.0);
    state.addTransition(targetState, label, 1.0); // Should keep cheaper weight

    const transitions = state.transitions.get(labelKey(label))!;
    expect(transitions.set.size).toBe(1);
    const transition = Array.from(transitions.set)[0];
    expect(transition.weight).toBe(1.0);
  });

  test("allTransitions yields all transitions", () => {
    const state = new State();
    const targetState1 = new State();
    const targetState2 = new State();

    state.addTransition(targetState1, ["a"], 1.0);
    state.addTransition(targetState2, ["b"], 2.0);

    const transitions = Array.from(state.allTransitions());

    expect(transitions.length).toBe(2);
    expect(transitions).toContainEqual([["a"], expect.anything()]);
    expect(transitions).toContainEqual([["b"], expect.anything()]);
  });

  test("allTargets returns set of all target states", () => {
    const state = new State();
    const targetState1 = new State();
    const targetState2 = new State();

    state.addTransition(targetState1, ["a"], 1.0);
    state.addTransition(targetState2, ["b"], 2.0);

    const targets = state.allTargets();

    expect(targets.size).toBe(2);
    expect(targets.has(targetState1)).toBe(true);
    expect(targets.has(targetState2)).toBe(true);
  });

  test("allEpsilonTargetsCheapest returns cheapest epsilon transitions", () => {
    const state = new State();
    const targetState1 = new State();
    const targetState2 = new State();

    state.addTransition(targetState1, ["", "", ""], 3.0);
    state.addTransition(targetState1, [""], 1.0); // Equivalent, also epsilon
    state.addTransition(targetState2, ["a"], 2.0); // Not epsilon

    const epsilonTargets = state.allEpsilonTargetsCheapest();

    expect(epsilonTargets.size).toBe(1);
    expect(epsilonTargets.get(targetState1)).toBe(1.0);
  });

  test("allTargetsCheapest returns cheapest transitions to each target", () => {
    const state = new State();
    const targetState = new State();

    state.addTransition(targetState, ["a"], 3.0);
    state.addTransition(targetState, ["b"], 1.0); // Cheaper

    const targetsCheapest = state.allTargetsCheapest();

    expect(targetsCheapest.size).toBe(1);
    expect(targetsCheapest.get(targetState)).toBe(1.0);
  });
});

describe('PartitionRefinement', () => {
  test('refine with subset that splits a set', () => {
    const s1 = new Set([1, 2, 3]);
    const s2 = new Set([4, 5]);
    const S = new Set([s1, s2]);
    const pr = new PartitionRefinement(S);

    const R = new Set([1, 2]);
    const result = pr.refine(R);
    console.log(result);

    expect(result.length).toBe(1);
    const [AS, A_minus_AS] = result[0];
    expect(AS).toEqual(new Set([1, 2]));
    expect(A_minus_AS).toEqual(new Set([3])); // Remaining part of s1

    // Check that s1 in sets is now A_minus_AS (the remainder)
    expect(pr.sets.has(A_minus_AS)).toBe(true);
    expect(pr.sets.has(AS)).toBe(true);
    expect(pr.sets.size).toBe(3); // AS, A_minus_AS, s2

    // Check partition updates
    expect(pr.partition.get(1)).toBe(AS);
    expect(pr.partition.get(3)).toBe(A_minus_AS);
  });

  test('refine with subset that does not intersect any set', () => {
    const s1 = new Set([1, 2]);
    const s2 = new Set([3, 4]);
    const S = new Set([s1, s2]);
    const pr = new PartitionRefinement(S);

    const R = new Set([5, 6]); // disjoint set
    const result = pr.refine(R);

    expect(result.length).toBe(0);
    expect(pr.sets.size).toBe(2); // No change
  });

  test('refine with subset that is equal to a set', () => {
    const s1 = new Set([1, 2]);
    const s2 = new Set([3, 4]);
    const S = new Set([s1, s2]);
    const pr = new PartitionRefinement(S);

    const R = new Set([1, 2]); // equal to s1
    const result = pr.refine(R);

    expect(result.length).toBe(0);
    expect(pr.sets.size).toBe(2); // No change
  });

  test('refine with subset that intersects multiple sets', () => {
    const s1 = new Set([1, 2, 3]);
    const s2 = new Set([4, 5, 6]);
    const S = new Set([s1, s2]);
    const pr = new PartitionRefinement(S);

    const R = new Set([2, 5]); // intersects both s1 and s2
    const result = pr.refine(R);

    expect(result.length).toBe(2);

    // Result contains [AS, A] pairs
    const AS1 = result[0][0];
    const A_minus_AS1 = result[0][1];
    const AS2 = result[1][0];
    const A_minus_AS2 = result[1][1];

    expect(AS1).toEqual(new Set([2]));
    expect(A_minus_AS1).toEqual(new Set([1, 3]));
    expect(AS2).toEqual(new Set([5]));
    expect(A_minus_AS2).toEqual(new Set([4, 6]));

    expect(pr.sets.size).toBe(4); // AS1, A_minus_AS1, AS2, A_minus_AS2
  });

  test('asTuples returns correct representation', () => {
    const s1 = new Set([1, 2]);
    const s2 = new Set([3, 4]);
    const S = new Set([s1, s2]);
    const pr = new PartitionRefinement<number>(S);

    const tuples = pr.asTuples();
    expect(tuples.size).toBe(2);
    // Should contain [1, 2] or [2, 1] and [3, 4], or [4, 3]
    let contains12 = false;
    let contains34 = false;
    for (const tuple of tuples) {
      if (tuple.length == 2 && tuple.includes(1) && tuple.includes(2)) contains12 = true;
      if (tuple.length == 2 && tuple.includes(3) && tuple.includes(4)) contains34 = true;
    }
    expect(contains12).toBe(true);
    expect(contains34).toBe(true);
  });

  test('refine updates partition mapping correctly', () => {
    const s1 = new Set(['a', 'b', 'c']);
    const s2 = new Set(['d', 'e']);
    const S = new Set([s1, s2]);
    const pr = new PartitionRefinement(S);

    const R = new Set(['a', 'd']);
    pr.refine(R);

    // Original s1 should be split into {'a'} and {'b', 'c'}
    // Original s2 should be split into {'d'} and {'e'}
    expect(pr.sets.size).toBe(4);
    expect(pr.partition.get('a')).not.toBe(pr.partition.get('b'));
    expect(pr.partition.get('d')).not.toBe(pr.partition.get('e'));
    expect(pr.partition.get('d')).not.toBe(pr.partition.get('b'));
  });
});
