import { test } from 'node:test';
import assert from 'node:assert/strict';
import { stripComments, parseLemmas, parseInductives } from './coq-parse.mjs';

test('stripComments blanks nested comments but keeps offsets and newlines', () => {
  const src = 'a (* x (* y *)\n z *) b';
  const out = stripComments(src);
  assert.equal(out.length, src.length);
  assert.equal(out.replace(/\s+/g, ' '), 'a b');
  assert.equal(out.split('\n').length, 2);
});

test('parseLemmas classifies how each proof ends', () => {
  const src = [
    'Lemma a : True.', 'Proof. auto. Qed.',
    'Lemma b : True.', 'Proof.', '  - (* Case1 *) auto.', '  - (* Case2 *) admit.', 'Admitted.',
    'Lemma c : True.', 'Proof.', 'Admitted.',
    'Lemma d : True.', 'Abort.',
    '(* Lemma hidden : True. Proof. Qed. *)',
    'Module FooTest.', '  Lemma t : True. Proof. auto. Qed.', 'End FooTest.',
    'Example e := 3.',
  ].join('\n');
  const ls = Object.fromEntries(parseLemmas('X.v', src).map((l) => [l.name, l]));
  assert.deepEqual(Object.keys(ls), ['a', 'b', 'c', 'd', 't']);
  assert.equal(ls.a.status, 'proved');
  assert.equal(ls.b.status, 'partial');
  assert.equal(ls.c.status, 'stated');
  assert.equal(ls.d.status, 'aborted');
  assert.equal(ls.t.isTest, true);
  assert.deepEqual(ls.b.cases.map((c) => [c.label, c.status]), [['Case1', 'closed'], ['Case2', 'open']]);
});

test('bullet nesting: an admit in a sub-case opens the parent case', () => {
  const src = [
    'Lemma p : True.', 'Proof.',
    '  - (* A *)', '    + (* A1 *) auto.', '    + (* A2 *) admit.',
    '  - (* B *)', '    + (* B1 *) auto.',
    'Admitted.',
  ].join('\n');
  const [p] = parseLemmas('X.v', src);
  assert.deepEqual(
    p.cases.map((c) => [c.label, c.level, c.status]),
    [['A', 0, 'open'], ['A1', 1, 'closed'], ['A2', 1, 'open'], ['B', 0, 'closed'], ['B1', 1, 'closed']],
  );
});

test('parseInductives ignores commented constructors and `Proof with`', () => {
  const src = [
    'Lemma x : True. Proof with eauto. auto. Qed.',
    'Inductive instr :=',
    '  | Const (v: nat)',
    '  (* | Cvtop (op: nat) *)',
    '  | Drop.',
    'Inductive r : nat -> Prop :=',
    '  | R0 : r 0',
    'with s : nat -> Prop :=',
    '  | S0 : (match 0 with 0 => True | _ => False end) -> s 0.',
  ].join('\n');
  const inds = Object.fromEntries(parseInductives('X.v', src).map((i) => [i.name, i.constructors.map((c) => c.name)]));
  assert.deepEqual(inds, { instr: ['Const', 'Drop'], r: ['R0'], s: ['S0'] });
});
