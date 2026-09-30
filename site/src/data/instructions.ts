// The instruction coverage matrix: one row per Wasm instruction (or family).
// Only the *mapping* is curated here; every status is computed from the Coq
// source via the generated index, so the matrix updates itself as proofs land.

import { constructorSite, pointsStatus, type ProofPoint, type Status } from './coq';
import { specExec, specValid, type SpecRef } from './refs';

export type Group = 'Numeric' | 'Parametric' | 'Variable' | 'Memory' | 'Control' | 'Administrative';

export interface InstructionRow {
  id: string;
  /** How it is written in the spec / text format. */
  name: string;
  group: Group;
  /** One plain-English line for readers who have never opened the spec. */
  blurb: string;
  spec?: { exec?: SpecRef; valid?: SpecRef };
  /** Constructor of `instr` (or `admin_instr`) in Coq. */
  syntax: string;
  /** Typing rule constructor(s). */
  validation: string[];
  /** Reduction rule constructor(s); `'value'` for things that never step. */
  execution: string[] | 'value';
  progress: ProofPoint[];
  preservation: ProofPoint[] | 'na';
  /** Proof-graph edge that explains the interesting part of this row. */
  edge?: string;
}

const p = (lemma: string, c?: string): ProofPoint => ({ lemma, case: c });
const PROG = 'progress';
const VAI = 'preservation_SC_simple_VAI_instr';

const s = (slug: string, name: string) => ({ exec: specExec(slug, name), valid: specValid(slug, name) });

export const INSTRUCTIONS: InstructionRow[] = [
  // Numeric ------------------------------------------------------------------
  {
    id: 'const', name: 't.const c', group: 'Numeric', blurb: 'Pushes a constant. It is already a value, so it never steps.',
    spec: s('const', 't.const'), syntax: 'Const', validation: ['VI_const'], execution: 'value',
    progress: [p(PROG, 'VI_const')], preservation: 'na', edge: 'normal-forms',
  },
  {
    id: 'unop', name: 't.unop', group: 'Numeric', blurb: 'Pops one number, pushes the result (clz, abs, neg, …).',
    spec: s('unop', 't.unop'), syntax: 'Unop', validation: ['VI_unop'], execution: ['SS_unop__some', 'SS_unop__none'],
    progress: [p(PROG, 'VI_unop'), p('eval_unop_no_runtime_err')],
    preservation: [p(VAI, 'VI_unop'), p('eval_unop_preserve_type')], edge: 'canonical-forms',
  },
  {
    id: 'binop', name: 't.binop', group: 'Numeric', blurb: 'Pops two numbers, pushes the result, or traps (e.g. divide by zero).',
    spec: s('binop', 't.binop'), syntax: 'Binop', validation: ['VI_binop'], execution: ['SS_binop__some', 'SS_binop__none'],
    progress: [p(PROG, 'VI_binop'), p('eval_binop_no_runtime_err')],
    preservation: [p(VAI, 'VI_binop'), p('eval_binop_preserve_type')], edge: 'canonical-forms',
  },
  {
    id: 'testop', name: 't.testop', group: 'Numeric', blurb: 'Tests one number (eqz) and pushes an i32 boolean.',
    spec: s('testop', 't.testop'), syntax: 'Testop', validation: ['VI_testop'], execution: ['SS_testop'],
    progress: [p(PROG, 'VI_testop'), p('eval_testop_no_runtime_err')],
    preservation: [p(VAI, 'VI_testop')], edge: 'numeric-preservation',
  },
  {
    id: 'relop', name: 't.relop', group: 'Numeric', blurb: 'Compares two numbers and pushes an i32 boolean.',
    spec: s('relop', 't.relop'), syntax: 'Relop', validation: ['VI_relop'], execution: ['SS_relop'],
    progress: [p(PROG, 'VI_relop'), p('eval_relop_no_runtime_err')],
    preservation: [p(VAI, 'VI_relop')], edge: 'numeric-preservation',
  },
  {
    id: 'cvtop', name: 't.cvtop', group: 'Numeric', blurb: 'Converts between number types (wrap, extend, trunc, …).',
    spec: s('cvtop', 't.cvtop'), syntax: 'Cvtop', validation: ['VI_cvtop'], execution: ['SS_cvtop'],
    progress: [p(PROG, 'VI_cvtop')], preservation: [p(VAI, 'VI_cvtop')],
  },
  // Parametric ---------------------------------------------------------------
  {
    id: 'drop', name: 'drop', group: 'Parametric', blurb: 'Throws away the top value, whatever its type.',
    spec: s('drop', 'drop'), syntax: 'Drop', validation: ['VI_drop'], execution: ['SS_drop'],
    progress: [p(PROG, 'VI_drop')], preservation: [p(VAI, 'VI_drop')],
  },
  {
    id: 'select', name: 'select', group: 'Parametric', blurb: 'Picks one of two values based on an i32 condition.',
    spec: s('select', 'select'), syntax: 'Select', validation: ['VI_select'], execution: ['SS_select1', 'SS_select2'],
    progress: [p(PROG, 'VI_select')], preservation: [p(VAI, 'VI_select')],
  },
  // Variable -----------------------------------------------------------------
  {
    id: 'local', name: 'local.get / set / tee', group: 'Variable', blurb: 'Reads or writes a local variable of the current function.',
    spec: s('local-get', 'local.get'), syntax: 'Local_get', validation: ['VI_local_get', 'VI_local_set', 'VI_local_tee'],
    execution: ['SC_local_get', 'SC_local_set', 'SC_local_tee'],
    progress: [p(PROG, 'VI_local_get')], preservation: [p('preservation', 'SC_local_get')],
  },
  {
    id: 'global', name: 'global.get / set', group: 'Variable', blurb: 'Reads or writes a module-level global.',
    spec: s('global-get', 'global.get'), syntax: 'Global_get', validation: ['VI_global_get', 'VI_global_set'],
    execution: ['SC_global_get', 'SC_global_set'],
    progress: [p(PROG, 'VI_global_get')], preservation: [p('preservation', 'SC_global_get')], edge: 'store-extension',
  },
  // Memory -------------------------------------------------------------------
  {
    id: 'memory', name: 'load / store / memory.*', group: 'Memory', blurb: 'Reads and writes linear memory; grows it.',
    spec: s('load', 't.load'), syntax: 'Load', validation: ['VI_load', 'VI_store'], execution: ['SC_load', 'SC_store'],
    progress: [p(PROG, 'VI_load')], preservation: [p('preservation', 'SC_load')], edge: 'store-extension',
  },
  // Control ------------------------------------------------------------------
  {
    id: 'nop', name: 'nop', group: 'Control', blurb: 'Does nothing.',
    spec: s('nop', 'nop'), syntax: 'Nop', validation: ['VI_nop'], execution: ['SS_nop'],
    progress: [p(PROG, 'VI_nop')], preservation: [p(VAI, 'VI_nop')],
  },
  {
    id: 'unreachable', name: 'unreachable', group: 'Control', blurb: 'Traps immediately. Its type is anything you like.',
    spec: s('unreachable', 'unreachable'), syntax: 'Unreachable', validation: ['VI_unreachable'], execution: ['SS_unreachable'],
    progress: [p(PROG, 'VI_unreachable')], preservation: [p(VAI, 'VI_unreachable')], edge: 'replacement',
  },
  {
    id: 'block', name: 'block', group: 'Control', blurb: 'Runs a body; a branch to it jumps to the end.',
    spec: s('block', 'block'), syntax: 'Block', validation: ['VI_block'], execution: ['SC_block', 'SS_block__exit'],
    progress: [p(PROG, 'VI_block')], preservation: [p('preservation', 'SC_block'), p('preservation_SC_block')],
    edge: 'label-typing',
  },
  {
    id: 'loop', name: 'loop', group: 'Control', blurb: 'Runs a body; a branch to it jumps back to the start.',
    spec: s('loop', 'loop'), syntax: 'Loop', validation: ['VI_loop'], execution: ['SC_loop'],
    progress: [p(PROG, 'VI_loop')], preservation: [p('preservation', 'SC_loop'), p('preservation_SC_loop')],
    edge: 'label-typing',
  },
  {
    id: 'if', name: 'if … else', group: 'Control', blurb: 'Pops an i32 and runs one of two bodies as a block.',
    spec: s('if', 'if'), syntax: 'If', validation: ['VI_if'], execution: ['SC_if__nez', 'SC_if__eqz'],
    progress: [p(PROG, 'VI_if')],
    preservation: [p('preservation', 'SC_if__nez'), p('preservation', 'SC_if2'), p('preservation_SC_if__nez'), p('preservation_SC_if__eqz')],
    edge: 'label-typing',
  },
  {
    id: 'br', name: 'br l', group: 'Control', blurb: 'Jumps out to the l-th enclosing block, carrying values along.',
    spec: s('br', 'br'), syntax: 'Br', validation: ['VI_br'], execution: ['SS_br'],
    progress: [p(PROG, 'VI_br')],
    preservation: [p('preservation_SC_simple_VAIS_snoc', 'VAI_label'), p('preservation_SC_simple_VAI_label'), p('Bl_give_vals')],
    edge: 'block-contexts',
  },
  {
    id: 'br_if', name: 'br_if l', group: 'Control', blurb: 'Pops an i32; branches if it is non-zero.',
    spec: s('br-if', 'br_if'), syntax: 'Br_if', validation: ['VI_br_if'], execution: ['SS_br_if1', 'SS_br_if2'],
    progress: [p(PROG, 'VI_br_if')], preservation: [p(VAI, 'VI_br_if')],
  },
  {
    id: 'br_table', name: 'br_table', group: 'Control', blurb: 'Pops an index and branches to the matching label (a switch).',
    spec: s('br-table', 'br_table'), syntax: 'Br_table', validation: ['VI_br_table'], execution: ['SS_br_table__i', 'SS_br_table__N'],
    progress: [p(PROG, 'VI_br_table')], preservation: [p(VAI, 'VI_br_table')],
  },
  {
    id: 'return', name: 'return', group: 'Control', blurb: 'Leaves the current function with its results.',
    spec: s('return', 'return'), syntax: 'Return', validation: ['VI_return'], execution: ['SS_return'],
    progress: [p(PROG, 'VI_return')], preservation: [p(VAI, 'VI_return')],
  },
  {
    id: 'call', name: 'call f', group: 'Control', blurb: 'Calls a function of the module.',
    spec: s('call', 'call'), syntax: 'Call', validation: ['VI_call'], execution: ['SC_call'],
    progress: [p(PROG, 'VI_call')], preservation: [p('preservation', 'SC_call')],
  },
  {
    id: 'call_indirect', name: 'call_indirect', group: 'Control', blurb: 'Calls through a table, checking the signature at run time.',
    spec: s('call-indirect', 'call_indirect'), syntax: 'Call_indirect', validation: ['VI_call_indirect'],
    execution: ['SC_call_indirect', 'SC_call_indirect__trap'],
    progress: [p(PROG, 'VI_call_indirect')], preservation: [p('preservation', 'SC_call_indirect')],
  },
  // Administrative (runtime-only) ---------------------------------------------
  {
    id: 'trap', name: 'trap', group: 'Administrative', blurb: 'Runtime-only: an error that aborts the whole computation.',
    syntax: 'Trap', validation: ['VAI_trap'], execution: ['SC_trap__E'],
    progress: [p(PROG, 'VAI_trap')], preservation: [p('preservation', 'SC_trap__E')], edge: 'normal-forms',
  },
  {
    id: 'label', name: 'label', group: 'Administrative', blurb: 'Runtime-only: marks an entered block so a branch knows where to go.',
    syntax: 'Label', validation: ['VAI_label'], execution: ['SS_block__exit'],
    progress: [p(PROG, 'VAIS_label')],
    preservation: [p('preservation_SC_simple_VAIS_snoc', 'VAI_label'), p('preservation', 'SC_E')], edge: 'replacement',
  },
];

// ---------------------------------------------------------------------------

export type ModelStatus = 'modeled' | 'partial' | 'absent';

function modeled(names: string[]): ModelStatus {
  const hits = names.filter((n) => constructorSite(n)).length;
  return hits === names.length ? 'modeled' : hits === 0 ? 'absent' : 'partial';
}

export interface RowStatus {
  syntax: ModelStatus;
  validation: ModelStatus;
  execution: ModelStatus | 'value';
  progress: Status;
  preservation: Status;
}

export function rowStatus(r: InstructionRow): RowStatus {
  const syntax = modeled([r.syntax]);
  return {
    syntax,
    validation: modeled(r.validation),
    execution: r.execution === 'value' ? 'value' : modeled(r.execution),
    progress: pointsStatus(r.progress),
    preservation: r.preservation === 'na' ? 'na' : pointsStatus(r.preservation),
  };
}

export const GROUPS: Group[] = ['Numeric', 'Parametric', 'Variable', 'Memory', 'Control', 'Administrative'];
