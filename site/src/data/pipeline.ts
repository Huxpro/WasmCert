// The four stages of the mechanization, in the order the spec presents them.

import { coq, inductive, type FileStat } from './coq';
import { SPEC, type SpecRef } from './refs';

export interface Stage {
  id: string;
  name: string;
  /** What the stage means to someone who writes Wasm, not proofs. */
  question: string;
  blurb: string;
  spec: SpecRef;
  files: string[];
  /** Inductives whose constructor counts summarise the stage. */
  measures: { inductive: string; label: string }[];
}

export const STAGES: Stage[] = [
  {
    id: 'syntax',
    name: 'Structure',
    question: 'What is a Wasm program?',
    blurb: 'Values, types and the instruction set, as Coq datatypes.',
    spec: SPEC.structureInstr,
    files: ['Int.v', 'Float.v', 'Types.v', 'Values.v', 'Commons.v', 'Structure.v'],
    measures: [{ inductive: 'instr', label: 'instructions' }],
  },
  {
    id: 'validation',
    name: 'Validation',
    question: 'Which programs does the type checker accept?',
    blurb: 'Typing rules that every engine runs before executing a module.',
    spec: SPEC.validInstr,
    files: ['Validation.v'],
    measures: [{ inductive: 'valid_instr', label: 'typing rules' }],
  },
  {
    id: 'execution',
    name: 'Execution',
    question: 'What does running a program do?',
    blurb: 'A small-step semantics: how one configuration reduces to the next.',
    spec: SPEC.execInstr,
    files: ['Numerics.v', 'Execution.v'],
    measures: [
      { inductive: 'step_simple', label: 'simple rules' },
      { inductive: 'step', label: 'config rules' },
    ],
  },
  {
    id: 'soundness',
    name: 'Soundness',
    question: 'Is passing the checker enough to never get stuck?',
    blurb: 'Runtime typing, then progress and preservation.',
    spec: SPEC.soundness,
    files: ['ExtendedTyping.v', 'ProofAux.v', 'Progress.v', 'Preservation.v', 'Soundness.v'],
    measures: [],
  },
];

export function stageStats(s: Stage) {
  const files = s.files.map((f) => coq.files.find((x) => x.file === f)).filter(Boolean) as FileStat[];
  const sum = (k: keyof Omit<FileStat, 'file'>) => files.reduce((n, f) => n + f[k], 0);
  return {
    files,
    lines: sum('lines'),
    proved: sum('proved'),
    partial: sum('partial'),
    stated: sum('stated'),
    aborted: sum('aborted'),
    measures: s.measures.map((m) => ({ ...m, count: inductive(m.inductive)?.constructors.length ?? 0 })),
  };
}
