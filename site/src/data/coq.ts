// Typed view over the generated index (scripts/extract-coq.mjs), plus the
// status arithmetic every component shares.

import raw from '../generated/coq-index.json';

export type LemmaStatus = 'proved' | 'partial' | 'stated' | 'aborted';
export type Trust = 'closed' | 'modulo' | 'open';

export interface ProofCase {
  label: string;
  level: number;
  line: number;
  status: 'open' | 'closed';
  admits: number;
}

export interface Lemma {
  name: string;
  kind: string;
  file: string;
  line: number;
  endLine: number;
  status: LemmaStatus;
  admits: number;
  isTest: boolean;
  cases: ProofCase[];
  deps: string[];
  trust: Trust | null;
  blockedBy?: string[];
}

export interface Inductive {
  name: string;
  file: string;
  line: number;
  constructors: { name: string; line: number }[];
}

export interface FileStat {
  file: string;
  lines: number;
  proved: number;
  partial: number;
  stated: number;
  aborted: number;
}

interface CoqIndex {
  repo: string;
  commit: string;
  commitDate: string | null;
  files: FileStat[];
  tactics: Record<string, number>;
  lemmas: Record<string, Lemma>;
  inductives: Record<string, Inductive>;
}

export const coq = raw as CoqIndex;

export const lemma = (name: string): Lemma | undefined => coq.lemmas[name];
export const inductive = (name: string): Inductive | undefined => coq.inductives[name];

export const realLemmas = Object.values(coq.lemmas).filter((l) => !l.isTest);

export const sourceHref = (file: string, line?: number, endLine?: number) =>
  `https://github.com/${coq.repo}/blob/${coq.commit}/coq/${file}` +
  (line ? `#L${line}${endLine && endLine !== line ? `-L${endLine}` : ''}` : '');

/** Where a constructor (e.g. `SS_br`, `VI_block`) is defined, if it exists. */
export function constructorSite(name: string): { file: string; line: number; of: string } | undefined {
  for (const ind of Object.values(coq.inductives)) {
    const c = ind.constructors.find((c) => c.name === name);
    if (c) return { file: ind.file, line: c.line, of: ind.name };
  }
  return undefined;
}

// ---------------------------------------------------------------------------
// Cell status: the single vocabulary used by badges, matrix cells and graph nodes.

/**
 *  proved   – Qed, and everything it depends on is Qed
 *  modulo   – Qed, but leans (transitively) on an admitted lemma
 *  open     – the proof exists but this part is admitted
 *  missing  – the case or lemma is not there yet
 *  na       – nothing to prove (e.g. values don't step)
 */
export type Status = 'proved' | 'modulo' | 'open' | 'missing' | 'na';

export const STATUS_ORDER: Status[] = ['missing', 'open', 'modulo', 'proved', 'na'];
export const worst = (xs: Status[]): Status =>
  xs.length === 0 ? 'na' : xs.reduce((a, b) => (STATUS_ORDER.indexOf(a) <= STATUS_ORDER.indexOf(b) ? a : b));

/** A pointer at a lemma, optionally narrowed to one labelled bullet case. */
export interface ProofPoint {
  lemma: string;
  case?: string;
}

export function pointStatus(p: ProofPoint): Status {
  const l = lemma(p.lemma);
  if (!l) return 'missing';
  if (p.case) {
    const cs = l.cases.filter((c) => c.label === p.case);
    if (cs.length === 0) return 'missing';
    if (cs.some((c) => c.status === 'open')) return 'open';
    // A closed case of a Qed proof inherits the lemma's trust; of an Admitted proof it is fine on its own.
    return l.status === 'proved' && l.trust === 'modulo' ? 'modulo' : 'proved';
  }
  if (l.status === 'proved') return l.trust === 'closed' ? 'proved' : 'modulo';
  return l.status === 'aborted' ? 'missing' : 'open';
}

export const pointsStatus = (ps: ProofPoint[]) => worst(ps.map(pointStatus));

export const STATUS_LABEL: Record<Status, string> = {
  proved: 'Proved',
  modulo: 'Proved, relies on admits',
  open: 'Admitted',
  missing: 'Not started',
  na: 'Nothing to prove',
};

export const LEMMA_STATUS_LABEL: Record<LemmaStatus, string> = {
  proved: 'Qed',
  partial: 'Admitted, partly proved',
  stated: 'Admitted, statement only',
  aborted: 'Aborted',
};

export function totals() {
  const by = (s: LemmaStatus) => realLemmas.filter((l) => l.status === s).length;
  return {
    all: realLemmas.length,
    proved: by('proved'),
    closed: realLemmas.filter((l) => l.trust === 'closed').length,
    partial: by('partial'),
    stated: by('stated'),
    aborted: by('aborted'),
    admits: realLemmas.reduce((n, l) => n + (l.status === 'proved' ? 0 : l.admits), 0),
  };
}

/** Closed vs total for the bullet cases of a lemma whose labels match `pattern`. */
export function caseTally(name: string, pattern: RegExp) {
  const cs = lemma(name)?.cases.filter((c) => pattern.test(c.label)) ?? [];
  return { closed: cs.filter((c) => c.status === 'closed').length, total: cs.length, cases: cs };
}
