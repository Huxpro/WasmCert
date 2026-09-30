// Every outbound link on the site goes through one of these registries, so a
// broken anchor is fixed in one place (and `npm run check-refs` can verify them).

/**
 * The mechanization was written in 2019 against the Wasm 1.0 spec plus the
 * multi-value proposal. The W3C 1.0 Recommendation is the closest stable
 * snapshot: the living spec (3.0) has since dropped evaluation contexts.
 */
export const SPEC_BASE = 'https://www.w3.org/TR/2019/REC-wasm-core-1-20191205/';
export const SPEC_LABEL = 'Wasm 1.0 spec';

export interface SpecRef {
  kind: 'spec';
  anchor: string;
  title: string;
}

const spec = (anchor: string, title: string): SpecRef => ({ kind: 'spec', anchor, title });

export const SPEC = {
  structureInstr: spec('syntax-instr', 'Structure › Instructions'),
  validInstr: spec('valid-instr', 'Validation › Instructions'),
  validInstrSeq: spec('valid-instr-seq', 'Validation › Instruction sequences'),
  validModule: spec('valid-module', 'Validation › Modules'),
  execInstr: spec('exec-instr', 'Execution › Instructions'),
  execNumeric: spec('exec-numeric', 'Execution › Numerics'),
  adminInstr: spec('syntax-instr-admin', 'Runtime › Administrative instructions'),
  trap: spec('syntax-trap', 'Runtime › Trap'),
  label: spec('syntax-label', 'Runtime › Labels'),
  blockCtx: spec('syntax-ctxt-block', 'Runtime › Block contexts'),
  evalCtx: spec('syntax-ctxt-eval', 'Runtime › Evaluation contexts'),
  config: spec('syntax-config', 'Runtime › Configurations'),
  store: spec('syntax-store', 'Runtime › Store'),
  result: spec('syntax-result', 'Runtime › Results'),
  soundness: spec('soundness', 'Appendix › Soundness'),
  soundnessStatement: spec('soundness-statement', 'Appendix › Soundness › Theorems'),
  validConfig: spec('valid-config', 'Appendix › Configuration validity'),
  validThread: spec('valid-thread', 'Appendix › Thread validity'),
  validFrame: spec('valid-frame', 'Appendix › Frame validity'),
  validAdmin: spec('valid-instr-admin', 'Appendix › Administrative instructions'),
  validStore: spec('valid-store', 'Appendix › Store validity'),
  validResult: spec('valid-result', 'Appendix › Result validity'),
  extendStore: spec('extend-store', 'Appendix › Store extension'),
} satisfies Record<string, SpecRef>;

/** Per-instruction anchors follow the spec's own `exec-*` / `valid-*` convention. */
export const specExec = (slug: string, name: string) => spec(`exec-${slug}`, `Execution › ${name}`);
export const specValid = (slug: string, name: string) => spec(`valid-${slug}`, `Validation › ${name}`);

export const specHref = (r: SpecRef) => `${SPEC_BASE}#${r.anchor}`;

// ---------------------------------------------------------------------------
// Software Foundations

export interface SfRef {
  kind: 'sf';
  volume: 'LF' | 'PLF';
  chapter: string;
  section?: string;
}

const sf = (volume: SfRef['volume'], chapter: string, section?: string): SfRef => ({
  kind: 'sf',
  volume,
  chapter,
  section,
});

/**
 * SF's own anchors (`#lab237`) are renumbered between releases, so section
 * links use a text fragment instead: browsers that support it scroll to the
 * heading, the rest simply open the chapter.
 */
export const sfHref = (r: SfRef) => {
  const base = `https://softwarefoundations.cis.upenn.edu/${r.volume.toLowerCase()}-current/${r.chapter}.html`;
  return r.section ? `${base}#:~:text=${encodeURIComponent(r.section)}` : base;
};

export const SF = {
  // Logical Foundations
  varyingIH: sf('LF', 'Tactics', 'Varying the Induction Hypothesis'),
  inductionOnEvidence: sf('LF', 'IndProp', 'Induction on Evidence'),
  invertingEvidence: sf('LF', 'IndProp', 'Destructing and Inverting Evidence'),
  rememberTactic: sf('LF', 'IndProp', 'The remember Tactic'),
  reflection: sf('LF', 'IndProp', 'Case Study: Improving Reflection'),
  lists: sf('LF', 'Lists'),
  // Programming Language Foundations
  smallstepRelations: sf('PLF', 'Smallstep', 'Relations'),
  smallstepValues: sf('PLF', 'Smallstep', 'Values'),
  normalForms: sf('PLF', 'Smallstep', 'Strong Progress and Normal Forms'),
  multiStep: sf('PLF', 'Smallstep', 'Multi-Step Reduction'),
  stackMachine: sf('PLF', 'Smallstep', 'A Small-Step Stack Machine'),
  typesCanonical: sf('PLF', 'Types', 'Canonical forms'),
  typesProgress: sf('PLF', 'Types', 'Progress'),
  typesPreservation: sf('PLF', 'Types', 'Type Preservation'),
  typesSoundness: sf('PLF', 'Types', 'Type Soundness'),
  stlcCanonical: sf('PLF', 'StlcProp', 'Canonical Forms'),
  stlcWeakening: sf('PLF', 'StlcProp', 'The Weakening Lemma'),
  stlcUniqueness: sf('PLF', 'StlcProp', 'Uniqueness of Types'),
  stlcContextInvariance: sf('PLF', 'StlcProp', 'Context Invariance'),
  refStoreTypings: sf('PLF', 'References', 'Store typings'),
  refWellTypedStores: sf('PLF', 'References', 'Well-Typed Stores'),
  refExtending: sf('PLF', 'References', 'Extending Store Typings'),
  refWeakeningStores: sf('PLF', 'References', 'Weakening for Stores'),
  typechecking: sf('PLF', 'Typechecking'),
  useTactics: sf('PLF', 'UseTactics'),
  useAuto: sf('PLF', 'UseAuto'),
} satisfies Record<string, SfRef>;

export const sfLabel = (r: SfRef) => `${r.volume} · ${r.chapter}${r.section ? ` § ${r.section}` : ''}`;

// ---------------------------------------------------------------------------
// Other literature the code itself cites

export interface WebRef {
  kind: 'web';
  href: string;
  title: string;
}

export const WEB = {
  multiValue: {
    kind: 'web',
    href: 'https://github.com/WebAssembly/multi-value/blob/master/proposals/multi-value/Overview.md',
    title: 'Multi-value proposal',
  },
  report: {
    kind: 'web',
    href: 'https://www.cs.rit.edu/~mtf/student-resources/20191_huang_mscourse.pdf',
    title: 'Project report (RIT, 2019)',
  },
  pldi2017: {
    kind: 'web',
    href: 'https://dl.acm.org/doi/10.1145/3062341.3062363',
    title: 'Haas et al., Bringing the Web up to Speed with WebAssembly (PLDI 2017)',
  },
  cpp2018: {
    kind: 'web',
    href: 'https://dl.acm.org/doi/10.1145/3167082',
    title: 'Watt, Mechanising and Verifying the WebAssembly Specification (CPP 2018)',
  },
} satisfies Record<string, WebRef>;

export type Ref = SpecRef | SfRef | WebRef;

export const refHref = (r: Ref) => (r.kind === 'spec' ? specHref(r) : r.kind === 'sf' ? sfHref(r) : r.href);
export const refLabel = (r: Ref) => (r.kind === 'spec' ? r.title : r.kind === 'sf' ? sfLabel(r) : r.title);
