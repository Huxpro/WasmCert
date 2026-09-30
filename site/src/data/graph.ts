// The proof graph. Nodes are the load-bearing definitions and lemmas; edges are
// the proof *moves* that connect them. The edge text is the "second level" of
// the site: written for readers who know Software Foundations, and each edge
// points at the SF section that teaches the same move.

import { pointsStatus, type ProofPoint, type Status } from './coq';
import { SF, SPEC, WEB, specExec, type Ref } from './refs';

export type NodeKind = 'definition' | 'lemma' | 'theorem' | 'goal';

export interface GraphNode {
  id: string;
  label: string;
  kind: NodeKind;
  /** Column (left to right: definitions → toolbox → cases → theorems → top level) and row. */
  col: number;
  row: number;
  /** Plain-language one-liner. */
  summary: string;
  /** Lemmas behind the node (status is the worst of them). Definitions list inductives instead. */
  lemmas?: ProofPoint[];
  inductives?: string[];
  refs?: Ref[];
}

export interface GraphEdge {
  id: string;
  from: string;
  to: string;
  title: string;
  /** One sentence; shown on hover and in lists. */
  gist: string;
  /** Paragraphs; `code` spans are written with backticks. */
  body: string[];
  sf: Ref[];
  spec: Ref[];
  /** Where the move happens in Coq. Also decides the edge's status. */
  coq: ProofPoint[];
  /** For edges into a node that doesn't exist yet. */
  status?: Status;
}

export const COLUMNS = ['Definitions', 'Toolbox lemmas', 'Per-rule cases', 'Main theorems', 'Top level'];

const p = (lemma: string, c?: string): ProofPoint => ({ lemma, case: c });

export const NODES: GraphNode[] = [
  // Definitions -----------------------------------------------------------------
  {
    id: 'typing', label: 'Sequence typing', kind: 'definition', col: 0, row: 0,
    summary: 'Instructions are typed as stack transformers ts1 → ts2, built up one instruction at a time.',
    inductives: ['valid_instr', 'valid_admin_instr', 'valid_admin_instrs'], refs: [SPEC.validInstr, SPEC.validAdmin],
  },
  {
    id: 'config', label: 'Configuration typing', kind: 'definition', col: 0, row: 1,
    summary: 'A running program (store, frame, instructions) is well typed.',
    inductives: ['valid_config', 'valid_thread', 'valid_frame', 'result_thread'], refs: [SPEC.validConfig],
  },
  {
    id: 'step', label: 'Reduction ↪', kind: 'definition', col: 0, row: 2,
    summary: 'The small-step semantics: one rule per instruction behaviour.',
    inductives: ['step_simple', 'step'], refs: [SPEC.execInstr],
  },
  {
    id: 'evalctx', label: 'Evaluation contexts', kind: 'definition', col: 0, row: 3,
    summary: 'Where in a program the next step may happen: after values, or inside a label.',
    inductives: ['eval_context', 'block_context'], refs: [SPEC.evalCtx, SPEC.blockCtx],
  },
  {
    id: 'store', label: 'Store extension ⪯', kind: 'definition', col: 0, row: 4,
    summary: 'The store only grows; typings made against the old store stay valid.',
    inductives: ['valid_store', 'extend_store'], refs: [SPEC.validStore, SPEC.extendStore],
  },
  // Toolbox ----------------------------------------------------------------------
  {
    id: 'num-progress', label: 'Numerics never mis-type', kind: 'lemma', col: 1, row: 0,
    summary: 'Well-typed operands never hit the “wrong operand” error branch.',
    lemmas: [p('eval_unop_no_runtime_err'), p('eval_binop_no_runtime_err'), p('eval_testop_no_runtime_err'), p('eval_relop_no_runtime_err')],
  },
  {
    id: 'num-preservation', label: 'Numerics keep types', kind: 'lemma', col: 1, row: 1,
    summary: 'An operator on two t’s returns a t.',
    lemmas: [p('eval_unop_preserve_type'), p('eval_binop_preserve_type')],
  },
  {
    id: 'stack-split', label: 'vais_app', kind: 'lemma', col: 1, row: 2,
    summary: 'Cut the typing of xs ++ ys at a middle stack.',
    lemmas: [p('vais_app'), p('vais_app3'), p('vais_weakening')],
  },
  {
    id: 'bt-expand', label: 'vbt_expand', kind: 'lemma', col: 1, row: 3,
    summary: 'Block types expand to function types (multi-value).',
    lemmas: [p('vbt_expand')],
  },
  {
    id: 'bl-vals', label: 'Bl_give_vals', kind: 'lemma', col: 1, row: 4,
    summary: 'A branch out of l labels delivers values of the l-th label’s type.',
    lemmas: [p('Bl_give_vals')],
  },
  {
    id: 'plug-inner', label: 'plug_E_inner', kind: 'lemma', col: 1, row: 5,
    summary: 'If E[e] is typed, e is typed under a context with E’s labels.',
    lemmas: [p('plug_E_inner')],
  },
  {
    id: 'plug-same', label: 'plug_E_same', kind: 'lemma', col: 1, row: 6,
    summary: 'Replacing e by a same-typed e′ inside E keeps the type.',
    lemmas: [p('plug_E_same')],
  },
  {
    id: 'store-weak', label: 'store_weakening', kind: 'lemma', col: 1, row: 7,
    summary: 'Typings survive store extension.',
    lemmas: [p('store_weakening')],
  },
  // Per-rule cases -----------------------------------------------------------------
  {
    id: 'sc-simple', label: 'Simple steps', kind: 'lemma', col: 2, row: 1,
    summary: 'Preservation for every store-free rule, one case per instruction.',
    lemmas: [p('preservation_SC_simple'), p('preservation_SC_simple_VAIS_snoc'), p('preservation_SC_simple_VAI_instr'), p('preservation_SC_simple_VAI_label')],
  },
  {
    id: 'sc-control', label: 'block · loop · if', kind: 'lemma', col: 2, row: 3,
    summary: 'Preservation for the rules that enter a block.',
    lemmas: [p('preservation_SC_block'), p('preservation_SC_loop'), p('preservation_SC_if__nez'), p('preservation_SC_if__eqz')],
  },
  {
    id: 'sc-e', label: 'Step inside E', kind: 'lemma', col: 2, row: 5,
    summary: 'Preservation for a step that happens inside a context.',
    lemmas: [p('preservation', 'SC_E')],
  },
  // Theorems -----------------------------------------------------------------------
  {
    id: 'progress', label: 'Progress', kind: 'theorem', col: 3, row: 1,
    summary: 'A well-typed program is finished or can take a step.',
    lemmas: [p('progress')], refs: [SPEC.soundnessStatement],
  },
  {
    id: 'preservation', label: 'Preservation', kind: 'theorem', col: 3, row: 4,
    summary: 'A step keeps a well-typed program well typed.',
    lemmas: [p('preservation')], refs: [SPEC.soundnessStatement],
  },
  // Top level ----------------------------------------------------------------------
  {
    id: 'toplevel', label: 'Preservation (spec form)', kind: 'theorem', col: 4, row: 4,
    summary: 'The statement exactly as the spec’s appendix phrases it.',
    lemmas: [p('preservation__toplevel')], refs: [SPEC.soundnessStatement],
  },
  {
    id: 'soundness', label: 'Soundness', kind: 'goal', col: 4, row: 2,
    summary: 'Well-typed programs never get stuck. Soundness.v is still empty.',
    refs: [SPEC.soundness],
  },
];

export const EDGES: GraphEdge[] = [
  {
    id: 'seq-induction', from: 'typing', to: 'progress',
    title: 'Induction on sequence typing, from the right',
    gist: 'Progress inducts on the typing of the whole instruction list, peeling off the last instruction each time.',
    body: [
      'The spec types a sequence instr* instr_N by typing the prefix, then typing instr_N against the top of the stack the prefix leaves. The mechanization copies that shape: `VAIS_snoc` types `ainstrs ++ [ainstr__N]`. The natural induction is on this derivation (`dependent induction HVAIS`), and each step of it removes one instruction from the right.',
      'The IH says the prefix is a result (values or a trap) or it steps. If it steps, the whole list steps by congruence (see “Congruence through evaluation contexts”). If it is values, inverting the typing of `ainstr__N` says which instruction is next, and the `Forall2_snoc_app_r` lemmas read its operands off the end of the value list.',
      'In SF the term is a tree and progress goes by induction on `has_type`. Here the term is a list typed as a stack transformer, so the same recipe runs on snoc-lists. That is why most of ProofAux.v is about `snoc` and `unsnoc`.',
    ],
    sf: [SF.typesProgress, SF.inductionOnEvidence, SF.lists],
    spec: [SPEC.validInstrSeq, SPEC.soundnessStatement],
    coq: [p('progress'), p('Forall2_snoc_app_r')],
  },
  {
    id: 'canonical-forms', from: 'num-progress', to: 'progress',
    title: 'Canonical forms for numeric operands',
    gist: 'A well-typed operand is a number of the right width, so evaluation never takes the ill-typed branch.',
    body: [
      'Numerics.v implements each operator as a function returning `runtime_err (option val)`. The error branch is the model’s way of saying the operand had the wrong shape, for example an i64 passed to an i32 operator. The spec never defines that case because validation rules it out.',
      '`eval_unop_no_runtime_err` and its siblings show that when `type_of val = t` for the operator’s type t, the error branch cannot happen. This is the canonical-forms lemma of SF: from a typing fact, recover the shape of a value. Progress uses it to discharge the `Err` case by contradiction.',
      'The `option` layer is different: `None` is a real Wasm trap, such as i32.div_u by zero, and steps to `trap` through `SS_binop__none`.',
    ],
    sf: [SF.typesCanonical, SF.stlcCanonical],
    spec: [SPEC.execNumeric],
    coq: [p('eval_unop_no_runtime_err'), p('eval_binop_no_runtime_err'), p('eval_testop_no_runtime_err'), p('eval_relop_no_runtime_err')],
  },
  {
    id: 'congruence', from: 'evalctx', to: 'progress',
    title: 'Congruence through evaluation contexts',
    gist: 'If a prefix steps, the whole list steps. One rule, SC_E, replaces SF’s family of congruence rules.',
    body: [
      'SF lists congruence rules by hand: `ST_Plus1`, `ST_Plus2`, `ST_If`. The Wasm spec uses evaluation contexts instead, E ::= [_] | val* E instr* | label_n{instr*} E end, with a single rule: if e ↪ e′ then E[e] ↪ E[e′]. The mechanization has exactly this: `eval_context` with `E_hole`, `E_seq` and `E_label`, the function `plug__E`, and the step rule `SC_E`.',
      'In progress, the “prefix steps” case rewrites `ainstrs ++ rest` as `plug__E (E_seq [] E_hole rest) ainstrs` (`decompose_rest_as_E_seq`) and applies `SC_E`. The “values, then a redex” case uses `E_seq vals E_hole []` the same way. Traps travel outward through `SC_trap__E`, again via a context.',
    ],
    sf: [SF.smallstepRelations, SF.smallstepValues],
    spec: [SPEC.evalCtx],
    coq: [p('decompose_vals_as_E_seq'), p('decompose_rest_as_E_seq')],
  },
  {
    id: 'normal-forms', from: 'config', to: 'progress',
    title: 'Values, traps and normal forms',
    gist: 'The “finished” side of progress: a thread holding only values, or a trap, is a result.',
    body: [
      'Progress has SF’s shape “value or steps”, where a value is Wasm’s notion of a result: a list of values, or a trap. Progress.v defines `result_thread` (written ⊢R) for this, built from `R_vals` and `R_trap`.',
      'Preservation.v proves the other direction for the simple cases: `vals_is_normal_form` shows that a list of values cannot step, like SF’s `value_is_nf`. Lifting that to whole configurations (`S_F_vals_is_normal_form`) is still admitted.',
      'A trap can be typed at any stack type (`VAI_trap`), so once a trap appears the typing says nothing about what follows. The trap case of progress propagates it with `SC_trap__E`.',
    ],
    sf: [SF.normalForms, SF.typesProgress],
    spec: [SPEC.validResult, SPEC.result, SPEC.trap],
    coq: [p('F_vals_R'), p('F_Trap_R'), p('vals_is_normal_form')],
  },
  {
    id: 'step-induction', from: 'step', to: 'preservation',
    title: 'Induction on the step, with dependent induction',
    gist: 'Preservation inducts on ↪, whose index is a tuple. Plain induction would forget what the tuple was.',
    body: [
      'The relation `(S, F, ainstrs) ↪ (S′, F′, ainstrs′)` is an inductive predicate indexed by a triple. Coq’s `induction` replaces those indices with fresh variables and drops the equations that tied them to your hypotheses. SF’s section on `remember` explains the failure and the manual fix.',
      'The header of the main theorem records the choice made here: `dependent induction` from Coq.Program.Equality, or LibTactics’ `inductions`, which do the remember-and-invert bookkeeping for you. Each constructor of `step` becomes a case: `SC_simple`, `SC_block`, `SC_loop`, `SC_if__nez`, `SC_if__eqz`, `SC_E`. `SC_trap__E` has no case yet.',
      'Every case except SC_E is handed to its own lemma, so the main theorem reads like a table of contents.',
    ],
    sf: [SF.inductionOnEvidence, SF.rememberTactic, SF.typesPreservation],
    spec: [SPEC.soundnessStatement],
    coq: [p('preservation')],
  },
  {
    id: 'generalize', from: 'preservation', to: 'toplevel',
    title: 'Generalize the statement, then specialize',
    gist: 'The spec states preservation for top-level configurations. That IH is too weak, so the theorem is proved for any context and stack type.',
    body: [
      'The spec’s theorem is about a whole configuration ⊢ (S; T) : rt, with an empty starting stack and no return type. Inside a block, though, instructions run under a context with extra labels and on a non-empty stack. An IH fixed to the top-level shape cannot be applied there.',
      'So `preservation` quantifies over an arbitrary context C and stack type ts1 → ts2, and runs `gen C ts1 ts2` before `dependent induction`. This is the move SF teaches as `generalize dependent` in “Varying the Induction Hypothesis”. The spec-shaped `preservation__toplevel` is then a short corollary: pick `C with_return = None` and ts1 = [].',
      'The comment above the theorem calls the spec’s formulation misleading for exactly this reason. The same lesson comes back in `plug_E_inner`: “it’s important here to generalize C”.',
    ],
    sf: [SF.varyingIH, SF.useTactics],
    spec: [SPEC.soundnessStatement, SPEC.validConfig, SPEC.validThread],
    coq: [p('preservation__toplevel'), p('VA_with_ret_none')],
  },
  {
    id: 'numeric-preservation', from: 'num-preservation', to: 'sc-simple',
    title: 'Operators return values of the operand type',
    gist: 'The numeric half of each simple case: t.binop on two t’s produces a t.',
    body: [
      '`eval_unop_preserve_type` and `eval_binop_preserve_type` go by case analysis on the operator and the operand shapes, like the `T_Succ` and `T_Pred` cases of SF’s Types chapter.',
      'Tests and comparisons need no lemma: their result is always an i32, which `simpl` shows directly. Numerics.v keeps two archived attempts at a general statement (`eval_testop_preserve_type`, `eval_relop_preserve_type`); the comment above them says their conclusions are wrong, so they stay admitted and nothing depends on them.',
    ],
    sf: [SF.typesPreservation],
    spec: [SPEC.execNumeric],
    coq: [p('eval_unop_preserve_type'), p('eval_binop_preserve_type')],
  },
  {
    id: 'stack-split', from: 'stack-split', to: 'sc-simple',
    title: 'Splitting a stack typing at a concatenation',
    gist: 'If xs ++ ys has type ts1 → ts3, some middle stack ts2 types xs : ts1 → ts2 and ys : ts2 → ts3.',
    body: [
      'Every case that rewrites part of a list has to cut the typing derivation at the edit point. `vais_app` cuts in two, `vais_app3` in three (prefix, redex, suffix). The typing is built by snoc, so the proof walks the second list from the right.',
      'The forward direction of `vais_app` is proved; the backward direction is admitted. `vais_weakening` is admitted too: a list typed [] → ts1 is also typed ts0 → ts0 ++ ts1, because the stack below is untouched. This is the frame rule of stack typing. The spec leaves it implicit; in Coq it needs an induction, and the comment notes it relies on choosing the polymorphic type in the empty case.',
      'SF’s nearest material is the stack machine at the end of Smallstep, which runs such lists but never types them.',
    ],
    sf: [SF.stackMachine, SF.lists],
    spec: [SPEC.validInstrSeq],
    coq: [p('vais_app'), p('vais_app3'), p('vais_weakening')],
  },
  {
    id: 'block-contexts', from: 'bl-vals', to: 'sc-simple',
    title: 'Branching out through block contexts',
    gist: 'br l under l nested labels hands the top values to the l-th label. The proof inducts over the block context.',
    body: [
      'The spec names the surroundings of a branch with block contexts: B⁰ ::= val* [_] instr*, and Bᵏ⁺¹ ::= val* label_n{instr*} Bᵏ end instr*. The Coq `block_context` is indexed by k, and `SS_br` reduces label_n{instr*} Bˡ[valⁿ (br l)] end to valⁿ instr*.',
      '`Bl_give_vals` is the typing half: if Bˡ[vals ++ [br l]] is well typed under C, then vals has the result type stored at position l of `C.labels`. It is an induction on B, with `Clabels_cons` tracking how the label list shifts under each label. `preservation_SC_simple_VAI_label` then uses it for `SS_br` and `SS_block__exit`.',
      'STLC has no labels, so SF has no direct counterpart. The closest idea is the induction over contexts in StlcProp’s weakening lemma.',
    ],
    sf: [SF.stlcWeakening],
    spec: [SPEC.blockCtx, specExec('br', 'br'), SPEC.label],
    coq: [p('Bl_give_vals'), p('preservation_SC_simple_VAI_label'), p('Clabels_cons')],
  },
  {
    id: 'label-typing', from: 'bt-expand', to: 'sc-control',
    title: 'Entering a block pushes a label onto the context',
    gist: 'block, loop and if step to a label; typing it means typing the body under C with one more label.',
    body: [
      '`SC_block` rewrites vals (block bt instrs) to label_n{[]} (vals ++ instrs) end. `VAI_label` types that: the continuation has type ts1 → ts2, and the body has type [] → ts2 under (C, labels ts1). Loop differs only in the continuation, which is the loop itself, so its label arity is the input arity m.',
      'First the block type has to become a function type. With multi-value, a block type is a type index or an optional value type, and `vbt_expand` relates `valid_blocktype` to the runtime `expand F bt` case by case (`VBT_typeidx`, `VBT_valtype__some`, `VBT_valtype__none`).',
      'Pushing a label is the control-flow analogue of extending Γ with x:T in STLC’s `T_Abs` case.',
    ],
    sf: [SF.stlcWeakening, SF.typesPreservation],
    spec: [specExec('block', 'block'), SPEC.label, SPEC.validAdmin, WEB.multiValue],
    coq: [p('vbt_expand'), p('preservation_SC_block'), p('preservation_SC_loop'), p('preservation_SC_if__nez'), p('preservation_SC_if__eqz')],
  },
  {
    id: 'store-extension', from: 'store', to: 'preservation',
    title: 'Store typing and store extension',
    gist: 'A step may grow the store, so preservation also returns ⊢ S ⪯ S′ to keep earlier typings valid.',
    body: [
      'Like PLF’s References chapter, Wasm has a mutable store, and preservation must say it stays well typed. SF uses a store typing ST and `extends ST′ ST`. The Wasm spec validates the store directly (⊢ S ok) and defines an extension relation ⊢ S ⪯ S′. The notes in Preservation.v observe that the two set-ups do the same job.',
      'The conclusion of `preservation` is therefore ⊢ S ⪯ S′ ∧ ⊢ S′ ok ∧ …. None of the instructions modeled so far write to the store, so every case closes with `extend_store_refl`.',
    ],
    sf: [SF.refStoreTypings, SF.refExtending, SF.refWellTypedStores],
    spec: [SPEC.extendStore, SPEC.validStore],
    coq: [p('extend_store_refl')],
  },
  {
    id: 'store-weakening', from: 'store', to: 'store-weak',
    title: 'Weakening: typings survive store extension',
    gist: 'If S ⪯ S′, whatever was typed under S is typed under S′. Needed once instructions start writing memory, tables and globals.',
    body: [
      '`store_weakening` mirrors SF’s weakening for stores: extending the store preserves the typing of module instances, function instances and tables. It is Qed, but rests on three admitted per-component lemmas.',
      'It is not on the critical path yet, because no modeled instruction writes to the store. It becomes essential with global.set, memory.grow and the table instructions.',
    ],
    sf: [SF.refWeakeningStores],
    spec: [SPEC.extendStore],
    coq: [p('store_weakening'), p('store_weakening_preserve_type_moduleinst'), p('store_weakening_preserve_type_tableinst')],
  },
  {
    id: 'context-decomposition', from: 'plug-inner', to: 'sc-e',
    title: 'Decomposing the typing of E[e]',
    gist: 'If E[e] is typed under C, then e is typed under some C′ that adds the labels E passes through.',
    body: [
      '`plug_E_inner` is an induction on the context E. `E_seq` cuts the typing into three with `vais_app3`. `E_label` inverts `VAI_label`, which moves the body under (C, labels ts). So the inner context C′ is C plus one label per `E_label` layer, recorded as `extend_context` (⊢C C ⪯ C′).',
      'It is Qed, modulo the stack-splitting lemmas. The proof comment carries the key lesson: generalize C before inducting on E, or the `E_label` case gets an IH about the wrong context.',
    ],
    sf: [SF.varyingIH, SF.stlcContextInvariance],
    spec: [SPEC.evalCtx],
    coq: [p('plug_E_inner'), p('extend_context_cons')],
  },
  {
    id: 'replacement', from: 'plug-same', to: 'sc-e',
    title: 'Replacement: swapping e for e′ inside E',
    gist: 'The open core of preservation: if e and e′ have the same type, E[e′] has E[e]’s type. Stated, not yet proved.',
    body: [
      'This is the replacement lemma of the Wright–Felleisen method. For STLC it is routine because typing is syntax-directed and types are unique. Wasm instruction typing is neither. `unreachable`, `br` and `trap` can take any stack type, and a list typed ts1 → ts2 can also be typed ts0 ++ ts1 → ts0 ++ ts2. So the type of e inside E is not determined by the type of E[e].',
      '`plug_E_same` states the lemma with C ⪯ C′ and one hole type ts3 → ts4 shared by e and e′; all three cases are `admit`. `plug_E_strong_same` also lets the store change; its `E_seq` case is under way. Proving either closes `SC_E`, and with it preservation for the whole modeled subset.',
      'StlcProp proves Uniqueness of Types, the very property Wasm lacks, which makes it a useful contrast. One promising route is to preserve the hole type that `plug_E_inner` produced, instead of an arbitrary one.',
    ],
    sf: [SF.stlcUniqueness, SF.stlcContextInvariance],
    spec: [SPEC.evalCtx, SPEC.soundness],
    coq: [p('plug_E_same'), p('plug_E_strong_same')],
  },
  {
    id: 'sc-e', from: 'sc-e', to: 'preservation',
    title: 'The SC_E case: a step inside a context',
    gist: 'The only admitted case of the main preservation theorem. Almost every real step goes through it.',
    body: [
      'Most steps happen inside a context: `vals ++ [i32.add] ++ rest` reduces through `E_seq`, and anything inside a block through `E_label`. Until SC_E is closed, the per-rule lemmas are proved but cannot yet be composed into preservation for whole programs.',
      'The plan, sketched in the comments of `preservation_SC_E` (an aborted draft): decompose E[e] with `plug_E_inner`, apply the IH to e ↪ e′ under C′, then put e′ back with the replacement lemma.',
    ],
    sf: [SF.typesPreservation],
    spec: [SPEC.evalCtx],
    coq: [p('preservation', 'SC_E')],
  },
  {
    id: 'rule-cases', from: 'sc-simple', to: 'preservation',
    title: 'Simple steps: one case per reduction rule',
    gist: 'Steps that touch neither store nor frame (↪s) get one case per instruction, all Qed.',
    body: [
      '`SC_simple` lifts the store-free relation ↪s. `preservation_SC_simple` inducts on the sequence typing (`VAIS_snoc` again), and `preservation_SC_simple_VAI_instr` inverts the typing of the reducing instruction, with one bullet per rule: unop, binop, testop, relop, drop, select, nop, unreachable, br_if, br_table. `preservation_SC_simple_VAI_label` covers the rules that remove a label (`SS_block__exit`, `SS_br`).',
      'Each case has the same rhythm: `inverts` the typing of the operands, rebuild the typing of the result with `econstructor` or `eauto`, and use `vais_vals` to type a list of values.',
    ],
    sf: [SF.typesPreservation, SF.useTactics, SF.invertingEvidence],
    spec: [SPEC.execInstr],
    coq: [p('preservation', 'SC_simple'), p('preservation_SC_simple_VAI_instr')],
  },
  {
    id: 'control-cases', from: 'sc-control', to: 'preservation',
    title: 'Control steps: block, loop, if',
    gist: 'Rules that read the frame to expand a block type are separate step constructors, each with its own lemma.',
    body: [
      '`SC_block`, `SC_loop`, `SC_if__nez` and `SC_if__eqz` need the frame F to expand the block type, so they live in the full `step` relation, not in ↪s. Each has a dedicated lemma that combines `vbt_expand`, the label typing rule and `vais_app`.',
    ],
    sf: [SF.typesPreservation],
    spec: [specExec('block', 'block'), specExec('loop', 'loop'), specExec('if', 'if')],
    coq: [p('preservation', 'SC_block'), p('preservation', 'SC_loop'), p('preservation', 'SC_if__nez'), p('preservation', 'SC_if2')],
  },
  {
    id: 'soundness-progress', from: 'progress', to: 'soundness',
    title: 'Soundness = progress + preservation, iterated',
    gist: 'Not stated yet: Soundness.v is an empty file.',
    body: [
      'The spec’s soundness theorem says a valid configuration either diverges or reduces to a result of the right type. With progress and the top-level preservation corollary, the SF argument (Types § Type Soundness) is an induction on the multi-step relation, which Execution.v already defines as `multi`.',
      'SF phrases soundness as “never stuck”: any normal form reached by multi-step is a value. That avoids having to talk about infinite runs in Coq.',
    ],
    sf: [SF.typesSoundness, SF.multiStep],
    spec: [SPEC.soundnessStatement],
    coq: [],
    status: 'missing',
  },
  {
    id: 'soundness-preservation', from: 'toplevel', to: 'soundness',
    title: 'Preservation feeds the soundness induction',
    gist: 'Each step of a multi-step run keeps the configuration typed, so progress applies again.',
    body: [
      'In the multi-step induction, `preservation__toplevel` re-establishes ⊢ (S′; T′) : rt after every step, which is exactly what progress needs as input for the next one.',
    ],
    sf: [SF.typesSoundness, SF.multiStep],
    spec: [SPEC.soundnessStatement],
    coq: [],
    status: 'missing',
  },
];

export const nodeById = Object.fromEntries(NODES.map((n) => [n.id, n]));
export const edgeById = Object.fromEntries(EDGES.map((e) => [e.id, e]));

export function nodeStatus(n: GraphNode): Status {
  if (n.kind === 'goal') return 'missing';
  if (n.kind === 'definition') return 'na';
  return pointsStatus(n.lemmas ?? []);
}

export function edgeStatus(e: GraphEdge): Status {
  return e.status ?? pointsStatus(e.coq);
}
