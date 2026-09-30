# WasmCert proof atlas

A small site that shows **what** the Coq development proves, **how far** it has
got, and **how** the proof is put together. It has two levels:

| View | Reader | Links to |
| --- | --- | --- |
| **Overview** (`#overview`) | Programmers who know Wasm, not proofs | The Wasm 1.0 spec |
| **Proof edges** (`#edges`) | Readers of *Software Foundations* (LF + PLF) | SF chapters/sections, the spec, exact Coq lines |

```sh
cd site
npm install
npm run dev      # extracts ../coq, then starts Vite
npm run build    # extract + typecheck + static build into dist/
npm test         # unit tests for the Coq extractor
npm run check-refs  # (network) verify every spec anchor exists
```

## How it fits together

```
coq/*.v ──scripts/extract-coq.mjs──▶ src/generated/coq-index.json   (generated, git-ignored)
                                              │
src/data/  curated content, joined with the index:
  refs.ts          one registry for every spec / SF / paper link
  coq.ts           typed index + status arithmetic (proved / modulo / open / missing)
  pipeline.ts      Structure → Validation → Execution → Soundness
  instructions.ts  instruction rows → Coq constructors and proof cases
  graph.ts         proof graph: nodes (lemmas) and edges (proof moves, SF-level text)
                                              │
src/components/  one component per visual: Theorems, Ledger, Pipeline,
                 CoverageMatrix, Frontier, ProofGraph, Detail, Toolbelt, …
src/views/       OverviewView, EdgesView (hash-routed in App.tsx)
```

**Nothing about progress is hand-written.** The extractor reads each proof and
records how it ends (`Qed`, `Admitted`, `Abort`), the `admit`s inside it, each
labelled bullet case (`- (* VI_block *)`) and whether that case is closed, and
which other lemmas it mentions. A `Qed` proof that transitively uses an admitted
lemma is reported as *relies on admits*. So when a proof lands, the next build
updates the matrix, the graph and the "what is left" list by itself.

The curated files only say *what maps to what*. Typical edits:

- **An instruction gets modeled/proved**: nothing to do, or add its proof
  points to its row in `instructions.ts` if the case label is new.
- **A new lemma matters for the story**: add a node to `graph.ts` with a
  `(col, row)` slot; the layout is computed from that.
- **Explain a proof move**: add an edge to `graph.ts` with `gist`, `body`,
  `sf` and `spec` references (use the registries in `refs.ts`).

Case labels come from the comment right after a bullet, so keeping the
`- (* Constructor *)` convention in proofs keeps the site precise.
