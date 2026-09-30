import { CoverageMatrix } from '../components/CoverageMatrix';
import { Frontier } from '../components/Frontier';
import { Ledger } from '../components/Ledger';
import { Pipeline } from '../components/Pipeline';
import { RefLink } from '../components/Refs';
import { StatusLegend } from '../components/Status';
import { Theorems } from '../components/Theorems';
import { SPEC, SPEC_LABEL } from '../data/refs';
import { edgeHash } from '../lib/route';
import css from './views.module.css';

export function OverviewView() {
  return (
    <>
      <header className={css.hero}>
        <p className="eyebrow">A Coq mechanization of the WebAssembly specification</p>
        <h1>Does passing the Wasm type checker guarantee a program never gets stuck?</h1>
        <p className={css.lead}>
          Every Wasm engine validates a module before it runs it. The spec claims that check is enough: a validated program can
          always take its next step, and every step keeps it well typed. This property is called <em>type soundness</em>. WasmCert
          is a machine-checked proof of it, written in Coq against the spec’s own definitions, rule by rule. It is not finished,
          and this page shows exactly how far it has got.
        </p>
      </header>

      <section className={css.section} aria-labelledby="h-thm">
        <div className={css.sectionHead}>
          <h2 id="h-thm">Two theorems make up soundness</h2>
          <p>
            The spec’s appendix states soundness as two rules. Read the bar as “if everything above holds, the thing below holds”.
          </p>
        </div>
        <Theorems />
        <Ledger />
      </section>

      <section className={css.section} aria-labelledby="h-pipe">
        <div className={css.sectionHead}>
          <h2 id="h-pipe">From spec to proof</h2>
          <p>
            The Coq files follow the chapters of the {SPEC_LABEL}. The first three stages transcribe the spec; the fourth is new
            work that the spec only sketches in its appendix.
          </p>
        </div>
        <Pipeline />
      </section>

      <section className={css.section} aria-labelledby="h-cov">
        <div className={css.sectionHead}>
          <h2 id="h-cov">Instruction by instruction</h2>
          <p>
            Squares show what is written down in Coq; circles show what is proved about it. Open a row to see the exact rules and
            lemmas, each linked to its line in the source.
          </p>
        </div>
        <div className={css.legendRow}>
          <StatusLegend />
          <ul className={css.modelLegend} aria-label="Definition legend">
            <li>
              <span data-s="modeled" /> modeled
            </li>
            <li>
              <span data-s="partial" /> partly modeled
            </li>
            <li>
              <span data-s="absent" /> not yet
            </li>
          </ul>
        </div>
        <p className={css.note}>
          Preservation cells show each rule’s own case. Combining those cases inside a larger program goes through one more
          case, a step inside an evaluation context, which is still open. <a href={edgeHash('sc-e')}>Why that case is hard →</a>
        </p>
        <CoverageMatrix />
      </section>

      <section className={css.section} aria-labelledby="h-front">
        <div className={css.sectionHead}>
          <h2 id="h-front">What is left</h2>
          <p>Read straight from the proof scripts on every build, so this list shrinks as proofs land.</p>
        </div>
        <Frontier />
      </section>

      <aside className={css.deeper}>
        <div>
          <p className="eyebrow">Next level</p>
          <h2>How the proof actually goes</h2>
          <p>
            The proof edges view lays the argument out as a graph: definitions on the left, theorems on the right, and one edge per
            proof technique. Each edge is written for readers who have worked through <em>Software Foundations</em> (Logical
            Foundations and Programming Language Foundations) and links the chapter that teaches the same move.
          </p>
        </div>
        <div className={css.deeperLinks}>
          <a className={css.button} href="#edges">
            Open the proof edges
          </a>
          <RefLink r={SPEC.soundness} />
        </div>
      </aside>
    </>
  );
}
