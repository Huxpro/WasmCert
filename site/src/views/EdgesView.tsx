import { SelectionDetail } from '../components/Detail';
import { ProofGraph, type Selection } from '../components/ProofGraph';
import { StatusLegend } from '../components/Status';
import { Toolbelt } from '../components/Toolbelt';
import { EDGES, edgeStatus, nodeById } from '../data/graph';
import { StatusMark } from '../components/Status';
import { edgeHash } from '../lib/route';
import css from './views.module.css';

// With nothing selected, open on the edge that decides whether preservation closes.
const DEFAULT: Selection = { type: 'edge', id: 'replacement' };

export function EdgesView({ select }: { select?: Selection }) {
  const selection = select ?? DEFAULT;
  const targets = [...new Set(EDGES.map((e) => e.to))];
  return (
    <>
      <header className={css.hero}>
        <p className="eyebrow">Proof edges · assumes Software Foundations, LF and PLF</p>
        <h1>How the soundness proof is put together</h1>
        <p className={css.lead}>
          Nodes are the definitions and lemmas that carry weight. Each edge is one proof move: why a lemma is needed, how it is
          proved, and which chapter of <em>Software Foundations</em> teaches the same move. Where Wasm departs from the textbook
          (stack typing, labels, typing that is not unique), the edge says so. Select any node or edge.
        </p>
        <StatusLegend />
      </header>

      <section className={css.graphSection} aria-label="Proof graph">
        <ProofGraph selection={selection} />
      </section>

      <div className={css.split}>
        <div className={css.detailPane} key={`${selection.type}-${selection.id}`}>
          <SelectionDetail {...selection} />
        </div>
        <aside className={css.sidePane}>
          <section>
            <h2 className={css.sideTitle}>All edges</h2>
            {targets.map((t) => (
              <div key={t} className={css.edgeGroup}>
                <p className="eyebrow">into {nodeById[t].label}</p>
                <ul>
                  {EDGES.filter((e) => e.to === t).map((e) => (
                    <li key={e.id} data-current={selection.type === 'edge' && selection.id === e.id ? true : undefined}>
                      <StatusMark status={edgeStatus(e)} size={9} />
                      <a href={edgeHash(e.id)}>{e.title}</a>
                    </li>
                  ))}
                </ul>
              </div>
            ))}
          </section>
          <section>
            <h2 className={css.sideTitle}>Tactic toolbelt</h2>
            <p className={css.sideNote}>
              The proofs are written with LibTactics, the library PLF introduces in UseTactics. Each tactic links to where SF
              teaches it.
            </p>
            <Toolbelt />
          </section>
        </aside>
      </div>
    </>
  );
}
