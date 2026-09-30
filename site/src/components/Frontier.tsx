import { caseTally, lemma, sourceHref } from '../data/coq';
import { EDGES, edgeStatus } from '../data/graph';
import { edgeHash } from '../lib/route';
import { StatusMark } from './Status';
import css from './Frontier.module.css';

/** What is still open, derived from the source: nothing here is hand-maintained. */
export function Frontier() {
  const progressOpen = caseTally('progress', /^(VI_|VAI_trap$|VAIS_empty$|VAIS_label$)/).cases.filter((c) => c.status === 'open');
  const edges = EDGES.filter((e) => ['open', 'missing'].includes(edgeStatus(e)));
  const prog = lemma('progress')!;
  return (
    <div className={css.grid}>
      <section className={css.col}>
        <h3>Progress: open cases</h3>
        <p className={css.lead}>Each is an <code>admit</code> inside the progress proof. Most are control flow, where a step needs the label typing that preservation already handles.</p>
        <ul className={css.chips}>
          {progressOpen.map((c) => (
            <li key={c.line}>
              <a href={sourceHref(prog.file, c.line)} target="_blank" rel="noreferrer">
                <StatusMark status="open" size={8} />
                <code>{c.label}</code>
              </a>
            </li>
          ))}
        </ul>
      </section>
      <section className={css.col}>
        <h3>Proof steps still open</h3>
        <ul className={css.edges}>
          {edges.map((e) => (
            <li key={e.id}>
              <StatusMark status={edgeStatus(e)} size={10} />
              <div>
                <a href={edgeHash(e.id)}>{e.title}</a>
                <p>{e.gist}</p>
              </div>
            </li>
          ))}
        </ul>
      </section>
    </div>
  );
}
