import { inductive, lemma, LEMMA_STATUS_LABEL, sourceHref } from '../data/coq';
import { EDGES, edgeById, edgeStatus, nodeById, nodeStatus, type GraphEdge, type GraphNode } from '../data/graph';
import { edgeHash, nodeHash } from '../lib/route';
import { CoqPoint, Prose, RefList } from './Refs';
import { StatusPill } from './Status';
import css from './Detail.module.css';

export function EdgeDetail({ e }: { e: GraphEdge }) {
  const from = nodeById[e.from];
  const to = nodeById[e.to];
  return (
    <article className={css.panel} aria-labelledby={`t-${e.id}`}>
      <div className={css.route}>
        <a href={nodeHash(from.id)}>{from.label}</a>
        <span aria-hidden="true">→</span>
        <a href={nodeHash(to.id)}>{to.label}</a>
      </div>
      <h2 id={`t-${e.id}`}>{e.title}</h2>
      <StatusPill status={edgeStatus(e)} />
      <p className={css.gist}>{e.gist}</p>
      <div className={css.body}>
        {e.body.map((t, i) => (
          <p key={i}>
            <Prose text={t} />
          </p>
        ))}
      </div>
      {e.sf.length > 0 && (
        <section>
          <h3 className="eyebrow">Learn the move in Software Foundations</h3>
          <RefList refs={e.sf} />
        </section>
      )}
      {e.spec.length > 0 && (
        <section>
          <h3 className="eyebrow">In the spec</h3>
          <RefList refs={e.spec} />
        </section>
      )}
      {e.coq.length > 0 && (
        <section>
          <h3 className="eyebrow">In the Coq source</h3>
          <ul className={css.points}>
            {e.coq.map((p) => (
              <li key={p.lemma + p.case}>
                <CoqPoint p={p} />
                <Blockers name={p.lemma} />
              </li>
            ))}
          </ul>
        </section>
      )}
    </article>
  );
}

function Blockers({ name }: { name: string }) {
  const b = lemma(name)?.blockedBy;
  if (!b?.length) return null;
  return (
    <p className={css.blockers}>
      relies on admitted <Prose text={b.map((x) => `\`${x}\``).join(', ')} />
    </p>
  );
}

export function NodeDetail({ n }: { n: GraphNode }) {
  const incoming = EDGES.filter((e) => e.to === n.id);
  const outgoing = EDGES.filter((e) => e.from === n.id);
  return (
    <article className={css.panel} aria-labelledby={`t-${n.id}`}>
      <div className={css.route}>
        <span className="eyebrow">{n.kind === 'goal' ? 'goal' : n.kind}</span>
      </div>
      <h2 id={`t-${n.id}`}>{n.label}</h2>
      {n.kind !== 'definition' && <StatusPill status={nodeStatus(n)} />}
      <p className={css.gist}>{n.summary}</p>

      {n.inductives && (
        <section>
          <h3 className="eyebrow">Definitions</h3>
          <ul className={css.points}>
            {n.inductives.map((name) => {
              const ind = inductive(name);
              return (
                <li key={name}>
                  {ind ? (
                    <a href={sourceHref(ind.file, ind.line)} target="_blank" rel="noreferrer" className={css.def}>
                      <code>{name}</code> <span>{ind.constructors.length} rules · {ind.file}</span>
                    </a>
                  ) : (
                    <code>{name}</code>
                  )}
                </li>
              );
            })}
          </ul>
        </section>
      )}

      {n.lemmas && (
        <section>
          <h3 className="eyebrow">Lemmas</h3>
          <ul className={css.points}>
            {n.lemmas.map((p) => {
              const l = lemma(p.lemma);
              return (
                <li key={p.lemma + p.case}>
                  <CoqPoint p={p} />
                  {l && !p.case && <span className={css.how}>{LEMMA_STATUS_LABEL[l.status]}</span>}
                  <Blockers name={p.lemma} />
                </li>
              );
            })}
          </ul>
        </section>
      )}

      {n.refs && n.refs.length > 0 && (
        <section>
          <h3 className="eyebrow">In the spec</h3>
          <RefList refs={n.refs} />
        </section>
      )}

      {[
        ['Built from', incoming],
        ['Used by', outgoing],
      ].map(([label, list]) =>
        (list as GraphEdge[]).length ? (
          <section key={label as string}>
            <h3 className="eyebrow">{label as string}</h3>
            <ul className={css.edges}>
              {(list as GraphEdge[]).map((e) => (
                <li key={e.id}>
                  <a href={edgeHash(e.id)}>{e.title}</a>
                </li>
              ))}
            </ul>
          </section>
        ) : null,
      )}
    </article>
  );
}

export function SelectionDetail({ type, id }: { type: 'edge' | 'node'; id: string }) {
  if (type === 'edge' && edgeById[id]) return <EdgeDetail e={edgeById[id]} />;
  if (type === 'node' && nodeById[id]) return <NodeDetail n={nodeById[id]} />;
  return <p>Nothing called “{id}” in the graph.</p>;
}
