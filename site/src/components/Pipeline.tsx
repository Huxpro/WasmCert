import { sourceHref } from '../data/coq';
import { STAGES, stageStats } from '../data/pipeline';
import { RefLink } from './Refs';
import css from './Pipeline.module.css';

/** Structure → Validation → Execution → Soundness, each with the Coq files that implement it. */
export function Pipeline() {
  return (
    <ol className={css.pipeline}>
      {STAGES.map((s, i) => {
        const st = stageStats(s);
        const lemmas = st.proved + st.partial + st.stated;
        return (
          <li key={s.id} className={css.stage}>
            <div className={css.top}>
              <span className="eyebrow">
                {i + 1} · {s.name}
              </span>
              <h3 className={css.question}>{s.question}</h3>
              <p className={css.blurb}>{s.blurb}</p>
            </div>
            <dl className={css.facts}>
              {st.measures.map((m) => (
                <div key={m.inductive}>
                  <dt>{m.label}</dt>
                  <dd className="num">{m.count}</dd>
                </div>
              ))}
              <div>
                <dt>lines of Coq</dt>
                <dd className="num">{st.lines.toLocaleString('en-US')}</dd>
              </div>
              {lemmas > 0 && (
                <div>
                  <dt>lemmas Qed</dt>
                  <dd className="num">
                    {st.proved}
                    <span className={css.of}>/{lemmas}</span>
                  </dd>
                </div>
              )}
            </dl>
            <ul className={css.files}>
              {st.files.map((f) => (
                <li key={f.file}>
                  <a href={sourceHref(f.file)} target="_blank" rel="noreferrer">
                    <code>{f.file}</code>
                  </a>
                  <FileBar f={f} />
                </li>
              ))}
            </ul>
            <RefLink r={s.spec} />
          </li>
        );
      })}
    </ol>
  );
}

function FileBar({ f }: { f: { proved: number; partial: number; stated: number } }) {
  const n = f.proved + f.partial + f.stated;
  if (!n) return <span className={css.nolemmas}>definitions</span>;
  return (
    <span className={css.fbar} title={`${f.proved} Qed · ${f.partial} partial · ${f.stated} statement only`}>
      <span data-k="proved" style={{ flexGrow: f.proved }} />
      <span data-k="partial" style={{ flexGrow: f.partial }} />
      <span data-k="stated" style={{ flexGrow: f.stated }} />
    </span>
  );
}
