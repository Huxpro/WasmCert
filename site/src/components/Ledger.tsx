import { totals } from '../data/coq';
import css from './Ledger.module.css';

/** Every lemma in the project, as one proportional bar. */
export function Ledger() {
  const t = totals();
  const segs = [
    { key: 'closed', n: t.closed, label: 'Qed, fully closed' },
    { key: 'modulo', n: t.proved - t.closed, label: 'Qed, relies on an admit' },
    { key: 'partial', n: t.partial, label: 'Admitted, partly proved' },
    { key: 'stated', n: t.stated, label: 'Statement only' },
    { key: 'aborted', n: t.aborted, label: 'Aborted drafts' },
  ];
  return (
    <figure className={css.ledger}>
      <figcaption>
        <span className="eyebrow">Lemma ledger</span>
        <span className={css.total}>
          <b className="num">{t.all}</b> lemmas across the project, <b className="num">{t.admits}</b> <code>admit</code>s left in
          unfinished proofs
        </span>
      </figcaption>
      <div className={css.bar}>
        {segs.map((s) => (
          <span key={s.key} data-k={s.key} style={{ flexGrow: s.n }} title={`${s.label}: ${s.n}`} />
        ))}
      </div>
      <ul className={css.keys}>
        {segs.map((s) => (
          <li key={s.key}>
            <span className={css.swatch} data-k={s.key} />
            <b className="num">{s.n}</b> {s.label}
          </li>
        ))}
      </ul>
    </figure>
  );
}
