import { caseTally, inductive, lemma, pointStatus, sourceHref } from '../data/coq';
import { SPEC } from '../data/refs';
import { edgeHash } from '../lib/route';
import { Judgment } from './Judgment';
import { RefLink } from './Refs';
import { StatusPill } from './Status';
import css from './Theorems.module.css';

const V = ({ children }: { children: React.ReactNode }) => <i>{children}</i>;

/** The two halves of type soundness, stated as rules, with live progress. */
export function Theorems() {
  const prog = caseTally('progress', /^(VI_|VAI_trap$|VAIS_empty$|VAIS_label$)/);
  const stepRules = inductive('step')?.constructors.length ?? 0;
  const pres = caseTally('preservation', /^SC_/);
  const presTop = pres.cases.filter((c) => c.level === 0);

  const cards = [
    {
      id: 'progress',
      name: 'Progress',
      rule: (
        <Judgment
          name="Progress"
          premises={[<>⊢ (<V>S</V>; <V>T</V>) : <V>rt</V></>]}
          conclusion={<><V>T</V> is a result &ensp;∨&ensp; (<V>S</V>; <V>T</V>) ↪ (<V>S′</V>; <V>T′</V>)</>}
        />
      ),
      plain:
        'A program that passed the type checker is never stuck. Either it has finished, with values or a trap, or there is a rule that lets it take another step.',
      done: prog.closed,
      total: prog.total,
      unit: 'instruction cases',
      edge: 'seq-induction',
    },
    {
      id: 'preservation',
      name: 'Preservation',
      rule: (
        <Judgment
          name="Preservation"
          premises={[<>⊢ (<V>S</V>; <V>T</V>) : <V>rt</V></>, <>(<V>S</V>; <V>T</V>) ↪ (<V>S′</V>; <V>T′</V>)</>]}
          conclusion={<>⊢ (<V>S′</V>; <V>T′</V>) : <V>rt</V></>}
        />
      ),
      plain:
        'Taking a step never breaks the typing. So the promise the type checker made before the program started still holds after every step.',
      done: presTop.filter((c) => c.status === 'closed').length,
      total: stepRules,
      unit: 'reduction rules',
      edge: 'replacement',
    },
  ];

  return (
    <div className={css.grid}>
      {cards.map((c) => {
        const l = lemma(c.id)!;
        return (
          <article key={c.id} className={css.card}>
            <div className={css.head}>
              <h3>{c.name}</h3>
              <StatusPill status={pointStatus({ lemma: c.id })} />
            </div>
            <div className={css.rule}>{c.rule}</div>
            <p className={css.plain}>{c.plain}</p>
            <div className={css.meter} role="img" aria-label={`${c.done} of ${c.total} ${c.unit} proved`}>
              <div className={css.track}>
                <div className={css.fill} style={{ width: `${(100 * c.done) / Math.max(1, c.total)}%` }} />
              </div>
              <span className="num">
                <b>{c.done}</b> of {c.total} {c.unit} proved
              </span>
            </div>
            <div className={css.links}>
              <RefLink r={SPEC.soundnessStatement} />
              <a href={sourceHref(l.file, l.line, l.endLine)} target="_blank" rel="noreferrer" className={css.src}>
                <code>{c.id}</code> in {l.file}
              </a>
              <a href={edgeHash(c.edge)} className={css.deeper}>
                How it is proved →
              </a>
            </div>
          </article>
        );
      })}
    </div>
  );
}
