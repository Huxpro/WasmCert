import css from './Judgment.module.css';

/**
 * An inference rule, drawn the way the spec and SF draw them:
 * premises over a bar, conclusion under it, the rule name to the right.
 */
export function Judgment({ premises, conclusion, name }: { premises: React.ReactNode[]; conclusion: React.ReactNode; name?: string }) {
  return (
    <figure className={css.rule}>
      <div className={css.body}>
        <div className={css.premises}>
          {premises.map((p, i) => (
            <span key={i}>{p}</span>
          ))}
        </div>
        <div className={css.bar} />
        <div className={css.conclusion}>{conclusion}</div>
      </div>
      {name && <figcaption className={css.name}>{name}</figcaption>}
    </figure>
  );
}
