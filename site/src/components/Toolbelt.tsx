import { coq } from '../data/coq';
import { SF, sfHref, type SfRef } from '../data/refs';
import css from './Toolbelt.module.css';

const ROWS: { tactic: string; what: string; sf: SfRef }[] = [
  { tactic: 'inverts', what: 'inversion that names and substitutes', sf: SF.useTactics },
  { tactic: 'introv', what: 'intro only the hypotheses', sf: SF.useTactics },
  { tactic: 'eapply', what: 'apply, leaving evars', sf: SF.useAuto },
  { tactic: 'eauto', what: 'search with constructor hints', sf: SF.useAuto },
  { tactic: 'induction', what: 'structural induction', sf: SF.inductionOnEvidence },
  { tactic: 'remember', what: 'keep an index before inducting', sf: SF.rememberTactic },
  { tactic: 'asserts_rewrite', what: 'assert an equation, rewrite with it', sf: SF.useTactics },
  { tactic: 'splits', what: 'split an n-ary conjunction', sf: SF.useTactics },
  { tactic: 'gen', what: 'generalize dependent, n at a time', sf: SF.varyingIH },
  { tactic: 'dependent induction', what: 'induction on an indexed relation', sf: SF.rememberTactic },
];

/** The tactic vocabulary of the proofs, counted from the source. */
export function Toolbelt() {
  const max = Math.max(...ROWS.map((r) => coq.tactics[r.tactic] ?? 0));
  return (
    <table className={css.table}>
      <caption>Uses across the project</caption>
      <tbody>
        {ROWS.map((r) => {
          const n = coq.tactics[r.tactic] ?? 0;
          return (
            <tr key={r.tactic}>
              <th scope="row">
                <a href={sfHref(r.sf)} target="_blank" rel="noreferrer">
                  <code>{r.tactic}</code>
                </a>
                <span className={css.what}>{r.what}</span>
              </th>
              <td className={css.barCell}>
                <span className={css.bar} style={{ width: `${(100 * n) / max}%` }} />
              </td>
              <td className="num">{n}</td>
            </tr>
          );
        })}
      </tbody>
    </table>
  );
}
