import { Fragment, useState } from 'react';
import { constructorSite, sourceHref, STATUS_LABEL, type Status } from '../data/coq';
import { GROUPS, INSTRUCTIONS, rowStatus, type InstructionRow, type ModelStatus } from '../data/instructions';
import { edgeById } from '../data/graph';
import { edgeHash } from '../lib/route';
import { CoqPoint, RefLink } from './Refs';
import { StatusMark } from './Status';
import css from './CoverageMatrix.module.css';

const MODEL_LABEL: Record<ModelStatus | 'value', string> = {
  modeled: 'Modeled in Coq',
  partial: 'Partly modeled',
  absent: 'Not modeled yet',
  value: 'A value: never steps',
};

function ModelMark({ s }: { s: ModelStatus | 'value' }) {
  return <span className={css.model} data-s={s} title={MODEL_LABEL[s]} aria-label={MODEL_LABEL[s]} />;
}

function ProofCell({ s }: { s: Status }) {
  return (
    <span title={STATUS_LABEL[s]} aria-label={STATUS_LABEL[s]}>
      <StatusMark status={s} size={13} />
    </span>
  );
}

/** Instruction × stage. Definitions are squares, proofs are circles. */
export function CoverageMatrix() {
  const [open, setOpen] = useState<string | null>('block');
  return (
    <div className={css.wrap}>
      <table className={css.table}>
        <thead>
          <tr>
            <th scope="col" className={css.first}>Instruction</th>
            <th scope="col">Structure</th>
            <th scope="col">Validation</th>
            <th scope="col">Execution</th>
            <th scope="col" className={css.proofCol}>Progress</th>
            <th scope="col">Preservation</th>
          </tr>
        </thead>
        <tbody>
          {GROUPS.map((g) => (
            <Fragment key={g}>
              <tr className={css.group}>
                <th colSpan={6} scope="colgroup">
                  {g}
                  {g === 'Administrative' && <span className={css.groupNote}>exist only while a program runs</span>}
                </th>
              </tr>
              {INSTRUCTIONS.filter((r) => r.group === g).map((r) => {
                const st = rowStatus(r);
                const isOpen = open === r.id;
                return (
                  <Fragment key={r.id}>
                    <tr className={css.row} data-open={isOpen || undefined}>
                      <th scope="row" className={css.first}>
                        <button
                          type="button"
                          id={`row-${r.id}`}
                          aria-expanded={isOpen}
                          aria-controls={`detail-${r.id}`}
                          onClick={() => setOpen(isOpen ? null : r.id)}
                        >
                          <span className={css.chev} aria-hidden="true">
                            ›
                          </span>
                          <code>{r.name}</code>
                        </button>
                      </th>
                      <td>
                        <ModelMark s={st.syntax} />
                      </td>
                      <td>
                        <ModelMark s={st.validation} />
                      </td>
                      <td>
                        <ModelMark s={st.execution} />
                      </td>
                      <td className={css.proofCol}>
                        <ProofCell s={st.progress} />
                      </td>
                      <td>
                        <ProofCell s={st.preservation} />
                      </td>
                    </tr>
                    {isOpen && (
                      <tr className={css.detailRow} id={`detail-${r.id}`}>
                        <td colSpan={6}>
                          <RowDetail r={r} />
                        </td>
                      </tr>
                    )}
                  </Fragment>
                );
              })}
            </Fragment>
          ))}
        </tbody>
      </table>
    </div>
  );
}

function Ctors({ names }: { names: string[] }) {
  return (
    <ul className={css.ctors}>
      {names.map((n) => {
        const site = constructorSite(n);
        return (
          <li key={n}>
            {site ? (
              <a href={sourceHref(site.file, site.line)} target="_blank" rel="noreferrer">
                <code>{n}</code>
              </a>
            ) : (
              <code className={css.absent}>{n}</code>
            )}
          </li>
        );
      })}
    </ul>
  );
}

function RowDetail({ r }: { r: InstructionRow }) {
  const edge = r.edge ? edgeById[r.edge] : undefined;
  return (
    <div className={css.detail}>
      <div className={css.detailHead}>
        <p>{r.blurb}</p>
        <div className={css.detailRefs}>
          {r.spec?.valid && <RefLink r={r.spec.valid} />}
          {r.spec?.exec && <RefLink r={r.spec.exec} />}
        </div>
      </div>
      <dl className={css.detailGrid}>
        <div>
          <dt>Typing rules</dt>
          <dd>
            <Ctors names={r.validation} />
          </dd>
        </div>
        <div>
          <dt>Reduction rules</dt>
          <dd>{r.execution === 'value' ? <span className={css.muted}>none: a value</span> : <Ctors names={r.execution} />}</dd>
        </div>
        <div>
          <dt>Progress</dt>
          <dd>
            <ul className={css.points}>
              {r.progress.map((p) => (
                <li key={p.lemma + p.case}>
                  <CoqPoint p={p} />
                </li>
              ))}
            </ul>
          </dd>
        </div>
        <div>
          <dt>Preservation</dt>
          <dd>
            {r.preservation === 'na' ? (
              <span className={css.muted}>nothing to prove: values do not step</span>
            ) : (
              <ul className={css.points}>
                {r.preservation.map((p) => (
                  <li key={p.lemma + p.case}>
                    <CoqPoint p={p} />
                  </li>
                ))}
              </ul>
            )}
          </dd>
        </div>
      </dl>
      {edge && (
        <a className={css.edgeLink} href={edgeHash(edge.id)}>
          Proof edge: {edge.title} →
        </a>
      )}
    </div>
  );
}
