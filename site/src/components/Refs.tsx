import { refHref, refLabel, type Ref } from '../data/refs';
import { lemma, pointStatus, sourceHref, type ProofPoint } from '../data/coq';
import { StatusMark } from './Status';
import css from './Refs.module.css';

const KIND: Record<Ref['kind'], string> = { spec: 'Spec', sf: 'SF', web: 'Paper' };

export function RefLink({ r }: { r: Ref }) {
  return (
    <a className={css.ref} data-kind={r.kind} href={refHref(r)} target="_blank" rel="noreferrer">
      <span className={css.kind}>{KIND[r.kind]}</span>
      <span className={css.label}>{refLabel(r)}</span>
    </a>
  );
}

export function RefList({ refs }: { refs: Ref[] }) {
  if (!refs.length) return null;
  return (
    <ul className={css.list}>
      {refs.map((r) => (
        <li key={refHref(r)}>
          <RefLink r={r} />
        </li>
      ))}
    </ul>
  );
}

/** A lemma (or one case of it), linked to the exact lines on GitHub. */
export function CoqPoint({ p }: { p: ProofPoint }) {
  const l = lemma(p.lemma);
  const c = p.case ? l?.cases.find((c) => c.label === p.case) : undefined;
  const status = pointStatus(p);
  const href = l ? sourceHref(l.file, c?.line ?? l.line, c ? undefined : l.endLine) : undefined;
  const text = (
    <>
      <StatusMark status={status} size={10} />
      <code>{p.lemma}</code>
      {p.case && <span className={css.case}>case {p.case}</span>}
      {l && <span className={css.file}>{l.file}</span>}
    </>
  );
  return href ? (
    <a className={css.coq} href={href} target="_blank" rel="noreferrer" title={blockedTitle(p.lemma)}>
      {text}
    </a>
  ) : (
    <span className={css.coq}>{text}</span>
  );
}

function blockedTitle(name: string) {
  const b = lemma(name)?.blockedBy;
  return b?.length ? `Relies on admitted: ${b.join(', ')}` : undefined;
}

/** Paragraph text where `backticks` become inline code. */
export function Prose({ text }: { text: string }) {
  const parts = text.split(/`([^`]+)`/g);
  return <>{parts.map((s, i) => (i % 2 ? <code key={i}>{s}</code> : s))}</>;
}
