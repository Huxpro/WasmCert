import { STATUS_LABEL, type Status } from '../data/coq';
import css from './Status.module.css';

/** The status glyph. Shape and fill carry the meaning, so it survives greyscale. */
export function StatusMark({ status, size = 12 }: { status: Status; size?: number }) {
  return <span className={css.mark} data-status={status} style={{ width: size, height: size }} aria-hidden="true" />;
}

export function StatusPill({ status, label }: { status: Status; label?: string }) {
  return (
    <span className={css.pill} data-status={status}>
      <StatusMark status={status} size={9} />
      {label ?? STATUS_LABEL[status]}
    </span>
  );
}

const LEGEND: Status[] = ['proved', 'modulo', 'open', 'missing'];

export function StatusLegend({ extra }: { extra?: React.ReactNode }) {
  return (
    <ul className={css.legend} aria-label="Legend">
      {LEGEND.map((s) => (
        <li key={s}>
          <StatusMark status={s} />
          {STATUS_LABEL[s]}
        </li>
      ))}
      {extra}
    </ul>
  );
}
