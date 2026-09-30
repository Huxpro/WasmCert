import { useMemo, useState } from 'react';
import { COLUMNS, EDGES, NODES, edgeStatus, nodeById, nodeStatus, type GraphEdge, type GraphNode } from '../data/graph';
import { edgeHash, nodeHash } from '../lib/route';
import css from './ProofGraph.module.css';

// Geometry: columns left→right, rows top→bottom. All positions come from the
// node's (col, row), so adding a node to data/graph.ts is enough to place it.
const NODE_W = 178;
const NODE_H = 50;
const COL_GAP = 58;
const ROW_H = 66;
const PAD_X = 12;
const PAD_TOP = 44;

const colX = (col: number) => PAD_X + col * (NODE_W + COL_GAP);
const rowY = (row: number) => PAD_TOP + row * ROW_H;

const GAP_Y = (ROW_H - NODE_H) / 2; // half the vertical gap between rows

/**
 * Adjacent columns get a plain S-curve. Longer edges would cut through the
 * nodes in between, so they drop into the horizontal gap between two rows
 * (a "lane"), run along it, and climb out in the last column gap.
 */
function edgePath(e: GraphEdge, laneOffset: number) {
  const a = nodeById[e.from];
  const b = nodeById[e.to];
  const x1 = colX(a.col) + NODE_W;
  const y1 = rowY(a.row) + NODE_H / 2;
  const x2 = colX(b.col);
  const y2 = rowY(b.row) + NODE_H / 2;
  if (b.col - a.col <= 1) {
    const dx = Math.max(28, (x2 - x1) * 0.5);
    return {
      d: `M ${x1} ${y1} C ${x1 + dx} ${y1}, ${x2 - dx} ${y2}, ${x2} ${y2}`,
      // Midpoint of the cubic (t = 0.5) for the clickable marker.
      mx: (x1 + 3 * (x1 + dx) + 3 * (x2 - dx) + x2) / 8,
      my: (y1 + 3 * y1 + 3 * y2 + y2) / 8,
    };
  }
  const ly = laneY(e) + laneOffset;
  const c = COL_GAP / 2;
  return {
    d: `M ${x1} ${y1} C ${x1 + c} ${y1}, ${x1 + c * 0.2} ${ly}, ${x1 + c} ${ly} L ${x2 - c} ${ly} C ${x2 - c * 0.2} ${ly}, ${x2 - c} ${y2}, ${x2} ${y2}`,
    mx: (x1 + x2) / 2,
    my: ly,
  };
}

/** The row boundary closest to the target, among those between source and target. */
function laneBoundary(e: GraphEdge) {
  const ra = nodeById[e.from].row;
  const rb = nodeById[e.to].row;
  if (ra === rb) return ra + 1;
  return rb > ra ? rb : rb + 1;
}
const laneY = (e: GraphEdge) => rowY(laneBoundary(e)) - GAP_Y;

/** Edges sharing a lane are nudged apart so they stay distinguishable. */
const LANE_OFFSETS = (() => {
  const seen = new Map<number, number>();
  const out = new Map<string, number>();
  for (const e of EDGES) {
    if (nodeById[e.to].col - nodeById[e.from].col <= 1) continue;
    const k = laneBoundary(e);
    const i = seen.get(k) ?? 0;
    seen.set(k, i + 1);
    out.set(e.id, [0, -5, 5][i % 3]);
  }
  return out;
})();

export interface Selection {
  type: 'edge' | 'node';
  id: string;
}

export function ProofGraph({ selection }: { selection?: Selection }) {
  const [hover, setHover] = useState<string | null>(null);

  const maxRow = Math.max(...NODES.map((n) => n.row));
  const width = colX(COLUMNS.length - 1) + NODE_W + PAD_X;
  const height = rowY(maxRow) + NODE_H + 16;

  // Which edges/nodes are "lit": the selection, or whatever the pointer is on.
  const focusNode = hover ?? (selection?.type === 'node' ? selection.id : null);
  const lit = useMemo(() => {
    const edges = new Set<string>();
    const nodes = new Set<string>();
    if (selection?.type === 'edge' && !hover) {
      const e = EDGES.find((e) => e.id === selection.id);
      if (e) {
        edges.add(e.id);
        nodes.add(e.from).add(e.to);
      }
    }
    if (focusNode) {
      nodes.add(focusNode);
      for (const e of EDGES)
        if (e.from === focusNode || e.to === focusNode) {
          edges.add(e.id);
          nodes.add(e.from).add(e.to);
        }
    }
    return { edges, nodes, any: edges.size + nodes.size > 0 };
  }, [selection, hover, focusNode]);

  return (
    <div className={css.scroller}>
      <svg
        className={css.svg}
        viewBox={`0 0 ${width} ${height}`}
        width={width}
        height={height}
        role="group"
        aria-label="Proof graph: definitions on the left, main theorems on the right"
      >
        <defs>
          <marker id="arrow" viewBox="0 0 8 8" refX="7.5" refY="4" markerWidth="7" markerHeight="7" orient="auto">
            <path d="M0,0 L8,4 L0,8 z" className={css.arrowHead} />
          </marker>
          <marker id="arrow-lit" viewBox="0 0 8 8" refX="7.5" refY="4" markerWidth="7" markerHeight="7" orient="auto">
            <path d="M0,0 L8,4 L0,8 z" className={css.arrowHeadLit} />
          </marker>
        </defs>

        {COLUMNS.map((c, i) => (
          <text key={c} x={colX(i)} y={18} className={css.colLabel}>
            {c.toUpperCase()}
          </text>
        ))}

        {EDGES.map((e) => {
          const { d, mx, my } = edgePath(e, LANE_OFFSETS.get(e.id) ?? 0);
          const status = edgeStatus(e);
          const isLit = lit.edges.has(e.id);
          const selected = selection?.type === 'edge' && selection.id === e.id;
          return (
            <a key={e.id} href={edgeHash(e.id)} className={css.edge} data-status={status} data-lit={isLit || undefined} data-dim={(lit.any && !isLit) || undefined} aria-label={`Edge: ${e.title}`}>
              <title>{`${e.title}\n${e.gist}`}</title>
              <path d={d} className={css.hit} />
              <path d={d} className={css.line} markerEnd={isLit ? 'url(#arrow-lit)' : 'url(#arrow)'} />
              <circle cx={mx} cy={my} r={selected ? 7 : 5.5} className={css.knot} />
            </a>
          );
        })}

        {NODES.map((n) => (
          <Node
            key={n.id}
            n={n}
            lit={lit.nodes.has(n.id)}
            dim={lit.any && !lit.nodes.has(n.id)}
            selected={selection?.type === 'node' && selection.id === n.id}
            onHover={setHover}
          />
        ))}
      </svg>
    </div>
  );
}

function Node({ n, lit, dim, selected, onHover }: { n: GraphNode; lit: boolean; dim: boolean; selected: boolean; onHover: (id: string | null) => void }) {
  const x = colX(n.col);
  const y = rowY(n.row);
  const status = nodeStatus(n);
  return (
    <a
      href={nodeHash(n.id)}
      className={css.node}
      data-kind={n.kind}
      data-status={status}
      data-lit={lit || undefined}
      data-dim={dim || undefined}
      data-selected={selected || undefined}
      onMouseEnter={() => onHover(n.id)}
      onMouseLeave={() => onHover(null)}
      onFocus={() => onHover(n.id)}
      onBlur={() => onHover(null)}
      aria-label={`${n.label}: ${n.summary}`}
    >
      <rect x={x} y={y} width={NODE_W} height={NODE_H} rx={n.kind === 'theorem' || n.kind === 'goal' ? 3 : 6} className={css.box} />
      {n.kind !== 'definition' && <StatusGlyph status={status} x={x + 12} y={y + 17} />}
      <text x={x + (n.kind === 'definition' ? 12 : 24)} y={y + 21} className={css.label}>
        {n.label}
      </text>
      <text x={x + 12} y={y + 38} className={css.sub}>
        {subtitle(n)}
      </text>
    </a>
  );
}

function subtitle(n: GraphNode) {
  if (n.kind === 'definition') return `${n.inductives?.length ?? 0} inductive definitions`;
  if (n.kind === 'goal') return 'not stated yet';
  const k = n.lemmas?.length ?? 0;
  return k === 1 ? (n.lemmas![0].case ? `case ${n.lemmas![0].case}` : n.lemmas![0].lemma) : `${k} lemmas`;
}

/** SVG twin of <StatusMark>: same shapes, so the legend applies to both. */
function StatusGlyph({ status, x, y }: { status: string; x: number; y: number }) {
  const r = 5;
  if (status === 'open') return <rect x={x - 4} y={y - 4} width={8} height={8} transform={`rotate(45 ${x} ${y})`} className={css.gOpen} />;
  if (status === 'missing') return <circle cx={x} cy={y} r={r} className={css.gMissing} />;
  if (status === 'modulo')
    return (
      <g>
        <circle cx={x} cy={y} r={r} className={css.gRing} />
        <path d={`M ${x} ${y - r} A ${r} ${r} 0 0 0 ${x} ${y + r} Z`} className={css.gOk} />
      </g>
    );
  return <circle cx={x} cy={y} r={r} className={css.gOk} />;
}
