import { useEffect, useState } from 'react';

// Hash routes use bare tokens only (letters, digits, - _ . ~) so they also
// survive hosts that strip anything fancier:
//   #overview · #edges · #edge-<id> · #node-<id>

export type Route =
  | { view: 'overview' }
  | { view: 'edges'; select?: { type: 'edge' | 'node'; id: string } };

export function parse(hash: string): Route {
  const h = hash.replace(/^#/, '');
  const m = h.match(/^(edge|node)-(.+)$/);
  if (m) return { view: 'edges', select: { type: m[1] as 'edge' | 'node', id: m[2] } };
  if (h === 'edges') return { view: 'edges' };
  return { view: 'overview' };
}

export const edgeHash = (id: string) => `#edge-${id}`;
export const nodeHash = (id: string) => `#node-${id}`;

export function useRoute(): Route {
  const [route, setRoute] = useState(() => parse(window.location.hash));
  useEffect(() => {
    const on = () => setRoute(parse(window.location.hash));
    window.addEventListener('hashchange', on);
    return () => window.removeEventListener('hashchange', on);
  }, []);
  return route;
}
