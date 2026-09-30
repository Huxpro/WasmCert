#!/usr/bin/env node
// Verifies that every spec anchor the site links to exists in the W3C document.
// Needs network access; run manually (`npm run check-refs`) after editing refs.

import { readFileSync, readdirSync, statSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const src = resolve(here, '../src');
const refs = readFileSync(join(src, 'data/refs.ts'), 'utf8');
const base = refs.match(/SPEC_BASE = '([^']+)'/)[1];

const files = (d) => readdirSync(d).flatMap((f) => (statSync(join(d, f)).isDirectory() ? files(join(d, f)) : [join(d, f)]));
const text = files(src).filter((f) => f.endsWith('.ts') || f.endsWith('.tsx')).map((f) => readFileSync(f, 'utf8')).join('\n');

const anchors = new Set([...text.matchAll(/spec\('([a-z0-9-]+)'/g)].map((m) => m[1]));
for (const m of text.matchAll(/spec(Exec|Valid)\('([a-z0-9-]+)'/g)) anchors.add(`${m[1] === 'Exec' ? 'exec' : 'valid'}-${m[2]}`);
// `s(slug, …)` in instructions.ts expands to both exec-* and valid-*.
for (const m of text.matchAll(/\bs\('([a-z0-9-]+)'/g)) anchors.add(`exec-${m[1]}`).add(`valid-${m[1]}`);

const html = await (await fetch(base)).text();
const ids = new Set([...html.matchAll(/id="([^"]+)"/g)].map((m) => m[1]));
const missing = [...anchors].filter((a) => !ids.has(a)).sort();
console.log(`${anchors.size} anchors checked against ${base}`);
if (missing.length) {
  console.error(`missing: ${missing.join(', ')}`);
  process.exit(1);
}
