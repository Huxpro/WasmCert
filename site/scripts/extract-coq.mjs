#!/usr/bin/env node
// Reads ../coq/*.v (the files listed in _CoqProject) and writes
// src/generated/coq-index.json. Run automatically before `dev` and `build`.

import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { execSync } from 'node:child_process';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseLemmas, parseInductives, stripComments } from './coq-parse.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const COQ = resolve(here, '../../coq');
const OUT = resolve(here, '../src/generated/coq-index.json');

const files = readFileSync(resolve(COQ, '_CoqProject'), 'utf8')
  .split('\n')
  .map((l) => l.trim())
  .filter((l) => l.endsWith('.v') && !l.startsWith('Lib/')); // vendored LibTactics is not project work

function git(cmd, fallback) {
  try {
    return execSync(`git ${cmd}`, { cwd: COQ, stdio: ['ignore', 'pipe', 'ignore'] }).toString().trim();
  } catch {
    return fallback;
  }
}

const lemmas = {};
const inductives = {};
const fileStats = [];

// How often the proofs use the tactics SF teaches (LibTactics is covered in PLF's UseTactics).
const TACTICS = ['introv', 'inverts', 'gen', 'splits', 'asserts_rewrite', 'dependent induction', 'inductions',
  'inversion', 'induction', 'destruct', 'eapply', 'econstructor', 'eauto', 'remember', 'admit', 'skip'];
const tactics = Object.fromEntries(TACTICS.map((t) => [t, 0]));

for (const file of files) {
  const raw = readFileSync(resolve(COQ, file), 'utf8');
  const ls = parseLemmas(file, raw);
  const stripped = stripComments(raw);
  for (const t of TACTICS) {
    const re = new RegExp(String.raw`(?<![\w.])${t.replace(' ', String.raw`\s+`)}(?![\w'])`, 'g');
    tactics[t] += (stripped.match(re) ?? []).length;
  }
  for (const l of ls) {
    const key = lemmas[l.name] ? `${file}#${l.name}` : l.name;
    lemmas[key] = l;
  }
  for (const ind of parseInductives(file, raw)) {
    inductives[inductives[ind.name] ? `${file}#${ind.name}` : ind.name] = ind;
  }
  const real = ls.filter((l) => !l.isTest);
  fileStats.push({
    file,
    lines: raw.split('\n').length,
    proved: real.filter((l) => l.status === 'proved').length,
    partial: real.filter((l) => l.status === 'partial').length,
    stated: real.filter((l) => l.status === 'stated').length,
    aborted: real.filter((l) => l.status === 'aborted').length,
  });
}

// Dependencies: which other lemmas does each proof mention by name?
// (The project only registers constructors as hints, so `eauto` cannot pull in
// lemmas behind our back; textual references are a faithful approximation.)
const names = new Set(Object.values(lemmas).filter((l) => !l.isTest).map((l) => l.name));
for (const l of Object.values(lemmas)) {
  const tokens = new Set(l._body.match(/[\p{L}_][\p{L}\p{N}_']*/gu) ?? []);
  l.deps = [...tokens].filter((t) => t !== l.name && names.has(t));
  delete l._body;
}

// Trust: a Qed proof is only "closed" if everything it leans on is closed too.
const byName = Object.fromEntries(Object.values(lemmas).filter((l) => !l.isTest).map((l) => [l.name, l]));
const memo = new Map();
function trust(name, seen = new Set()) {
  if (memo.has(name)) return memo.get(name);
  const l = byName[name];
  if (!l) return 'closed';
  if (l.status !== 'proved') return 'open';
  if (seen.has(name)) return 'closed';
  seen.add(name);
  const t = l.deps.every((d) => trust(d, seen) === 'closed') ? 'closed' : 'modulo';
  memo.set(name, t);
  return t;
}
for (const l of Object.values(lemmas)) {
  l.trust = l.isTest ? null : trust(l.name);
  if (l.trust === 'modulo') {
    const blockers = new Set();
    const walk = (n, seen = new Set()) => {
      if (seen.has(n)) return;
      seen.add(n);
      for (const d of byName[n]?.deps ?? []) {
        if (!byName[d]) continue;
        if (byName[d].status !== 'proved') blockers.add(d);
        else walk(d, seen);
      }
    };
    walk(l.name);
    l.blockedBy = [...blockers];
  }
}

tactics.induction -= tactics['dependent induction']; // counted separately

const index = {
  repo: 'Huxpro/WasmCert',
  commit: git('rev-parse HEAD', 'master'),
  commitDate: git('log -1 --format=%cI', null),
  files: fileStats,
  tactics,
  lemmas,
  inductives,
};

mkdirSync(dirname(OUT), { recursive: true });
writeFileSync(OUT, JSON.stringify(index, null, 2) + '\n');

const real = Object.values(lemmas).filter((l) => !l.isTest);
const count = (s) => real.filter((l) => l.status === s).length;
console.log(
  `coq-index: ${real.length} lemmas (${count('proved')} proved, ${count('partial')} partial, ` +
    `${count('stated')} stated, ${count('aborted')} aborted) from ${files.length} files`,
);
