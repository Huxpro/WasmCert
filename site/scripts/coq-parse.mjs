// Lightweight, dependency-free reader for Coq vernacular.
//
// This is NOT a Coq parser. It recognises just enough structure to answer the
// questions the site asks: which lemmas exist, how each proof ends
// (Qed / Admitted / Abort), where the `admit`s are, which bullet cases are
// still open, and which constructors an inductive has. Everything works on a
// copy of the source with comments blanked out (same length, same newlines),
// so offsets and line numbers stay aligned with the original file.

const IDENT = String.raw`[\p{L}_][\p{L}\p{N}_']*`;

/** Replace every (nested) comment and string body with spaces, keeping newlines. */
export function stripComments(src) {
  const out = src.split('');
  let depth = 0;
  let inString = false;
  for (let i = 0; i < src.length; i++) {
    const c = src[i];
    const next = src[i + 1];
    if (!inString && c === '(' && next === '*') {
      depth++;
      out[i] = out[i + 1] = ' ';
      i++;
      continue;
    }
    if (depth > 0 && c === '*' && next === ')') {
      depth--;
      out[i] = out[i + 1] = ' ';
      i++;
      continue;
    }
    if (depth > 0) {
      if (c !== '\n') out[i] = ' ';
      continue;
    }
    if (c === '"') {
      inString = !inString;
      continue;
    }
    if (inString && c !== '\n') out[i] = ' ';
  }
  return out.join('');
}

export function lineAt(src, offset) {
  let line = 1;
  for (let i = 0; i < offset && i < src.length; i++) if (src[i] === '\n') line++;
  return line;
}

/** Module / Section nesting, so lemmas inside `Module FooTest.` can be flagged. */
function scopeEvents(stripped) {
  const events = [];
  const open = new RegExp(String.raw`\b(Module(?:\s+Type)?|Section)\s+(${IDENT})([\s\S]*?)\.(?=\s)`, 'gu');
  for (const m of stripped.matchAll(open)) {
    if (m[3].includes(':=')) continue; // `Module A := B.` does not open a scope
    events.push({ at: m.index, kind: 'open', name: m[2] });
  }
  const close = new RegExp(String.raw`\bEnd\s+(${IDENT})\s*\.`, 'gu');
  for (const m of stripped.matchAll(close)) events.push({ at: m.index, kind: 'close', name: m[1] });
  return events.sort((a, b) => a.at - b.at);
}

function scopeAt(events, offset) {
  const stack = [];
  for (const e of events) {
    if (e.at > offset) break;
    if (e.kind === 'open') stack.push(e.name);
    else {
      const i = stack.lastIndexOf(e.name);
      if (i >= 0) stack.length = i;
    }
  }
  return stack;
}

const ADMIT = /\b(admit|skip)\s*\./g;

/**
 * Walk the bullets (-, +, *, ++, ...) of a proof body and return labelled cases.
 * Coq bullet semantics: a bullet kind already on the stack closes everything
 * deeper than it; a new kind opens a deeper level.
 */
export function proofCases(raw, stripped, bodyStart, bodyEnd, fileSrc) {
  const bulletRe = /(^|\n)([ \t]*)(-+|\++|\*+)(?=[ \t])/g;
  const body = stripped.slice(bodyStart, bodyEnd);
  const bullets = [];
  const stack = [];
  for (const m of body.matchAll(bulletRe)) {
    const tok = m[3];
    const at = bodyStart + m.index + m[1].length + m[2].length;
    const idx = stack.indexOf(tok);
    if (idx >= 0) stack.length = idx + 1;
    else stack.push(tok);
    const level = stack.indexOf(tok);
    // The case label is the comment that immediately follows the bullet in the raw text.
    const after = raw.slice(at + tok.length, at + tok.length + 160);
    const lm = after.match(new RegExp(String.raw`^[ \t]*\(\*\s*\[?\s*(${IDENT})`, 'u'));
    bullets.push({ at, level, label: lm ? lm[1] : null });
  }
  return bullets.map((b, i) => {
    let end = bodyEnd;
    for (let j = i + 1; j < bullets.length; j++) {
      if (bullets[j].level <= b.level) {
        end = bullets[j].at;
        break;
      }
    }
    const segment = stripped.slice(b.at, end);
    const admits = [...segment.matchAll(ADMIT)].length;
    return {
      label: b.label,
      level: b.level,
      line: lineAt(fileSrc, b.at),
      status: admits > 0 ? 'open' : 'closed',
      admits,
    };
  });
}

const DECL = new RegExp(
  String.raw`\b(Theorem|Lemma|Corollary|Proposition|Fact|Remark|Example)\s+(${IDENT})`,
  'gu',
);
const END = /\b(Qed|Defined|Admitted|Abort)\s*\./g;

/** All lemma-like declarations in one file. */
export function parseLemmas(file, raw) {
  const stripped = stripComments(raw);
  const events = scopeEvents(stripped);
  const lemmas = [];
  for (const m of stripped.matchAll(DECL)) {
    // `Example foo := t.` is a definition in disguise: no proof to track.
    const stmtEnd = stripped.slice(m.index).search(/\.(?=\s)/);
    if (stmtEnd >= 0 && stripped.slice(m.index, m.index + stmtEnd).includes(':=')) continue;
    END.lastIndex = m.index + m[0].length;
    const end = END.exec(stripped);
    if (!end) continue;
    const endOffset = end.index + end[0].length;
    const text = stripped.slice(m.index, end.index);
    const proofIdx = text.search(/\bProof\b/);
    const proofBody = proofIdx >= 0 ? text.slice(proofIdx).replace(/^Proof\b[^.]*\./, '') : '';
    const admits = [...text.matchAll(ADMIT)].length;
    const terminator = end[1];
    let status;
    if (terminator === 'Qed' || terminator === 'Defined') status = 'proved';
    else if (terminator === 'Abort') status = 'aborted';
    else status = proofBody.trim().length > 0 ? 'partial' : 'stated';
    const scope = scopeAt(events, m.index);
    const bodyStart = m.index + (proofIdx >= 0 ? proofIdx : text.length);
    lemmas.push({
      name: m[2],
      kind: m[1],
      file,
      line: lineAt(raw, m.index),
      endLine: lineAt(raw, endOffset),
      status,
      admits,
      scope,
      // Examples, test modules and archived `*_old` attempts don't count towards progress.
      isTest: m[1] === 'Example' || /_old$/.test(m[2]) || scope.some((s) => /test/i.test(s)),
      cases: proofCases(raw, stripped, bodyStart, end.index, raw).filter((c) => c.label),
      _body: stripped.slice(bodyStart, end.index),
    });
  }
  return lemmas;
}

/**
 * Constructors of every `Inductive X` / `with X` block. The block ends at the
 * next depth-0 `.` followed by whitespace, or at the next depth-0 `with`/`where`.
 */
export function parseInductives(file, raw) {
  const stripped = stripComments(raw);
  // `with` only counts at the start of a line (mutual inductives), never in
  // `Proof with eauto.` or `match .. with`; the head may not cross a sentence end.
  const head = new RegExp(
    String.raw`(\bInductive|\bCoInductive|(?<=(?:^|\n)[ \t]*)with)\s+(${IDENT})(?:[^.]|\.(?=\S))*?:=`,
    'gu',
  );
  const out = [];
  for (const m of stripped.matchAll(head)) {
    let i = m.index + m[0].length;
    let depth = 0;
    const ctors = [];
    let expectFirst = true;
    for (; i < stripped.length; i++) {
      const c = stripped[i];
      if (c === '(' || c === '{' || c === '[') depth++;
      else if (c === ')' || c === '}' || c === ']') depth--;
      else if (depth === 0 && c === '.' && /\s/.test(stripped[i + 1] ?? ' ')) break;
      else if (depth === 0 && /\s/.test(stripped[i - 1] ?? ' ') && /^(with|where)\s/.test(stripped.slice(i, i + 6))) break;
      if (depth === 0 && (c === '|' || (expectFirst && /\S/.test(c)))) {
        const from = c === '|' ? i + 1 : i;
        const cm = stripped.slice(from, from + 120).match(new RegExp(String.raw`^\s*(${IDENT})`, 'u'));
        if (cm) ctors.push({ name: cm[1], line: lineAt(raw, from) });
        expectFirst = false;
      }
    }
    out.push({ name: m[2], file, line: lineAt(raw, m.index), constructors: ctors });
  }
  return out;
}
