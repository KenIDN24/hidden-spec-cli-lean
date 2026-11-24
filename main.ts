// main.ts is mend, the CLI SPEC.md specifies (MIT). Node 22, standard library alone; run as `node main.ts [options] [PATCH]`.
// Implements SPEC.md sections 1-10: invocation, output/exit codes, safe paths, format detection, three-tier line
// matching, unified diffs, SEARCH/REPLACE blocks, V4A patches, JSON edits, ordered atomic application.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;
type Move = [string, string];

/** A file split per section 3: its own line break, its lines, whether it ends with a break. */
interface FileParts {
  br: string;
  lines: string[];
  final: boolean;
}
function splitFile(text: string): FileParts {
  if (text === '') return { br: '\n', lines: [], final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const final = text.endsWith(br);
  if (final) parts.pop();
  return { br, lines: parts, final };
}
function joinFile(f: FileParts): string {
  return f.lines.length === 0 ? '' : f.lines.join(f.br) + (f.final ? f.br : '');
}

/** Section 5: line matching at three tiers. */
function tierLine(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return s.replace(/[ \t]+$/, '');
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}
function findOccFrom(fileLines: string[], O: string[], strict: boolean, from: number, eofOnly: boolean, phantom = false): { tier: number; positions: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  const limit = fileLines.length + (phantom ? 1 : 0);
  const at = (idx: number): string => (idx < fileLines.length ? fileLines[idx]! : '');
  for (const t of tiers) {
    const ot = O.map((x) => tierLine(x, t));
    const positions: number[] = [];
    for (let i = from; i + O.length <= limit; i++) {
      const end = i + O.length;
      if (eofOnly && end !== fileLines.length && !(phantom && end === limit)) continue;
      let ok = true;
      for (let j = 0; j < O.length; j++) {
        if (tierLine(at(i + j), t) !== ot[j]) {
          ok = false;
          break;
        }
      }
      if (ok) positions.push(i);
    }
    if (positions.length > 0) return { tier: t, positions };
  }
  return null;
}
const leadingWS = (s: string): string => /^[ \t]*/.exec(s)![0];
function reindent(text: string, F: string, P: string): string {
  if (text === '' || /^[ \t]+$/.test(text)) return text;
  return text.startsWith(P) ? F + text.slice(P.length) : text;
}

interface BodyLine {
  t: string; // ' ', '-', '+' or '\\'
  text: string;
  empty?: boolean; // came from a truly empty patch line
}
function bodyON(body: BodyLine[]): { O: string[]; N: number } {
  const O: string[] = [];
  let N = 0;
  for (const b of body) {
    if (b.t === ' ' || b.t === '-') O.push(b.text);
    if (b.t === ' ' || b.t === '+') N += 1;
  }
  return { O, N };
}
/** Replace the matched region at `pos` by walking the body: context lines come from the file itself.
 *  When the match consumes the phantom empty piece after a final break (pos + O length = lines + 1),
 *  that context element is dropped from the segment: it is the break artifact, not a real line. */
function applyBody(fileLines: string[], pos: number, body: BodyLine[], tier: number, phantom = false): string[] {
  let F = '';
  let P = '';
  if (tier === 2) {
    F = leadingWS(fileLines[pos] ?? '');
    const firstO = body.find((b) => b.t === ' ' || b.t === '-');
    P = firstO ? leadingWS(firstO.text) : '';
  }
  const seg: string[] = [];
  let idx = pos;
  let phantomIdx = -1;
  for (const b of body) {
    if (b.t === ' ') {
      if (phantom && idx === fileLines.length) phantomIdx = seg.length;
      seg.push(fileLines[idx] ?? '');
      idx += 1;
    } else if (b.t === '-') {
      idx += 1;
    } else if (b.t === '+') {
      seg.push(tier === 2 ? reindent(b.text, F, P) : b.text);
    }
  }
  if (phantomIdx >= 0) seg.splice(phantomIdx, 1);
  return seg;
}
/** True when a `\` line follows the body's last context or `+` line. */
function noBreakAfter(body: BodyLine[]): boolean {
  for (let j = body.length - 1; j >= 0; j--) {
    if (body[j]!.t === ' ' || body[j]!.t === '+') {
      const nxt = body[j + 1];
      return nxt !== undefined && nxt.t === '\\';
    }
  }
  return false;
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const f = splitFile(before);
      if (line < 0 || line > f.lines.length) throw new Fail('no-match', p);
      f.lines.splice(line, 0, ...add);
      tree.now.set(p, joinFile(f));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/** Section 6: unified diffs. */
interface Hunk {
  A: number;
  body: BodyLine[];
}
interface Section {
  diffOld?: string;
  diffNew?: string;
  oldRaw?: string | null;
  newRaw?: string | null;
  renOld?: string;
  renNew?: string;
  newFile: boolean;
  delFile: boolean;
  pair: boolean;
  hunks: Hunk[];
}
function sectionEdit(sec: Section, oldPath: string | null, newPath: string | null, strict: boolean, moves: Move[]): Edit {
  const creation = oldPath === null || sec.newFile;
  const deletion = !creation && (newPath === null || sec.delFile);
  return (tree) => {
    for (const p of [oldPath, newPath]) {
      if (p !== null && !safe(p)) throw new Fail('unsafe', p);
    }
    if (creation) {
      const target = newPath!;
      if (tree.get(target) !== null) throw new Fail('exists', target);
      const outLines: string[] = [];
      let lastPlus: { h: number; b: number } | null = null;
      sec.hunks.forEach((h, hi) => {
        h.body.forEach((b, bi) => {
          if (b.t === '+') {
            outLines.push(b.text);
            lastPlus = { h: hi, b: bi };
          }
        });
      });
      let final = true;
      if (lastPlus !== null) {
        const nxt = sec.hunks[lastPlus.h]!.body[lastPlus.b + 1];
        if (nxt !== undefined && nxt.t === '\\') final = false;
      }
      tree.now.set(target, outLines.length === 0 ? '' : outLines.join('\n') + (final ? '\n' : ''));
      return;
    }
    if (deletion) {
      const target = oldPath!;
      if (tree.get(target) === null) throw new Fail('missing', target);
      tree.now.set(target, null);
      return;
    }
    const src = oldPath!;
    const dst = newPath!;
    const before = tree.get(src);
    if (before === null) throw new Fail('missing', src);
    const isMove = dst !== src;
    if (isMove && tree.get(dst) !== null) throw new Fail('exists', dst);
    const f = splitFile(before);
    let d = 0;
    for (const h of sec.hunks) {
      const { O, N } = bodyON(h.body);
      if (O.length === 0) {
        const pos = Math.min(h.A + d, f.lines.length);
        const add = h.body.filter((b) => b.t === '+').map((b) => b.text);
        const touchEnd = pos === f.lines.length;
        f.lines.splice(pos, 0, ...add);
        if (touchEnd) f.final = !noBreakAfter(h.body);
        d += add.length;
      } else {
        const occ = findOccFrom(f.lines, O, strict, 0, false, f.final);
        if (occ === null) throw new Fail('no-match', src);
        const targetPos = h.A - 1 + d;
        let pos = occ.positions[0]!;
        let best = Math.abs(pos - targetPos);
        for (const p of occ.positions) {
          const dd = Math.abs(p - targetPos);
          if (dd < best) {
            best = dd;
            pos = p;
          }
        }
        const seg = applyBody(f.lines, pos, h.body, occ.tier, f.final);
        const touchEnd = pos + O.length >= f.lines.length;
        f.lines.splice(pos, O.length, ...seg);
        if (touchEnd) f.final = !noBreakAfter(h.body);
        d += N - O.length;
      }
    }
    if (isMove) {
      tree.now.set(dst, joinFile(f));
      tree.now.set(src, null);
      moves.push([src, dst]);
    } else {
      tree.now.set(src, joinFile(f));
    }
  };
}
function unifiedEdits(lines: string[], strict: boolean, moves: Move[]): Edit[] {
  const sections: Section[] = [];
  let cur: Section | null = null;
  let header = false;
  const newSec = (dOld?: string, dNew?: string): Section => {
    const s: Section = { diffOld: dOld, diffNew: dNew, newFile: false, delFile: false, pair: false, hunks: [] };
    sections.push(s);
    return s;
  };
  const pathOf = (l: string): string | null => {
    let raw = l.slice(4);
    const t = raw.indexOf('\t');
    if (t >= 0) raw = raw.slice(0, t);
    raw = raw.replace(/^ +| +$/g, '');
    if (raw === '/dev/null') return null;
    if (raw.startsWith('a/') || raw.startsWith('b/')) raw = raw.slice(2);
    return raw;
  };
  const diffPaths = (l: string, ln: number): [string, string] => {
    const m = /^a\/(.+?) b\/(.+)$/.exec(l.slice(11));
    if (m === null) throw new Exit2(`error: parse ${ln}`);
    return [m[1]!, m[2]!];
  };
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    const isDiff = l.startsWith('diff --git ');
    const isPair = l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ');
    if (isDiff) {
      const [x, y] = diffPaths(l, i + 1);
      cur = newSec(x, y);
      header = true;
      i += 1;
      continue;
    }
    if (cur === null && l.startsWith('@@')) throw new Exit2(`error: parse ${i + 1}`);
    if (isPair && (cur === null || !header || cur.pair)) {
      cur = newSec();
      header = true;
    }
    if (cur !== null && header) {
      if (l.startsWith('--- ')) {
        if (!(lines[i + 1] ?? '').startsWith('+++ ')) throw new Exit2(`error: parse ${i + 2}`);
        cur.oldRaw = pathOf(l);
        cur.newRaw = pathOf(lines[i + 1]!);
        cur.pair = true;
        i += 2;
        continue;
      }
      if (l.startsWith('rename from ')) {
        cur.renOld = l.slice(12).trim();
        i += 1;
        continue;
      }
      if (l.startsWith('rename to ')) {
        cur.renNew = l.slice(10).trim();
        i += 1;
        continue;
      }
      if (l.startsWith('new file mode')) {
        cur.newFile = true;
        i += 1;
        continue;
      }
      if (l.startsWith('deleted file mode')) {
        cur.delFile = true;
        i += 1;
        continue;
      }
      if (l.startsWith('@@')) {
        header = false;
      } else {
        i += 1;
        continue;
      }
    }
    if (cur !== null && !header) {
      if (isPair) {
        cur = newSec();
        header = true;
        continue;
      }
      if (l.startsWith('@@')) {
        const m = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(l);
        if (m === null) throw new Exit2(`error: parse ${i + 1}`);
        const A = parseInt(m[1]!, 10);
        i += 1;
        const body: BodyLine[] = [];
        while (i < lines.length) {
          const bl = lines[i]!;
          if (bl.startsWith('diff --git ')) break;
          if (bl.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
          if (bl === '') {
            body.push({ t: ' ', text: '', empty: true });
            i += 1;
            continue;
          }
          const c = bl[0]!;
          if (c === ' ' || c === '-' || c === '+' || c === '\\') {
            body.push({ t: c, text: bl.slice(1) });
            i += 1;
            continue;
          }
          break;
        }
        while (body.length > 0 && body[body.length - 1]!.empty === true) body.pop();
        cur.hunks.push({ A, body });
        continue;
      }
      i += 1;
      continue;
    }
    i += 1;
  }
  const edits: Edit[] = [];
  for (const s of sections) {
    const oldPath = s.oldRaw !== undefined ? s.oldRaw : s.renOld !== undefined ? s.renOld : (s.diffOld ?? null);
    const newPath = s.newRaw !== undefined ? s.newRaw : s.renNew !== undefined ? s.renNew : (s.diffNew ?? null);
    edits.push(sectionEdit(s, oldPath, newPath, strict, moves));
  }
  return edits;
}

/** Section 7: SEARCH/REPLACE blocks. */
function srEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    const f = splitFile(before);
    const occ = findOccFrom(f.lines, oldLines, strict, 0, false, f.final);
    if (occ === null) throw new Fail('no-match', path);
    if (occ.positions.length > 1) throw new Fail('ambiguous', path);
    const pos = occ.positions[0]!;
    let seg = newLines;
    if (occ.tier === 2) {
      const F = leadingWS(f.lines[pos]!);
      const P = leadingWS(oldLines[0]!);
      seg = newLines.map((n) => reindent(n, F, P));
    }
    // A match that consumed the phantom empty piece after the final break: a trailing '' in the
    // replacement is that same break artifact, not an extra line.
    if (pos + oldLines.length === f.lines.length + 1 && seg.length > 0 && seg[seg.length - 1] === '') seg = seg.slice(0, -1);
    f.lines.splice(pos, oldLines.length, ...seg);
    tree.now.set(path, joinFile(f));
  };
}
function srEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevPath: string | null = null;
  let searchFrom = 0;
  for (;;) {
    let s = -1;
    for (let j = searchFrom; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') {
        s = j;
        break;
      }
    }
    if (s < 0) break;
    let m = -1;
    let r = -1;
    for (let j = s + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '=======') {
        m = j;
        break;
      }
    }
    if (m >= 0) {
      for (let j = m + 1; j < lines.length; j++) {
        if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
          r = j;
          break;
        }
      }
    }
    if (m < 0 || r < 0) throw new Exit2(`error: parse ${s + 1}`);
    let path: string | null = null;
    for (let j = s - 1; j >= searchFrom; j--) {
      const t = lines[j]!.trim();
      if (t !== '' && !t.startsWith('```')) {
        path = t;
        break;
      }
    }
    if (path === null) {
      if (prevPath !== null) path = prevPath;
      else throw new Exit2(`error: parse ${s + 1}`);
    }
    prevPath = path;
    edits.push(srEdit(path, lines.slice(s + 1, m), lines.slice(m + 1, r), strict));
    searchFrom = r + 1;
  }
  return edits;
}

/** Section 8: V4A patches. */
interface Chunk {
  anchor: string | null;
  eof: boolean;
  body: BodyLine[];
}
function v4aEdits(lines: string[], strict: boolean, moves: Move[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = lines.length - 1;
  while (last > first && blank(lines[last]!)) last -= 1;
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const secStart = (l: string): string | null =>
    l.startsWith('*** Add File: ') ? 'add' : l.startsWith('*** Delete File: ') ? 'del' : l.startsWith('*** Update File: ') ? 'upd' : null;
  const secPath = (l: string): string => l.slice(l.indexOf(': ') + 2).replace(/^ +| +$/g, '');
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const l = lines[i]!;
    if (blank(l)) {
      i += 1;
      continue;
    }
    const kind = secStart(l);
    if (kind === null) throw new Exit2(`error: parse ${i + 1}`);
    const path = secPath(l);
    const secLine = i + 1;
    i += 1;
    if (kind === 'add') {
      const fileLines: string[] = [];
      while (i < last && secStart(lines[i]!) === null) {
        const bl = lines[i]!;
        if (bl.startsWith('+')) fileLines.push(bl.slice(1));
        else if (bl === '') fileLines.push('');
        else throw new Exit2(`error: parse ${i + 1}`);
        i += 1;
      }
      while (fileLines.length > 0 && fileLines[fileLines.length - 1] === '') fileLines.pop();
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) !== null) throw new Fail('exists', path);
        tree.now.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
      });
    } else if (kind === 'del') {
      while (i < last && secStart(lines[i]!) === null) {
        if (!blank(lines[i]!)) throw new Exit2(`error: parse ${i + 1}`);
        i += 1;
      }
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) === null) throw new Fail('missing', path);
        tree.now.set(path, null);
      });
    } else {
      let moveTo: string | null = null;
      if (i < last && lines[i]!.startsWith('*** Move to: ')) {
        moveTo = lines[i]!.slice(13).replace(/^ +| +$/g, '');
        i += 1;
      }
      const chunks: Chunk[] = [];
      let cur: Chunk | null = null;
      const newChunk = (anchor: string | null): void => {
        cur = { anchor, eof: false, body: [] };
        chunks.push(cur);
      };
      while (i < last && secStart(lines[i]!) === null) {
        const bl = lines[i]!;
        if (bl.startsWith('@@')) {
          const a = bl.slice(2).trim();
          newChunk(a === '' ? null : a);
          i += 1;
          continue;
        }
        if (bl.trim() === '*** End of File') {
          if (cur === null) newChunk(null);
          cur!.eof = true;
          cur = null;
          i += 1;
          continue;
        }
        const c = bl[0];
        if (bl === '' || c === ' ' || c === '-' || c === '+') {
          if (cur === null) newChunk(null);
          cur!.body.push({ t: bl === '' ? ' ' : c!, text: bl === '' ? '' : bl.slice(1), empty: bl === '' });
          i += 1;
          continue;
        }
        throw new Exit2(`error: parse ${i + 1}`);
      }
      if (chunks.length > 0) {
        const b = chunks[chunks.length - 1]!.body;
        while (b.length > 0 && b[b.length - 1]!.empty === true) b.pop();
      }
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${secLine}`);
      const target = moveTo;
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (target !== null && !safe(target)) throw new Fail('unsafe', target);
        const before = tree.get(path);
        if (before === null) throw new Fail('missing', path);
        if (target !== null && tree.get(target) !== null) throw new Fail('exists', target);
        const f = splitFile(before);
        let cursor = 0;
        for (const ch of chunks) {
          if (ch.anchor !== null) {
            const tiers = strict ? [0] : [0, 1, 2];
            let found = -1;
            for (const t of tiers) {
              const want = tierLine(ch.anchor, t);
              for (let k = cursor; k < f.lines.length; k++) {
                if (tierLine(f.lines[k]!, t) === want) {
                  found = k;
                  break;
                }
              }
              if (found >= 0) break;
            }
            if (found < 0) throw new Fail('no-match', path);
            cursor = found + 1;
          }
          const { O } = bodyON(ch.body);
          if (O.length === 0) {
            const add = ch.body.filter((b) => b.t === '+').map((b) => b.text);
            const pos = ch.eof ? f.lines.length : Math.min(cursor, f.lines.length);
            f.lines.splice(pos, 0, ...add);
            cursor = pos + add.length;
          } else {
            const occ = findOccFrom(f.lines, O, strict, cursor, ch.eof, f.final);
            if (occ === null) throw new Fail('no-match', path);
            const pos = occ.positions[0]!;
            const seg = applyBody(f.lines, pos, ch.body, occ.tier, f.final);
            f.lines.splice(pos, O.length, ...seg);
            cursor = pos + seg.length;
          }
        }
        if (target !== null) {
          tree.now.set(target, joinFile(f));
          tree.now.set(path, null);
          moves.push([path, target]);
        } else {
          tree.now.set(path, joinFile(f));
        }
      });
    }
  }
  return edits;
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  const moves: Move[] = [];
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, strict, moves)
          : kind === 'search-replace'
            ? srEdits(lines, strict)
            : v4aEdits(lines, strict, moves);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  if (!check) {
    for (const p of tree.now.keys()) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  const byBytes = (a: string, b: string): number => Buffer.compare(Buffer.from(a), Buffer.from(b));
  const validMoves = moves.filter(
    ([o, n]) =>
      tree.original(o) !== null &&
      tree.now.has(o) &&
      tree.now.get(o) === null &&
      tree.original(n) === null &&
      tree.now.has(n) &&
      tree.now.get(n) !== null,
  );
  const suppressed = new Set<string>();
  for (const [o, n] of validMoves) {
    suppressed.add(o);
    suppressed.add(n);
  }
  const rows: { key: string; text: string }[] = [];
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now || suppressed.has(p)) continue;
    rows.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  for (const [o, n] of validMoves) rows.push({ key: n, text: `R ${o} -> ${n}` });
  rows.sort((a, b) => byBytes(a.key, b.key));
  const out = rows.map((r) => r.text);
  return { code: 0, out: [...out, `ok: ${out.length} ${out.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
