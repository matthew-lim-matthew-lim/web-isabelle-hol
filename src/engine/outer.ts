// Outer syntax: tokenizer for theory files and command segmentation.
import { decodeSymbols } from './symbols';

export type OTokKind = 'ident' | 'string' | 'cartouche' | 'nat' | 'sym' | 'var' | 'tvar';

export interface OTok {
  kind: OTokKind;
  v: string; // decoded content (strings / cartouches without delimiters)
  from: number;
  to: number;
}

export interface Command {
  kw: string;
  toks: OTok[]; // tokens after the keyword
  from: number;
  to: number;
}

export const COMMANDS = new Set([
  'theory',
  'begin',
  'end',
  'text',
  'txt',
  'section',
  'subsection',
  'subsubsection',
  'chapter',
  'paragraph',
  'header',
  'text_raw',
  'datatype',
  'fun',
  'primrec',
  'function',
  'termination',
  'definition',
  'abbreviation',
  'type_synonym',
  'axiomatization',
  'consts',
  'declare',
  'lemmas',
  'inductive',
  'lemma',
  'theorem',
  'corollary',
  'proposition',
  'schematic_goal',
  'apply',
  'done',
  'by',
  '.',
  '..',
  'sorry',
  'oops',
  'proof',
  'qed',
  'next',
  'fix',
  'assume',
  'presume',
  'have',
  'show',
  'hence',
  'thus',
  'then',
  'from',
  'with',
  'using',
  'unfolding',
  'note',
  'case',
  'obtain',
  'let',
  'moreover',
  'ultimately',
  'also',
  'finally',
  'defer',
  'prefer',
  'back',
  'subgoal',
  'value',
  'term',
  'typ',
  'thm',
  'find_theorems',
  'print_theorems',
  'quickcheck',
  'nitpick',
  'sledgehammer',
  'try',
  'try0',
  'prop',
  'print_state',
  'export_code',
  'hide_const',
  'notation',
  'no_notation',
  'supply',
  'interpretation',
  'locale',
  'instantiation',
  'instance',
  'class',
]);

const SYMCHARS = [
  '..',
  '::',
  '==',
  '=>',
  '⇒',
  '(',
  ')',
  '[',
  ']',
  '{',
  '}',
  ',',
  ':',
  '|',
  '=',
  '+',
  '?',
  ';',
  '-',
  '.',
  '!',
  '*',
  '<',
  '>',
  '≡',
  '&',
  '%',
  '/',
  '\\',
  '#',
  '@',
  '^',
  '_',
  '~',
  '`',
];

const isIdStart = (c: string) => /[A-Za-zͰ-Ͽ]/.test(c) && c !== 'λ';
const isIdChar = (c: string) => /[A-Za-z0-9_'Ͱ-Ͽ]/.test(c) && c !== 'λ';

export class OuterError extends Error {
  constructor(
    msg: string,
    public from: number,
    public to: number,
  ) {
    super(msg);
  }
}

export interface Comment {
  from: number;
  to: number;
}

export function tokenizeOuter(src: string): { toks: OTok[]; errors: OuterError[] } {
  const toks: OTok[] = [];
  const errors: OuterError[] = [];
  let i = 0;
  const n = src.length;
  while (i < n) {
    const c = src[i];
    if (/\s/.test(c)) {
      i++;
      continue;
    }
    // comments (* ... *) nested
    if (src.startsWith('(*', i)) {
      let depth = 1;
      let j = i + 2;
      while (j < n && depth > 0) {
        if (src.startsWith('(*', j)) {
          depth++;
          j += 2;
        } else if (src.startsWith('*)', j)) {
          depth--;
          j += 2;
        } else j++;
      }
      if (depth > 0) errors.push(new OuterError('Unclosed comment', i, n));
      i = j;
      continue;
    }
    // — ‹...› or \<comment> ‹...›  marginal comments
    if (c === '—' || src.startsWith('\\<comment>', i) || src.startsWith('--', i)) {
      let j = c === '—' ? i + 1 : src.startsWith('--', i) ? i + 2 : i + 10;
      while (j < n && /\s/.test(src[j])) j++;
      if (src[j] === '‹' || src.startsWith('\\<open>', j)) {
        const end = scanCartouche(src, j);
        i = end.to;
        continue;
      }
      if (src.startsWith('--', i)) {
        // old style -- "comment"
        if (src[j] === '"') {
          const end = scanString(src, j);
          i = end.to;
          continue;
        }
      }
      i = j;
      continue;
    }
    if (c === '"') {
      const r = scanString(src, i);
      if (r.error) errors.push(new OuterError('Unclosed string', i, r.to));
      toks.push({ kind: 'string', v: decodeSymbols(r.content), from: i, to: r.to });
      i = r.to;
      continue;
    }
    if (c === '‹' || src.startsWith('\\<open>', i)) {
      const r = scanCartouche(src, i);
      if (r.error) errors.push(new OuterError('Unclosed cartouche', i, r.to));
      toks.push({ kind: 'cartouche', v: decodeSymbols(r.content), from: i, to: r.to });
      i = r.to;
      continue;
    }
    if (c === "'" && i + 1 < n && isIdStart(src[i + 1])) {
      let j = i + 1;
      while (j < n && isIdChar(src[j])) j++;
      toks.push({ kind: 'tvar', v: src.slice(i, j), from: i, to: j });
      i = j;
      continue;
    }
    if (c === '?' && i + 1 < n && isIdStart(src[i + 1])) {
      let j = i + 1;
      while (j < n && isIdChar(src[j])) j++;
      toks.push({ kind: 'var', v: src.slice(i + 1, j), from: i, to: j });
      i = j;
      continue;
    }
    if (/[0-9]/.test(c)) {
      let j = i;
      while (j < n && /[0-9]/.test(src[j])) j++;
      toks.push({ kind: 'nat', v: src.slice(i, j), from: i, to: j });
      i = j;
      continue;
    }
    if (isIdStart(c)) {
      let j = i;
      for (;;) {
        while (j < n && isIdChar(src[j])) j++;
        if (src[j] === '.' && j + 1 < n && isIdStart(src[j + 1])) {
          j++;
          continue;
        }
        break;
      }
      toks.push({ kind: 'ident', v: src.slice(i, j), from: i, to: j });
      i = j;
      continue;
    }
    let matched = false;
    for (const s of SYMCHARS) {
      if (src.startsWith(s, i)) {
        toks.push({ kind: 'sym', v: s, from: i, to: i + s.length });
        i += s.length;
        matched = true;
        break;
      }
    }
    if (!matched) {
      // other unicode symbols as single symbol tokens
      toks.push({ kind: 'sym', v: c, from: i, to: i + 1 });
      i++;
    }
  }
  return { toks, errors };
}

function scanString(src: string, i: number): { content: string; to: number; error?: boolean } {
  let j = i + 1;
  let out = '';
  while (j < src.length && src[j] !== '"') {
    if (src[j] === '\\' && src[j + 1] === '"') {
      out += '"';
      j += 2;
      continue;
    }
    out += src[j];
    j++;
  }
  if (j >= src.length) return { content: out, to: src.length, error: true };
  return { content: out, to: j + 1 };
}

function scanCartouche(src: string, i: number): { content: string; to: number; error?: boolean } {
  let depth = 0;
  let j = i;
  let start = -1;
  while (j < src.length) {
    if (src[j] === '‹') {
      depth++;
      j++;
      if (start < 0) start = j;
      continue;
    }
    if (src.startsWith('\\<open>', j)) {
      depth++;
      j += 7;
      if (start < 0) start = j;
      continue;
    }
    if (src[j] === '›' || src.startsWith('\\<close>', j)) {
      depth--;
      const len = src[j] === '›' ? 1 : 8;
      if (depth === 0) return { content: src.slice(start, j), to: j + len };
      j += len;
      continue;
    }
    j++;
  }
  return { content: src.slice(Math.max(start, 0)), to: src.length, error: true };
}

/** Split tokens into commands. Tokens before the first command are reported as an error command. */
export function splitCommands(toks: OTok[]): Command[] {
  const cmds: Command[] = [];
  let cur: Command | null = null;
  let depth = 0;
  for (const t of toks) {
    const isCmd =
      (t.kind === 'ident' && COMMANDS.has(t.v) && depth === 0) ||
      (t.kind === 'sym' && (t.v === '.' || t.v === '..') && depth === 0) ||
      (t.kind === 'sym' && (t.v === '{' || t.v === '}') && depth === 0 && cur?.kw !== 'datatype');
    if (isCmd) {
      if (cur) cmds.push(cur);
      cur = { kw: t.v, toks: [], from: t.from, to: t.to };
      depth = 0;
      continue;
    }
    if (!cur) {
      cur = { kw: '<junk>', toks: [], from: t.from, to: t.to };
    }
    if (t.kind === 'sym' && (t.v === '(' || t.v === '[')) depth++;
    if (t.kind === 'sym' && (t.v === ')' || t.v === ']')) depth = Math.max(0, depth - 1);
    cur.toks.push(t);
    cur.to = t.to;
  }
  if (cur) cmds.push(cur);
  return cmds;
}

/** Token stream reader used by command parsers. */
export class TokReader {
  p = 0;
  constructor(
    public toks: OTok[],
    public cmd: Command,
  ) {}
  peek(o = 0): OTok | undefined {
    return this.toks[this.p + o];
  }
  atEnd() {
    return this.p >= this.toks.length;
  }
  next(): OTok {
    const t = this.toks[this.p++];
    if (!t) this.fail('unexpected end of command');
    return t;
  }
  isSym(v: string, o = 0) {
    const t = this.peek(o);
    return !!t && t.kind === 'sym' && t.v === v;
  }
  isIdent(v?: string, o = 0) {
    const t = this.peek(o);
    return !!t && t.kind === 'ident' && (v === undefined || t.v === v);
  }
  expectSym(v: string) {
    if (!this.isSym(v)) this.fail(`expected "${v}"`);
    return this.next();
  }
  expectIdent(v?: string): OTok {
    if (!this.isIdent(v)) this.fail(v ? `expected "${v}"` : 'identifier expected');
    return this.next();
  }
  /** a term argument: string, cartouche, identifier, number, var */
  isTermArg(o = 0) {
    const t = this.peek(o);
    return !!t && (t.kind === 'string' || t.kind === 'cartouche' || t.kind === 'ident' || t.kind === 'nat' || t.kind === 'var' || t.kind === 'tvar');
  }
  termArg(): OTok {
    if (!this.isTermArg()) this.fail('term expected');
    return this.next();
  }
  fail(msg: string): never {
    const t = this.peek();
    const from = t ? t.from : this.cmd.to;
    const to = t ? t.to : this.cmd.to;
    throw new OuterError(`Outer syntax error: ${msg}${t ? ` at "${t.v}"` : ''}`, from, to);
  }
}
