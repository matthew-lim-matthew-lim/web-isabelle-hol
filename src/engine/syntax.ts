// Inner syntax: lexer and Pratt parser for HOL terms and types.
import { EngineError } from './terms';

export type PTy =
  | { t: 'tcon'; name: string; args: PTy[] }
  | { t: 'tvar'; name: string }
  | { t: 'tdummy' };

export type PT =
  | { t: 'id'; name: string }
  | { t: 'const'; name: string }
  | { t: 'var'; name: string }
  | { t: 'num'; n: number }
  | { t: 'app'; f: PT; a: PT }
  | { t: 'abs'; x: string; ty?: PTy; body: PT; pat?: PT }
  | { t: 'q'; q: string; x: string; ty?: PTy; body: PT }
  | { t: 'constraint'; e: PT; ty: PTy }
  | { t: 'case'; e: PT; clauses: { pat: PT; rhs: PT }[] }
  | { t: 'dummy' }
  | { t: 'dots' };

interface Tok {
  kind: 'id' | 'tvar' | 'var' | 'num' | 'sym' | 'eof';
  v: string;
  pos: number;
}

const SYMS = [
  '<-->',
  '==>',
  '-->',
  '<->',
  '..<',
  '...',
  '[|',
  '|]',
  '~=',
  '~:',
  '<=',
  '>=',
  '=>',
  '::',
  '==',
  '!!',
  '..',
  '⟹',
  '⟶',
  '⟷',
  '⟺',
  '⇒',
  '→',
  '∧',
  '∨',
  '¬',
  '∀',
  '∃',
  'λ',
  '⋀',
  '≠',
  '≤',
  '≥',
  '∈',
  '∉',
  '∪',
  '∩',
  '⊆',
  '⊂',
  '×',
  '∘',
  '≡',
  '⟦',
  '⟧',
  '‹',
  '›',
  '…',
  '(',
  ')',
  '[',
  ']',
  '{',
  '}',
  ',',
  '.',
  ':',
  ';',
  '=',
  '<',
  '>',
  '+',
  '-',
  '*',
  '/',
  '^',
  '@',
  '#',
  '&',
  '|',
  '~',
  '%',
  '!',
  '?',
  '_',
  '`',
  '\'',
];

const isIdStart = (c: string) => /[A-Za-zͰ-Ͽᴀ-ᶿ]/.test(c) && c !== 'λ';
const isIdChar = (c: string) => /[A-Za-z0-9_'Ͱ-Ͽ₀-₉]/.test(c) && c !== 'λ';

export function lexInner(s: string): Tok[] {
  const toks: Tok[] = [];
  let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) {
      i++;
      continue;
    }
    if (s.startsWith('(*', i)) {
      const j = s.indexOf('*)', i + 2);
      i = j < 0 ? s.length : j + 2;
      continue;
    }
    if (c === "'" && i + 1 < s.length && isIdStart(s[i + 1])) {
      let j = i + 1;
      while (j < s.length && isIdChar(s[j])) j++;
      toks.push({ kind: 'tvar', v: s.slice(i, j), pos: i });
      i = j;
      continue;
    }
    if (c === '?' && i + 1 < s.length && isIdStart(s[i + 1])) {
      let j = i + 1;
      while (j < s.length && isIdChar(s[j])) j++;
      toks.push({ kind: 'var', v: s.slice(i + 1, j), pos: i });
      i = j;
      continue;
    }
    if (/[0-9]/.test(c)) {
      let j = i;
      while (j < s.length && /[0-9]/.test(s[j])) j++;
      toks.push({ kind: 'num', v: s.slice(i, j), pos: i });
      i = j;
      continue;
    }
    if (isIdStart(c)) {
      let j = i;
      while (j < s.length && isIdChar(s[j])) j++;
      toks.push({ kind: 'id', v: s.slice(i, j), pos: i });
      i = j;
      continue;
    }
    let matched = false;
    for (const sym of SYMS) {
      if (s.startsWith(sym, i)) {
        toks.push({ kind: 'sym', v: sym, pos: i });
        i += sym.length;
        matched = true;
        break;
      }
    }
    if (!matched) throw new EngineError(`Inner lexical error at: ${s.slice(i, i + 10)}`);
  }
  toks.push({ kind: 'eof', v: '', pos: s.length });
  return toks;
}

// Normalise ASCII to canonical symbols
const CANON: Record<string, string> = {
  '==>': '⟹',
  '-->': '⟶',
  '<-->': '⟷',
  '<->': '⟷',
  '⟺': '⟷',
  '=>': '⇒',
  '→': '⇒',
  '&': '∧',
  '|': '∨',
  '~': '¬',
  '~=': '≠',
  '<=': '≤',
  '>=': '≥',
  '~:': '∉',
  '[|': '⟦',
  '|]': '⟧',
  '!!': '⋀',
  '%': 'λ',
  '==': '≡',
  '…': '...',
};

interface InfixInfo {
  prec: number;
  assoc: 'l' | 'r' | 'n';
  build: (a: PT, b: PT) => PT;
}

const C = (name: string): PT => ({ t: 'const', name });
const app = (f: PT, ...args: PT[]): PT => args.reduce((acc, a) => ({ t: 'app', f: acc, a }), f);
const bin = (name: string) => (a: PT, b: PT) => app(C(name), a, b);

export const INFIX: Record<string, InfixInfo> = {
  '⟹': { prec: 1, assoc: 'r', build: bin('==>') },
  '≡': { prec: 2, assoc: 'n', build: bin('eq') },
  '⟷': { prec: 25, assoc: 'r', build: bin('iff') },
  '⟶': { prec: 25, assoc: 'r', build: bin('imp') },
  '∨': { prec: 30, assoc: 'r', build: bin('disj') },
  '∧': { prec: 35, assoc: 'r', build: bin('conj') },
  '=': { prec: 50, assoc: 'l', build: bin('eq') },
  '≠': { prec: 50, assoc: 'l', build: (a, b) => app(C('Not'), app(C('eq'), a, b)) },
  '<': { prec: 50, assoc: 'n', build: bin('less') },
  '≤': { prec: 50, assoc: 'n', build: bin('less_eq') },
  '>': { prec: 50, assoc: 'n', build: (a, b) => app(C('less'), b, a) },
  '≥': { prec: 50, assoc: 'n', build: (a, b) => app(C('less_eq'), b, a) },
  '∈': { prec: 50, assoc: 'n', build: bin('member') },
  ':': { prec: 50, assoc: 'n', build: bin('member') },
  '∉': { prec: 50, assoc: 'n', build: (a, b) => app(C('Not'), app(C('member'), a, b)) },
  '⊆': { prec: 50, assoc: 'n', build: bin('subset_eq') },
  '⊂': { prec: 50, assoc: 'n', build: bin('subset') },
  '∘': { prec: 55, assoc: 'l', build: bin('comp') },
  '#': { prec: 65, assoc: 'r', build: bin('Cons') },
  '@': { prec: 65, assoc: 'r', build: bin('append') },
  '+': { prec: 65, assoc: 'l', build: bin('plus') },
  '-': { prec: 65, assoc: 'l', build: bin('minus') },
  '∪': { prec: 65, assoc: 'l', build: bin('union') },
  '∩': { prec: 70, assoc: 'l', build: bin('inter') },
  '*': { prec: 70, assoc: 'l', build: bin('times') },
  '/': { prec: 70, assoc: 'l', build: bin('divide') },
  div: { prec: 70, assoc: 'l', build: bin('div') },
  mod: { prec: 70, assoc: 'l', build: bin('mod') },
  dvd: { prec: 50, assoc: 'n', build: bin('dvd') },
  o: { prec: 55, assoc: 'l', build: bin('comp') },
  '^': { prec: 80, assoc: 'r', build: bin('power') },
  '!': { prec: 100, assoc: 'l', build: bin('nth') },
  '`': { prec: 90, assoc: 'r', build: bin('image') },
};

// Operator sections like (+) usable as functions.
const SECTIONS: Record<string, string> = {
  '+': 'plus',
  '*': 'times',
  '-': 'minus',
  '@': 'append',
  '#': 'Cons',
  '=': 'eq',
  '∧': 'conj',
  '∨': 'disj',
  '⟶': 'imp',
  '≤': 'less_eq',
  '<': 'less',
  '∘': 'comp',
  '∪': 'union',
  '∩': 'inter',
};

const KEYWORDS = new Set(['if', 'then', 'else', 'case', 'of', 'let', 'in', 'div', 'mod', 'dvd', 'o', 'ALL', 'EX', 'SOME', 'THE']);

export class InnerParser {
  private toks: Tok[];
  private p = 0;
  private inCase = 0;
  constructor(private src: string) {
    this.toks = lexInner(src).map((t) => (t.kind === 'sym' && CANON[t.v] ? { ...t, v: CANON[t.v] } : t));
  }

  private peek(o = 0): Tok {
    return this.toks[Math.min(this.p + o, this.toks.length - 1)];
  }
  private next(): Tok {
    return this.toks[this.p++];
  }
  private isSym(v: string, o = 0) {
    const t = this.peek(o);
    return t.kind === 'sym' && t.v === v;
  }
  private isKw(v: string, o = 0) {
    const t = this.peek(o);
    return t.kind === 'id' && t.v === v;
  }
  private expectSym(v: string) {
    if (!this.isSym(v)) this.fail(`expected "${v}"`);
    this.next();
  }
  private fail(msg: string): never {
    const t = this.peek();
    const at = t.kind === 'eof' ? 'end of input' : this.src.slice(t.pos, t.pos + 20);
    throw new EngineError(`Inner syntax error: ${msg} at "${at}"`);
  }

  parseTermAll(): PT {
    const t = this.parse(0);
    if (this.peek().kind !== 'eof') this.fail('unexpected token');
    return t;
  }

  parseTypeAll(): PTy {
    const t = this.parseType(0);
    if (this.peek().kind !== 'eof') this.fail('unexpected token in type');
    return t;
  }

  // ---------- types ----------
  parseType(min: number): PTy {
    let left = this.parseTypeAtomPostfix();
    for (;;) {
      if (this.isSym('⇒') && min <= 0) {
        this.next();
        const r = this.parseType(0);
        left = { t: 'tcon', name: 'fun', args: [left, r] };
      } else if (this.isSym('×') && min <= 20) {
        this.next();
        const r = this.parseType(20);
        left = { t: 'tcon', name: 'prod', args: [left, r] };
      } else if (this.isSym('*') && min <= 20) {
        this.next();
        const r = this.parseType(20);
        left = { t: 'tcon', name: 'prod', args: [left, r] };
      } else break;
    }
    return left;
  }

  private parseTypeAtomPostfix(): PTy {
    let args: PTy[];
    const t = this.peek();
    if (t.kind === 'sym' && t.v === '(') {
      this.next();
      const first = this.parseType(0);
      const list = [first];
      while (this.isSym(',')) {
        this.next();
        list.push(this.parseType(0));
      }
      this.expectSym(')');
      args = list;
    } else if (t.kind === 'tvar') {
      this.next();
      args = [{ t: 'tvar', name: t.v }];
    } else if (t.kind === 'sym' && t.v === '_') {
      this.next();
      args = [{ t: 'tdummy' }];
    } else if (t.kind === 'id') {
      this.next();
      args = [{ t: 'tcon', name: t.v, args: [] }];
    } else this.fail('type expected');
    // postfix type constructors
    while (this.peek().kind === 'id' && !KEYWORDS.has(this.peek().v)) {
      const name = this.next().v;
      args = [{ t: 'tcon', name, args }];
    }
    if (args.length !== 1) this.fail('bad type arguments');
    return args[0];
  }

  // ---------- terms ----------
  private startsAtom(): boolean {
    const t = this.peek();
    if (t.kind === 'id') return !KEYWORDS.has(t.v) || t.v === 'SOME' || t.v === 'THE';
    if (t.kind === 'num' || t.kind === 'var') return true;
    if (t.kind === 'sym') return ['(', '[', '{', '_', '...', '‹'].includes(t.v);
    return false;
  }

  parse(min: number): PT {
    let left = this.parsePrefix(min);
    for (;;) {
      const t = this.peek();
      if (t.kind === 'eof') break;
      // application
      if (this.startsAtom() && min <= 1000) {
        const a = this.parseAtom();
        left = { t: 'app', f: left, a };
        continue;
      }
      if (t.kind === 'sym' && t.v === '::') {
        if (min > 4) break;
        this.next();
        const ty = this.parseType(0);
        left = { t: 'constraint', e: left, ty };
        continue;
      }
      const opName = t.kind === 'sym' || (t.kind === 'id' && INFIX[t.v]) ? t.v : null;
      if (!opName) break;
      if (opName === '∨' && this.inCase > 0) break;
      const info = INFIX[opName];
      if (!info || info.prec < min) break;
      this.next();
      const rmin = info.assoc === 'r' ? info.prec : info.prec + 1;
      const right = this.parse(rmin);
      left = info.build(left, right);
      if (info.assoc === 'n') {
        const nt = this.peek();
        const nop = nt.kind === 'sym' || nt.kind === 'id' ? INFIX[nt.v] : undefined;
        if (nop && nop.prec === info.prec && nop.assoc === 'n' && min <= info.prec) this.fail('ambiguous non-associative operator');
      }
    }
    return left;
  }

  private parseBinderVars(): { x: string; ty?: PTy; pat?: PT }[] {
    const vs: { x: string; ty?: PTy; pat?: PT }[] = [];
    for (;;) {
      const t = this.peek();
      if (t.kind === 'id' && !KEYWORDS.has(t.v)) {
        this.next();
        let ty: PTy | undefined;
        if (this.isSym('::')) {
          this.next();
          ty = this.parseTypeAtomPostfixOrParen();
        }
        vs.push({ x: t.v, ty });
      } else if (t.kind === 'sym' && t.v === '_') {
        this.next();
        vs.push({ x: '_' });
      } else if (t.kind === 'sym' && t.v === '(') {
        // (x :: T) or tuple pattern (x, y)
        this.next();
        const items: { x: string; ty?: PTy }[] = [];
        for (;;) {
          const id = this.next();
          if (id.kind !== 'id' && !(id.kind === 'sym' && id.v === '_')) this.fail('variable expected in binder');
          let ty: PTy | undefined;
          if (this.isSym('::')) {
            this.next();
            ty = this.parseType(0);
          }
          items.push({ x: id.v, ty });
          if (this.isSym(',')) {
            this.next();
            continue;
          }
          break;
        }
        this.expectSym(')');
        if (items.length === 1) vs.push(items[0]);
        else {
          // tuple pattern: encoded as pat
          const pat = items
            .map((i): PT => (i.ty ? { t: 'constraint', e: { t: 'id', name: i.x }, ty: i.ty } : { t: 'id', name: i.x }))
            .reduceRight((acc, it) => app(C('Pair'), it, acc));
          vs.push({ x: '__pair', pat });
        }
      } else break;
    }
    if (vs.length === 0) this.fail('bound variable expected');
    return vs;
  }

  private parseTypeAtomPostfixOrParen(): PTy {
    return this.parseTypeAtomPostfix();
  }

  private parseQuant(q: string, bodyPrec: number): PT {
    const vs = this.parseBinderVars();
    // bounded quantifier  ∀x∈A. P
    let bound: { op: string; set: PT } | undefined;
    if (this.isSym('∈') || this.isSym(':')) {
      this.next();
      bound = { op: 'member', set: this.parse(51) };
    } else if (this.isSym('<') || this.isSym('≤') || this.isSym('>') || this.isSym('≥')) {
      const op = this.next().v;
      bound = { op, set: this.parse(51) };
    }
    this.expectSym('.');
    let body = this.parse(bodyPrec);
    for (let i = vs.length - 1; i >= 0; i--) {
      const v = vs[i];
      if (bound) {
        const x: PT = { t: 'id', name: v.x };
        const cond =
          bound.op === 'member'
            ? app(C('member'), x, bound.set)
            : bound.op === '<'
              ? app(C('less'), x, bound.set)
              : bound.op === '≤'
                ? app(C('less_eq'), x, bound.set)
                : bound.op === '>'
                  ? app(C('less'), bound.set, x)
                  : app(C('less_eq'), bound.set, x);
        body = q === 'Ex' ? app(C('conj'), cond, body) : app(C('imp'), cond, body);
      }
      if (v.pat) {
        if (q !== 'lambda') this.fail('tuple patterns only supported in λ');
        body = { t: 'abs', x: '__pair', body, pat: v.pat };
      } else if (q === 'lambda') body = { t: 'abs', x: v.x, ty: v.ty, body };
      else body = { t: 'q', q, x: v.x, ty: v.ty, body };
    }
    return body;
  }

  private parsePrefix(min: number): PT {
    const t = this.peek();
    if (t.kind === 'sym') {
      switch (t.v) {
        case '¬':
          this.next();
          return app(C('Not'), this.parse(40));
        case '-':
          this.next();
          return app(C('uminus'), this.parse(80));
        case '∀':
        case '!':
          this.next();
          return this.parseQuant('All', 10);
        case '∃':
        case '?':
          this.next();
          if (this.isSym('!')) {
            this.next();
            return this.parseQuant('Ex1', 10);
          }
          return this.parseQuant('Ex', 10);
        case 'λ':
          this.next();
          return this.parseQuant('lambda', 3);
        case '⋀':
          this.next();
          return this.parseQuant('!!', 0);
        case '⟦': {
          this.next();
          const prems: PT[] = [this.parse(0)];
          while (this.isSym(';')) {
            this.next();
            prems.push(this.parse(0));
          }
          this.expectSym('⟧');
          this.expectSym('⟹');
          const concl = this.parse(1);
          return prems.reduceRight((acc, p) => app(C('==>'), p, acc), concl);
        }
      }
    }
    if (t.kind === 'id') {
      if (t.v === 'ALL') {
        this.next();
        return this.parseQuant('All', 10);
      }
      if (t.v === 'EX') {
        this.next();
        return this.parseQuant('Ex', 10);
      }
      if (t.v === 'if') {
        this.next();
        const c = this.parse(0);
        if (!this.isKw('then')) this.fail('expected "then"');
        this.next();
        const a = this.parse(0);
        if (!this.isKw('else')) this.fail('expected "else"');
        this.next();
        const b = this.parse(10);
        return app(C('If'), c, a, b);
      }
      if (t.v === 'let') {
        this.next();
        const binds: { x: string; v: PT }[] = [];
        for (;;) {
          const id = this.next();
          if (id.kind !== 'id') this.fail('variable expected after let');
          this.expectSym('=');
          binds.push({ x: id.v, v: this.parse(0) });
          if (this.isSym(';')) {
            this.next();
            continue;
          }
          break;
        }
        if (!this.isKw('in')) this.fail('expected "in"');
        this.next();
        let body = this.parse(10);
        for (let i = binds.length - 1; i >= 0; i--) body = app(C('Let'), binds[i].v, { t: 'abs', x: binds[i].x, body });
        return body;
      }
      if (t.v === 'case') {
        this.next();
        const e = this.parse(0);
        if (!this.isKw('of')) this.fail('expected "of"');
        this.next();
        const clauses: { pat: PT; rhs: PT }[] = [];
        this.inCase++;
        for (;;) {
          const pat = this.parse(11);
          this.expectSym('⇒');
          const rhs = this.parse(11);
          clauses.push({ pat, rhs });
          if (this.isSym('∨')) {
            this.next();
            continue;
          }
          break;
        }
        this.inCase--;
        return { t: 'case', e, clauses };
      }
      if (t.v === 'SOME' || t.v === 'THE') {
        this.next();
        return this.parseQuant(t.v === 'SOME' ? 'Eps' : 'The', 10);
      }
    }
    void min;
    return this.parseAtom();
  }

  private parseAtom(): PT {
    const t = this.next();
    switch (t.kind) {
      case 'id':
        if (KEYWORDS.has(t.v) && t.v !== 'SOME' && t.v !== 'THE') {
          this.p--;
          this.fail('unexpected keyword');
        }
        if (t.v === 'SOME' || t.v === 'THE') {
          return this.parseQuant(t.v === 'SOME' ? 'Eps' : 'The', 10);
        }
        return { t: 'id', name: t.v };
      case 'num':
        return { t: 'num', n: Number(t.v) };
      case 'var':
        return { t: 'var', name: t.v };
      case 'sym':
        switch (t.v) {
          case '_':
            return { t: 'dummy' };
          case '...':
            return { t: 'dots' };
          case '(': {
            if (this.isSym(')')) {
              this.next();
              return C('Unity');
            }
            // operator section
            const s = this.peek();
            if (s.kind === 'sym' && SECTIONS[s.v] && this.isSym(')', 1)) {
              this.next();
              this.next();
              return C(SECTIONS[s.v]);
            }
            const save = this.inCase;
            this.inCase = 0;
            const items = [this.parse(0)];
            while (this.isSym(',')) {
              this.next();
              items.push(this.parse(0));
            }
            this.inCase = save;
            this.expectSym(')');
            return items.reduceRight((acc, it) => app(C('Pair'), it, acc));
          }
          case '[': {
            if (this.isSym(']')) {
              this.next();
              return C('Nil');
            }
            const save = this.inCase;
            this.inCase = 0;
            const first = this.parse(0);
            if (this.isSym('..<')) {
              this.next();
              const hi = this.parse(0);
              this.expectSym(']');
              this.inCase = save;
              return app(C('upt'), first, hi);
            }
            if (this.isSym('..')) {
              this.next();
              const hi = this.parse(0);
              this.expectSym(']');
              this.inCase = save;
              return app(C('upto'), first, hi);
            }
            const items = [first];
            while (this.isSym(',')) {
              this.next();
              items.push(this.parse(0));
            }
            this.inCase = save;
            this.expectSym(']');
            return items.reduceRight((acc, it) => app(C('Cons'), it, acc), C('Nil'));
          }
          case '{': {
            if (this.isSym('}')) {
              this.next();
              return C('bot_set');
            }
            // set comprehension {x. P}
            const p0 = this.p;
            const id = this.peek();
            if (id.kind === 'id' && (this.isSym('.', 1) || this.isSym('::', 1))) {
              this.next();
              let ty: PTy | undefined;
              if (this.isSym('::')) {
                this.next();
                ty = this.parseType(0);
              }
              if (this.isSym('.')) {
                this.next();
                const body = this.parse(0);
                this.expectSym('}');
                return app(C('Collect'), { t: 'abs', x: id.v, ty, body });
              }
              this.p = p0;
            }
            const items = [this.parse(0)];
            while (this.isSym(',')) {
              this.next();
              items.push(this.parse(0));
            }
            this.expectSym('}');
            return items.reduceRight((acc, it) => app(C('insert'), it, acc), C('bot_set'));
          }
          case '‹': {
            // cartouche inside term: treat content as nested term
            const start = this.p;
            let depth = 1;
            while (this.peek().kind !== 'eof') {
              if (this.isSym('‹')) depth++;
              if (this.isSym('›')) {
                depth--;
                if (depth === 0) break;
              }
              this.next();
            }
            void start;
            this.fail('cartouche not allowed in term');
          }
        }
    }
    this.p--;
    this.fail('term expected');
  }
}

export function parseTerm(s: string): PT {
  return new InnerParser(s).parseTermAll();
}

export function parseType(s: string): PTy {
  return new InnerParser(s).parseTypeAll();
}
