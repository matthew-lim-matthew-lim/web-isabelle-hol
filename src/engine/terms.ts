// Core term and type representation (simply-typed lambda calculus, de Bruijn indices).

export type Type =
  | { k: 'T'; name: string; args: Type[] } // type constructor application
  | { k: 'V'; name: string } // fixed type variable, e.g. 'a
  | { k: 'S'; id: number }; // schematic / inference type variable

export type Term =
  | { k: 'C'; name: string; ty: Type } // constant
  | { k: 'F'; name: string; ty: Type } // free variable
  | { k: 'V'; name: string; ty: Type } // schematic variable ?x
  | { k: 'B'; i: number } // bound variable (de Bruijn)
  | { k: 'L'; x: string; ty: Type; body: Term } // abstraction
  | { k: 'A'; f: Term; a: Term }; // application

export class EngineError extends Error {
  constructor(message: string) {
    super(message);
  }
}

// ---------- types ----------
export const tcon = (name: string, args: Type[] = []): Type => ({ k: 'T', name, args });
export const tvar = (name: string): Type => ({ k: 'V', name });
let tsCounter = 0;
export const freshTS = (): Type => ({ k: 'S', id: ++tsCounter });
export const boolT = tcon('bool');
export const natT = tcon('nat');
export const intT = tcon('int');
export const funT = (a: Type, b: Type): Type => tcon('fun', [a, b]);
export const listT = (a: Type): Type => tcon('list', [a]);
export const setT = (a: Type): Type => tcon('set', [a]);
export const prodT = (a: Type, b: Type): Type => tcon('prod', [a, b]);
export const funTs = (args: Type[], res: Type): Type => args.reduceRight((acc, a) => funT(a, acc), res);

export function isFunT(t: Type): t is { k: 'T'; name: string; args: Type[] } {
  return t.k === 'T' && t.name === 'fun';
}
export function domT(t: Type): Type {
  if (!isFunT(t)) throw new EngineError('domT: not a function type');
  return t.args[0];
}
export function ranT(t: Type): Type {
  if (!isFunT(t)) throw new EngineError('ranT: not a function type');
  return t.args[1];
}
export function stripFunT(t: Type): { args: Type[]; res: Type } {
  const args: Type[] = [];
  while (isFunT(t)) {
    args.push(t.args[0]);
    t = t.args[1];
  }
  return { args, res: t };
}

export function typeEq(a: Type, b: Type): boolean {
  if (a === b) return true;
  if (a.k !== b.k) return false;
  if (a.k === 'T') {
    const bb = b as typeof a;
    if (a.name !== bb.name || a.args.length !== bb.args.length) return false;
    return a.args.every((x, i) => typeEq(x, bb.args[i]));
  }
  if (a.k === 'V') return a.name === (b as typeof a).name;
  return a.id === (b as typeof a).id;
}

export type TSubst = Map<number, Type>;

export function tsubst(t: Type, s: TSubst): Type {
  if (s.size === 0) return t;
  switch (t.k) {
    case 'S': {
      const r = s.get(t.id);
      return r ? tsubst(r, s) : t;
    }
    case 'V':
      return t;
    case 'T': {
      if (t.args.length === 0) return t;
      let changed = false;
      const args = t.args.map((a) => {
        const r = tsubst(a, s);
        if (r !== a) changed = true;
        return r;
      });
      return changed ? { k: 'T', name: t.name, args } : t;
    }
  }
}

export function tOccurs(id: number, t: Type, s: TSubst): boolean {
  t = tsubst(t, s);
  if (t.k === 'S') return t.id === id;
  if (t.k === 'T') return t.args.some((a) => tOccurs(id, a, s));
  return false;
}

/** Unify two types, extending s in place. Returns false on clash. */
export function tunify(a: Type, b: Type, s: TSubst): boolean {
  a = tsubst(a, s);
  b = tsubst(b, s);
  if (a.k === 'S') {
    if (b.k === 'S' && b.id === a.id) return true;
    if (tOccurs(a.id, b, s)) return false;
    s.set(a.id, b);
    return true;
  }
  if (b.k === 'S') return tunify(b, a, s);
  if (a.k === 'V' || b.k === 'V') return a.k === b.k && (a as { name: string }).name === (b as { name: string }).name;
  if (a.name !== b.name || a.args.length !== b.args.length) return false;
  for (let i = 0; i < a.args.length; i++) if (!tunify(a.args[i], b.args[i], s)) return false;
  return true;
}

export function tmapV(t: Type, f: (name: string) => Type): Type {
  if (t.k === 'V') return f(t.name);
  if (t.k === 'T' && t.args.length) return { k: 'T', name: t.name, args: t.args.map((a) => tmapV(a, f)) };
  return t;
}

export function tvarsOf(t: Type, acc: Set<string> = new Set()): Set<string> {
  if (t.k === 'V') acc.add(t.name);
  else if (t.k === 'T') t.args.forEach((a) => tvarsOf(a, acc));
  return acc;
}
export function tsvarsOf(t: Type, acc: Set<number> = new Set()): Set<number> {
  if (t.k === 'S') acc.add(t.id);
  else if (t.k === 'T') t.args.forEach((a) => tsvarsOf(a, acc));
  return acc;
}

// ---------- terms ----------
export const mkC = (name: string, ty: Type): Term => ({ k: 'C', name, ty });
export const mkF = (name: string, ty: Type): Term => ({ k: 'F', name, ty });
export const mkV = (name: string, ty: Type): Term => ({ k: 'V', name, ty });
export const mkB = (i: number): Term => ({ k: 'B', i });
export const mkL = (x: string, ty: Type, body: Term): Term => ({ k: 'L', x, ty, body });
export const mkA = (f: Term, a: Term): Term => ({ k: 'A', f, a });
export const mkApps = (f: Term, args: Term[]): Term => args.reduce((acc, a) => mkA(acc, a), f);

export function stripApp(t: Term): { head: Term; args: Term[] } {
  const args: Term[] = [];
  while (t.k === 'A') {
    args.push(t.a);
    t = t.f;
  }
  args.reverse();
  return { head: t, args };
}

export function headName(t: Term): string | null {
  const h = stripApp(t).head;
  if (h.k === 'C') return h.name;
  return null;
}

export function isConst(t: Term, name: string): boolean {
  return t.k === 'C' && t.name === name;
}

/** Matches `c a1 .. an` exactly with n args, returning args. */
export function destApp(t: Term, name: string, n: number): Term[] | null {
  const args: Term[] = [];
  for (let i = 0; i < n; i++) {
    if (t.k !== 'A') return null;
    args.push(t.a);
    t = t.f;
  }
  if (t.k !== 'C' || t.name !== name) return null;
  return args.reverse();
}

export function termEq(a: Term, b: Term): boolean {
  if (a === b) return true;
  if (a.k !== b.k) return false;
  switch (a.k) {
    case 'C':
    case 'F':
    case 'V': {
      const bb = b as typeof a;
      return a.name === bb.name && (a.k !== 'C' || typeEq(a.ty, bb.ty));
    }
    case 'B':
      return a.i === (b as typeof a).i;
    case 'L':
      return termEq(a.body, (b as typeof a).body);
    case 'A':
      return termEq(a.f, (b as typeof a).f) && termEq(a.a, (b as typeof a).a);
  }
}

/** Structural key, used for hashing / atom identification. Ignores type annotations on frees. */
export function typeKey(t: Type): string {
  switch (t.k) {
    case 'V':
      return t.name;
    case 'S':
      return '?' + t.id;
    case 'T':
      return t.args.length ? t.name + '(' + t.args.map(typeKey).join(',') + ')' : t.name;
  }
}

export function termKey(t: Term): string {
  switch (t.k) {
    case 'C':
      return t.name + ':' + typeKey(t.ty);
    case 'F':
      return '$' + t.name;
    case 'V':
      return '?' + t.name;
    case 'B':
      return '#b' + t.i;
    case 'L':
      return '(\\' + termKey(t.body) + ')';
    case 'A': {
      const { head, args } = stripApp(t);
      return '(' + termKey(head) + ' ' + args.map(termKey).join(' ') + ')';
    }
  }
}

export function hasLooseBound(t: Term, lev = 0): boolean {
  switch (t.k) {
    case 'B':
      return t.i >= lev;
    case 'L':
      return hasLooseBound(t.body, lev + 1);
    case 'A':
      return hasLooseBound(t.f, lev) || hasLooseBound(t.a, lev);
    default:
      return false;
  }
}

export function looseBoundAt(t: Term, i: number, lev = 0): boolean {
  switch (t.k) {
    case 'B':
      return t.i === i + lev;
    case 'L':
      return looseBoundAt(t.body, i, lev + 1);
    case 'A':
      return looseBoundAt(t.f, i, lev) || looseBoundAt(t.a, i, lev);
    default:
      return false;
  }
}

/** Increment loose bound indices >= lev by inc. */
export function incrBound(t: Term, inc: number, lev = 0): Term {
  if (inc === 0) return t;
  switch (t.k) {
    case 'B':
      return t.i >= lev ? mkB(t.i + inc) : t;
    case 'L':
      return mkL(t.x, t.ty, incrBound(t.body, inc, lev + 1));
    case 'A':
      return mkA(incrBound(t.f, inc, lev), incrBound(t.a, inc, lev));
    default:
      return t;
  }
}

/** Substitute u for Bound lev in body (body is the body of an abstraction). */
export function substBound(body: Term, u: Term, lev = 0): Term {
  switch (body.k) {
    case 'B':
      if (body.i === lev) return incrBound(u, lev);
      if (body.i > lev) return mkB(body.i - 1);
      return body;
    case 'L':
      return mkL(body.x, body.ty, substBound(body.body, u, lev + 1));
    case 'A':
      return mkA(substBound(body.f, u, lev), substBound(body.a, u, lev));
    default:
      return body;
  }
}

/** Abstract over occurrences of term v (a free or var) producing body for a lambda. */
export function abstractOver(t: Term, v: Term, lev = 0): Term {
  if (termEq(t, v)) return mkB(lev);
  switch (t.k) {
    case 'L':
      return mkL(t.x, t.ty, abstractOver(t.body, v, lev + 1));
    case 'A':
      return mkA(abstractOver(t.f, v, lev), abstractOver(t.a, v, lev));
    default:
      return t;
  }
}

export function lambda(v: Term & { name: string; ty: Type }, body: Term): Term {
  return mkL(v.name, v.ty, abstractOver(body, v));
}

export function betaNorm(t: Term): Term {
  switch (t.k) {
    case 'A': {
      const f = betaNorm(t.f);
      const a = betaNorm(t.a);
      if (f.k === 'L') return betaNorm(substBound(f.body, a));
      if (f === t.f && a === t.a) return t;
      return mkA(f, a);
    }
    case 'L': {
      const b = betaNorm(t.body);
      return b === t.body ? t : mkL(t.x, t.ty, b);
    }
    default:
      return t;
  }
}

export function typeOf(t: Term, env: Type[] = []): Type {
  switch (t.k) {
    case 'C':
    case 'F':
    case 'V':
      return t.ty;
    case 'B': {
      const ty = env[env.length - 1 - t.i];
      if (!ty) throw new EngineError('typeOf: loose bound variable');
      return ty;
    }
    case 'L':
      return funT(t.ty, typeOf(t.body, [...env, t.ty]));
    case 'A': {
      const ft = typeOf(t.f, env);
      if (isFunT(ft)) return ft.args[1];
      throw new EngineError('typeOf: application of non-function');
    }
  }
}

export function mapTypes(t: Term, f: (ty: Type) => Type): Term {
  switch (t.k) {
    case 'C':
    case 'F':
    case 'V':
      return { ...t, ty: f(t.ty) };
    case 'B':
      return t;
    case 'L':
      return mkL(t.x, f(t.ty), mapTypes(t.body, f));
    case 'A':
      return mkA(mapTypes(t.f, f), mapTypes(t.a, f));
  }
}

export function frees(t: Term, acc: Map<string, Term> = new Map()): Map<string, Term> {
  switch (t.k) {
    case 'F':
      if (!acc.has(t.name)) acc.set(t.name, t);
      break;
    case 'L':
      frees(t.body, acc);
      break;
    case 'A':
      frees(t.f, acc);
      frees(t.a, acc);
      break;
  }
  return acc;
}

export function vars(t: Term, acc: Map<string, Term> = new Map()): Map<string, Term> {
  switch (t.k) {
    case 'V':
      if (!acc.has(t.name)) acc.set(t.name, t);
      break;
    case 'L':
      vars(t.body, acc);
      break;
    case 'A':
      vars(t.f, acc);
      vars(t.a, acc);
      break;
  }
  return acc;
}

export function occursFree(name: string, t: Term): boolean {
  switch (t.k) {
    case 'F':
      return t.name === name;
    case 'L':
      return occursFree(name, t.body);
    case 'A':
      return occursFree(name, t.f) || occursFree(name, t.a);
    default:
      return false;
  }
}

export function occursTerm(sub: Term, t: Term): boolean {
  if (termEq(sub, t)) return true;
  if (t.k === 'L') return occursTerm(sub, t.body);
  if (t.k === 'A') return occursTerm(sub, t.f) || occursTerm(sub, t.a);
  return false;
}

/** Replace free variables by name. */
export function substFrees(t: Term, m: Map<string, Term>): Term {
  if (m.size === 0) return t;
  switch (t.k) {
    case 'F': {
      const r = m.get(t.name);
      return r ?? t;
    }
    case 'L':
      return mkL(t.x, t.ty, substFrees(t.body, m));
    case 'A':
      return mkA(substFrees(t.f, m), substFrees(t.a, m));
    default:
      return t;
  }
}

/** Replace subterm occurrences. */
export function replaceTerm(t: Term, from: Term, to: Term): Term {
  if (termEq(t, from)) return to;
  switch (t.k) {
    case 'L':
      return mkL(t.x, t.ty, replaceTerm(t.body, from, to));
    case 'A':
      return mkA(replaceTerm(t.f, from, to), replaceTerm(t.a, from, to));
    default:
      return t;
  }
}

export function termSize(t: Term): number {
  switch (t.k) {
    case 'L':
      return 1 + termSize(t.body);
    case 'A':
      return termSize(t.f) + termSize(t.a);
    default:
      return 1;
  }
}

// ---------- logical constants ----------
export const TRUE = mkC('True', boolT);
export const FALSE = mkC('False', boolT);
const bbb = funT(boolT, funT(boolT, boolT));
export const mkNot = (a: Term): Term => mkA(mkC('Not', funT(boolT, boolT)), a);
export const mkConj = (a: Term, b: Term): Term => mkApps(mkC('conj', bbb), [a, b]);
export const mkDisj = (a: Term, b: Term): Term => mkApps(mkC('disj', bbb), [a, b]);
export const mkImp = (a: Term, b: Term): Term => mkApps(mkC('imp', bbb), [a, b]);
export const mkMetaImp = (a: Term, b: Term): Term => mkApps(mkC('==>', bbb), [a, b]);
export function mkEq(a: Term, b: Term, ty?: Type): Term {
  const t = ty ?? typeOfSafe(a);
  return mkApps(mkC('eq', funT(t, funT(t, boolT))), [a, b]);
}
export function mkAll(v: Term & { name: string; ty: Type }, body: Term, q = 'All'): Term {
  return mkA(mkC(q, funT(funT(v.ty, boolT), boolT)), lambda(v, body));
}
export function mkEx(v: Term & { name: string; ty: Type }, body: Term): Term {
  return mkAll(v, body, 'Ex');
}
export function mkMetaAll(v: Term & { name: string; ty: Type }, body: Term): Term {
  return mkAll(v, body, '!!');
}
export function typeOfSafe(t: Term): Type {
  try {
    return typeOf(t);
  } catch {
    return freshTS();
  }
}

export function conjs(ts: Term[]): Term {
  if (ts.length === 0) return TRUE;
  return ts.slice(0, -1).reduceRight((acc, t) => mkConj(t, acc), ts[ts.length - 1]);
}

export function destConj(t: Term): Term[] {
  const c = destApp(t, 'conj', 2);
  if (c) return [...destConj(c[0]), ...destConj(c[1])];
  return [t];
}

export function mkNum(n: number, ty: Type): Term {
  return mkC('#' + n, ty);
}
export function numVal(t: Term): number | null {
  if (t.k === 'C' && t.name.charCodeAt(0) === 35 /* # */) return Number(t.name.slice(1));
  return null;
}

export function mkSuc(t: Term): Term {
  return mkA(mkC('Suc', funT(natT, natT)), t);
}

/** Fresh name not in used, Isabelle style: x, xa, xb, ... */
export function variant(name: string, used: Set<string>): string {
  if (!used.has(name)) return name;
  const base = name.replace(/_+$/, '');
  const suffixes = 'abcdefghijklmnopqrstuvwxyz';
  for (let i = 0; ; i++) {
    let s = '';
    let n = i;
    do {
      s = suffixes[n % 26] + s;
      n = Math.floor(n / 26) - 1;
    } while (n >= 0);
    const cand = base + s;
    if (!used.has(cand)) return cand;
  }
}

let nameCounter = 0;
export function freshId(): number {
  return ++nameCounter;
}
