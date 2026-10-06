// Polynomial normalisation and a linear arithmetic decision procedure (Fourier-Motzkin with integer tightening).
import {
  Term,
  Type,
  stripApp,
  numVal,
  termKey,
  mkC,
  mkApps,
  funT,
  typeOf,
  natT,
  intT,
  typeEq,
  destApp,
  boolT,
  isConst,
} from './terms';

export interface Mono {
  coeff: number;
  atoms: Term[]; // sorted by key, with repetition
  key: string;
}
export type Poly = Map<string, Mono>; // '' is the constant monomial

const isNat = (ty: Type) => ty.k === 'T' && ty.name === 'nat';
const isInt = (ty: Type) => ty.k === 'T' && ty.name === 'int';
export const isArithType = (ty: Type) => isNat(ty) || isInt(ty);

function monoKey(atoms: Term[]) {
  return atoms.map(termKey).join('*');
}

export function polyConst(c: number): Poly {
  const p: Poly = new Map();
  if (c !== 0) p.set('', { coeff: c, atoms: [], key: '' });
  return p;
}
function polyAtom(t: Term): Poly {
  const k = termKey(t);
  return new Map([[k, { coeff: 1, atoms: [t], key: k }]]);
}
export function polyAdd(a: Poly, b: Poly, sign = 1): Poly {
  const r: Poly = new Map(a);
  for (const [k, m] of b) {
    const ex = r.get(k);
    const c = (ex ? ex.coeff : 0) + sign * m.coeff;
    if (c === 0) r.delete(k);
    else r.set(k, { coeff: c, atoms: m.atoms, key: k });
  }
  return r;
}
export function polyMul(a: Poly, b: Poly): Poly {
  let r: Poly = new Map();
  for (const ma of a.values())
    for (const mb of b.values()) {
      const atoms = [...ma.atoms, ...mb.atoms].sort((x, y) => (termKey(x) < termKey(y) ? -1 : termKey(x) > termKey(y) ? 1 : 0));
      const k = monoKey(atoms);
      r = polyAdd(r, new Map([[k, { coeff: ma.coeff * mb.coeff, atoms, key: k }]]));
    }
  return r;
}
export function polyIsConst(p: Poly): number | null {
  if (p.size === 0) return 0;
  if (p.size === 1 && p.has('')) return p.get('')!.coeff;
  return null;
}
export function polyEq(a: Poly, b: Poly): boolean {
  return polyAdd(a, b, -1).size === 0;
}

/** Convert a term of type nat/int to a polynomial. Non-arithmetic subterms become atoms. */
export function toPoly(t: Term, ty: Type): Poly {
  const v = numVal(t);
  if (v !== null) return polyConst(v);
  const { head, args } = stripApp(t);
  if (head.k === 'C') {
    switch (head.name) {
      case 'Suc':
        if (args.length === 1) return polyAdd(toPoly(args[0], ty), polyConst(1));
        break;
      case 'plus':
        if (args.length === 2) return polyAdd(toPoly(args[0], ty), toPoly(args[1], ty));
        break;
      case 'times':
        if (args.length === 2) return polyMul(toPoly(args[0], ty), toPoly(args[1], ty));
        break;
      case 'minus':
        if (args.length === 2) {
          if (isInt(ty)) return polyAdd(toPoly(args[0], ty), toPoly(args[1], ty), -1);
          const a = polyIsConst(toPoly(args[0], ty));
          const b = polyIsConst(toPoly(args[1], ty));
          if (a !== null && b !== null) return polyConst(Math.max(0, a - b));
          const pb = toPoly(args[1], ty);
          if (polyIsConst(pb) === 0) return toPoly(args[0], ty);
        }
        break;
      case 'uminus':
        if (args.length === 1 && isInt(ty)) return polyAdd(new Map(), toPoly(args[0], ty), -1);
        break;
      case 'power':
        if (args.length === 2) {
          const e = numVal(args[1]);
          if (e !== null && e <= 8) {
            let r = polyConst(1);
            const b = toPoly(args[0], ty);
            for (let i = 0; i < e; i++) r = polyMul(r, b);
            return r;
          }
        }
        break;
    }
  }
  return polyAtom(t);
}

function sortedMonos(p: Poly): Mono[] {
  return [...p.values()].sort((a, b) => {
    if (a.key === '') return 1;
    if (b.key === '') return -1;
    if (a.atoms.length !== b.atoms.length) return b.atoms.length - a.atoms.length;
    return a.key < b.key ? -1 : a.key > b.key ? 1 : 0;
  });
}

/** Build a term from a polynomial with non-negative coefficients. */
export function fromPoly(p: Poly, ty: Type): Term {
  const plus = mkC('plus', funT(ty, funT(ty, ty)));
  const times = mkC('times', funT(ty, funT(ty, ty)));
  const minus = mkC('minus', funT(ty, funT(ty, ty)));
  const monos = sortedMonos(p);
  if (monos.length === 0) return mkC('#0', ty);
  const monoTerm = (m: Mono, abs: boolean): Term => {
    const c = abs ? Math.abs(m.coeff) : m.coeff;
    if (m.atoms.length === 0) return c < 0 ? mkApps(mkC('uminus', funT(ty, ty)), [mkC('#' + -c, ty)]) : mkC('#' + c, ty);
    let t = m.atoms[0];
    for (let i = 1; i < m.atoms.length; i++) t = mkApps(times, [t, m.atoms[i]]);
    if (c === 1) return t;
    if (c < 0) return mkApps(mkC('uminus', funT(ty, ty)), [c === -1 ? t : mkApps(times, [mkC('#' + -c, ty), t])]);
    return mkApps(times, [mkC('#' + c, ty), t]);
  };
  let t = monoTerm(monos[0], false);
  for (let i = 1; i < monos.length; i++) {
    const m = monos[i];
    if (m.coeff < 0) t = mkApps(minus, [t, monoTerm(m, true)]);
    else t = mkApps(plus, [t, monoTerm(m, false)]);
  }
  return t;
}

// -------------------- linear arithmetic --------------------

interface Lin {
  c: Map<string, number>; // variable coefficients
  k: number; // constant;  meaning: sum c_i x_i + k  (<= 0 | = 0)
  eq: boolean;
}

interface Atoms {
  natVars: Set<string>; // monomials known to be >= 0
  extra: Term[]; // generated facts for minus/div/mod atoms
  seen: Set<string>;
}

const relNames = new Set(['less', 'less_eq', 'eq']);

function relOf(t: Term): { rel: string; a: Term; b: Term; ty: Type } | null {
  const { head, args } = stripApp(t);
  if (head.k !== 'C' || !relNames.has(head.name) || args.length !== 2) return null;
  let ty: Type;
  try {
    ty = typeOf(args[0]);
  } catch {
    return null;
  }
  if (!isArithType(ty)) return null;
  return { rel: head.name, a: args[0], b: args[1], ty };
}

export function isArithRel(t: Term): boolean {
  if (isConst(stripApp(t).head, 'Not') && t.k === 'A') return relOf(t.a) !== null;
  return relOf(t) !== null;
}

function gcd(a: number, b: number): number {
  a = Math.abs(a);
  b = Math.abs(b);
  while (b) [a, b] = [b, a % b];
  return a;
}

function linFromPoly(p: Poly, ty: Type, at: Atoms): { c: Map<string, number>; k: number } {
  const c = new Map<string, number>();
  let k = 0;
  for (const m of p.values()) {
    if (m.key === '') {
      k += m.coeff;
      continue;
    }
    c.set(m.key, (c.get(m.key) ?? 0) + m.coeff);
    if (isNat(ty)) at.natVars.add(m.key);
    // nat subtraction / div / mod atoms produce side facts
    for (const a of m.atoms) registerAtom(a, ty, at);
  }
  return { c, k };
}

function registerAtom(a: Term, ty: Type, at: Atoms) {
  const key = termKey(a);
  if (at.seen.has(key)) return;
  at.seen.add(key);
  const minus = destApp(a, 'minus', 2);
  const nat = isNat(ty);
  const T = (n: number) => mkC('#' + n, ty);
  const op = (name: string, rt: Type = ty) => mkC(name, funT(ty, funT(ty, rt)));
  if (minus && nat) {
    // (b <= a --> d + b = a) & (a < b --> d = 0)
    const [x, y] = minus;
    at.extra.push(
      mkApps(mkC('disj', funT(boolT, funT(boolT, boolT))), [
        mkApps(mkC('conj', funT(boolT, funT(boolT, boolT))), [
          mkApps(op('less_eq', boolT), [y, x]),
          mkApps(op('eq', boolT), [mkApps(op('plus'), [a, y]), x]),
        ]),
        mkApps(mkC('conj', funT(boolT, funT(boolT, boolT))), [mkApps(op('less', boolT), [x, y]), mkApps(op('eq', boolT), [a, T(0)])]),
      ]),
    );
  }
  const dv = destApp(a, 'div', 2);
  const md = destApp(a, 'mod', 2);
  if (dv || md) {
    const [x, y] = (dv ?? md)!;
    const k = numVal(y);
    if (k !== null && k > 0) {
      const q = mkApps(op('div'), [x, y]);
      const r = mkApps(op('mod'), [x, y]);
      at.extra.push(mkApps(op('eq', boolT), [mkApps(op('plus'), [mkApps(op('times'), [T(k), q]), r]), x]));
      at.extra.push(mkApps(op('less', boolT), [r, T(k)]));
      at.extra.push(mkApps(op('less_eq', boolT), [T(0), r]));
      if (nat) {
        at.seen.add(termKey(q));
        at.seen.add(termKey(r));
      }
    }
  }
  const mx = destApp(a, 'max', 2);
  const mn = destApp(a, 'min', 2);
  if (mx || mn) {
    const [x, y] = (mx ?? mn)!;
    const le = mkApps(op('less_eq', boolT), [x, y]);
    const conj = (p: Term, q: Term) => mkApps(mkC('conj', funT(boolT, funT(boolT, boolT))), [p, q]);
    const not = (p: Term) => mkApps(mkC('Not', funT(boolT, boolT)), [p]);
    const eqT = (p: Term, q: Term) => mkApps(op('eq', boolT), [p, q]);
    at.extra.push(
      mkApps(mkC('disj', funT(boolT, funT(boolT, boolT))), [
        conj(le, eqT(a, mx ? y : x)),
        conj(not(le), eqT(a, mx ? x : y)),
      ]),
    );
  }
  const ab = destApp(a, 'abs', 1);
  if (ab) {
    const x = ab[0];
    const le0 = mkApps(op('less_eq', boolT), [T(0), x]);
    const conj = (p: Term, q: Term) => mkApps(mkC('conj', funT(boolT, funT(boolT, boolT))), [p, q]);
    const not = (p: Term) => mkApps(mkC('Not', funT(boolT, boolT)), [p]);
    at.extra.push(
      mkApps(mkC('disj', funT(boolT, funT(boolT, boolT))), [
        conj(le0, mkApps(op('eq', boolT), [a, x])),
        conj(not(le0), mkApps(op('eq', boolT), [a, mkApps(mkC('uminus', funT(ty, ty)), [x])])),
      ]),
    );
  }
}

// literal: arithmetic relation, possibly negated -> list of alternative constraint sets (disjunction)
function litToLins(rel: { rel: string; a: Term; b: Term; ty: Type }, positive: boolean, at: Atoms): Lin[][] {
  const pa = toPoly(rel.a, rel.ty);
  const pb = toPoly(rel.b, rel.ty);
  const d = linFromPoly(polyAdd(pa, pb, -1), rel.ty, at); // a - b
  const neg = (l: { c: Map<string, number>; k: number }) => ({ c: new Map([...l.c].map(([k, v]) => [k, -v])), k: -l.k });
  const mk = (l: { c: Map<string, number>; k: number }, eq: boolean): Lin => ({ c: l.c, k: l.k, eq });
  const plus1 = (l: { c: Map<string, number>; k: number }) => ({ c: l.c, k: l.k + 1 });
  if (rel.rel === 'eq') {
    if (positive) return [[mk(d, true)]];
    // a < b  or  b < a
    return [[mk(plus1(d), false)], [mk(plus1(neg(d)), false)]];
  }
  if (rel.rel === 'less_eq') {
    if (positive) return [[mk(d, false)]]; // a - b <= 0
    return [[mk(plus1(neg(d)), false)]]; // b < a: b - a + 1 <= 0
  }
  // less
  if (positive) return [[mk(plus1(d), false)]];
  return [[mk(neg(d), false)]]; // b <= a
}

const MAX_BRANCHES = 256;

/** Decide whether hyps ⊢ concl by linear arithmetic (refutation of hyps ∧ ¬concl). */
export function linarith(hyps: Term[], concl: Term | null): boolean {
  const at: Atoms = { natVars: new Set(), extra: [], seen: new Set() };
  const facts: { t: Term; pos: boolean }[] = hyps.map((h) => ({ t: h, pos: true }));
  if (concl) facts.push({ t: concl, pos: false });
  let branches = 0;
  const bconj = (t: Term) => destApp(t, 'conj', 2);
  const bdisj = (t: Term) => destApp(t, 'disj', 2);
  const bimp = (t: Term) => destApp(t, 'imp', 2) ?? destApp(t, '==>', 2);
  const bnot = (t: Term) => destApp(t, 'Not', 1);

  // DFS over the formula structure collecting constraints
  const solve = (todo: { t: Term; pos: boolean }[], lins: Lin[], lits: Map<string, boolean>, extraDone: number): boolean => {
    // returns true if the branch is refuted
    if (++branches > MAX_BRANCHES * 8) return false;
    while (todo.length) {
      const { t, pos } = todo.shift()!;
      if (isConst(t, 'True')) {
        if (!pos) return true;
        continue;
      }
      if (isConst(t, 'False')) {
        if (pos) return true;
        continue;
      }
      const n = bnot(t);
      if (n) {
        todo.unshift({ t: n[0], pos: !pos });
        continue;
      }
      const c = bconj(t);
      if (c) {
        if (pos) todo.unshift({ t: c[0], pos: true }, { t: c[1], pos: true });
        else return solve([{ t: c[0], pos: false }, ...todo], [...lins], new Map(lits), extraDone) && solve([{ t: c[1], pos: false }, ...todo], [...lins], new Map(lits), extraDone);
        continue;
      }
      const d = bdisj(t);
      if (d) {
        if (!pos) todo.unshift({ t: d[0], pos: false }, { t: d[1], pos: false });
        else return solve([{ t: d[0], pos: true }, ...todo], [...lins], new Map(lits), extraDone) && solve([{ t: d[1], pos: true }, ...todo], [...lins], new Map(lits), extraDone);
        continue;
      }
      const im = bimp(t);
      if (im) {
        if (!pos) todo.unshift({ t: im[0], pos: true }, { t: im[1], pos: false });
        else return solve([{ t: im[0], pos: false }, ...todo], [...lins], new Map(lits), extraDone) && solve([{ t: im[1], pos: true }, ...todo], [...lins], new Map(lits), extraDone);
        continue;
      }
      const r = relOf(t);
      if (r) {
        const alts = litToLins(r, pos, at);
        if (alts.length === 1) lins.push(...alts[0]);
        else {
          return alts.every((alt) => solve([...todo], [...lins, ...alt], new Map(lits), extraDone));
        }
        continue;
      }
      // bool equality as iff
      const eq = destApp(t, 'eq', 2);
      if (eq && typeEqSafe(eq[0], boolT)) {
        const [a, b] = eq;
        const both = { t: mkConjT(a, b), pos: true };
        const neither = { t: mkConjT(mkNotT(a), mkNotT(b)), pos: true };
        if (pos) return solve([both, ...todo], [...lins], new Map(lits), extraDone) && solve([neither, ...todo], [...lins], new Map(lits), extraDone);
        const one = { t: mkConjT(a, mkNotT(b)), pos: true };
        const other = { t: mkConjT(mkNotT(a), b), pos: true };
        return solve([one, ...todo], [...lins], new Map(lits), extraDone) && solve([other, ...todo], [...lins], new Map(lits), extraDone);
      }
      // propositional atom
      const key = termKey(t);
      const prev = lits.get(key);
      if (prev !== undefined && prev !== pos) return true;
      lits.set(key, pos);
    }
    // side facts from atoms (minus, div, mod)
    if (extraDone < at.extra.length) {
      const more = at.extra.slice(extraDone).map((t) => ({ t, pos: true }));
      return solve(more, lins, lits, at.extra.length);
    }
    const all = [...lins];
    for (const v of at.natVars) all.push({ c: new Map([[v, -1]]), k: 0, eq: false });
    return fourierMotzkin(all);
  };
  return solve(facts, [], new Map(), 0);
}

function typeEqSafe(t: Term, ty: Type) {
  try {
    return typeEq(typeOf(t), ty);
  } catch {
    return false;
  }
}
const mkConjT = (a: Term, b: Term) => mkApps(mkC('conj', funT(boolT, funT(boolT, boolT))), [a, b]);
const mkNotT = (a: Term) => mkApps(mkC('Not', funT(boolT, boolT)), [a]);

function normalizeLin(l: Lin): Lin | 'false' | 'true' {
  for (const [k, v] of l.c) if (v === 0) l.c.delete(k);
  if (l.c.size === 0) {
    if (l.eq) return l.k === 0 ? 'true' : 'false';
    return l.k <= 0 ? 'true' : 'false';
  }
  let g = 0;
  for (const v of l.c.values()) g = gcd(g, v);
  if (g > 1) {
    const c = new Map<string, number>();
    for (const [k, v] of l.c) c.set(k, v / g);
    if (l.eq) {
      if (l.k % g !== 0) return 'false';
      return { c, k: l.k / g, eq: true };
    }
    // sum (v/g) x + k/g <= 0  ->  sum (v/g) x <= -k/g -> floor
    return { c, k: -Math.floor(-l.k / g), eq: false };
  }
  return l;
}

export function fourierMotzkin(input: Lin[]): boolean {
  let cs: Lin[] = [];
  for (const l of input) {
    const n = normalizeLin({ c: new Map(l.c), k: l.k, eq: l.eq });
    if (n === 'false') return true;
    if (n !== 'true') cs.push(n);
  }
  // eliminate equalities
  for (;;) {
    const ei = cs.findIndex((l) => l.eq);
    if (ei < 0) break;
    const e = cs[ei];
    // choose variable with smallest abs coefficient
    let best: string | null = null;
    for (const [k, v] of e.c) if (best === null || Math.abs(v) < Math.abs(e.c.get(best)!)) best = k;
    const x = best!;
    let a = e.c.get(x)!;
    let ee = e;
    if (a < 0) {
      ee = { c: new Map([...e.c].map(([k, v]) => [k, -v])), k: -e.k, eq: true };
      a = -a;
    }
    const next: Lin[] = [];
    for (let i = 0; i < cs.length; i++) {
      if (i === ei) continue;
      const l = cs[i];
      const b = l.c.get(x) ?? 0;
      if (b === 0) {
        next.push(l);
        continue;
      }
      // a*l - b*ee  (a > 0 keeps direction)
      const c = new Map<string, number>();
      for (const [k, v] of l.c) c.set(k, a * v);
      for (const [k, v] of ee.c) c.set(k, (c.get(k) ?? 0) - b * v);
      c.delete(x);
      const n = normalizeLin({ c, k: a * l.k - b * ee.k, eq: l.eq });
      if (n === 'false') return true;
      if (n !== 'true') next.push(n);
    }
    // note: equality with |a| > 1 loses integrality info; still sound over rationals
    cs = next;
  }
  // inequalities
  let rounds = 0;
  while (cs.length) {
    if (++rounds > 60 || cs.length > 3000) return false;
    const vars = new Map<string, { pos: number; neg: number }>();
    for (const l of cs)
      for (const [k, v] of l.c) {
        const e = vars.get(k) ?? { pos: 0, neg: 0 };
        if (v > 0) e.pos++;
        else e.neg++;
        vars.set(k, e);
      }
    if (vars.size === 0) return false;
    let x = '';
    let bestCost = Infinity;
    for (const [k, e] of vars) {
      const cost = e.pos * e.neg - e.pos - e.neg;
      if (cost < bestCost) {
        bestCost = cost;
        x = k;
      }
    }
    const pos: Lin[] = [];
    const neg: Lin[] = [];
    const rest: Lin[] = [];
    for (const l of cs) {
      const v = l.c.get(x) ?? 0;
      if (v > 0) pos.push(l);
      else if (v < 0) neg.push(l);
      else rest.push(l);
    }
    const next = rest;
    const seen = new Set<string>();
    for (const p of pos)
      for (const n of neg) {
        const a = p.c.get(x)!;
        const b = -n.c.get(x)!;
        const c = new Map<string, number>();
        for (const [k, v] of p.c) c.set(k, b * v);
        for (const [k, v] of n.c) c.set(k, (c.get(k) ?? 0) + a * v);
        c.delete(x);
        const r = normalizeLin({ c, k: b * p.k + a * n.k, eq: false });
        if (r === 'false') return true;
        if (r === 'true') continue;
        for (const v of r.c.values()) if (!Number.isSafeInteger(v)) return false;
        const key = [...r.c].sort().map(([k, v]) => k + ':' + v).join(',') + '|' + r.k;
        if (seen.has(key)) continue;
        seen.add(key);
        next.push(r);
      }
    cs = next;
  }
  return false;
}

export { natT, intT };
