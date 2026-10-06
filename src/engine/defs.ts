// Definitional packages: datatype, fun (with pattern completion), definition, inductive.
import {
  Term,
  Type,
  tcon,
  tvar,
  funT,
  funTs,
  boolT,
  natT,
  mkC,
  mkF,
  mkV,
  mkApps,
  mkEq,
  mkMetaImp,
  stripApp,
  numVal,
  frees,
  substFrees,
  termEq,
  typeOf,
  typeEq,
  EngineError,
  mapTypes,
  tmapV,
  destApp,
  hasLooseBound,
  variant,
} from './terms';
import { Theory, Thm, Datatype, FunEq, generalize } from './theory';
import { unify, match, collectVarNames } from './unify';

// ---------------- datatype ----------------

export interface DatatypeSpec {
  name: string;
  params: string[];
  ctors: { name: string; argTys: Type[] }[];
}

export function declareDatatype(thy: Theory, spec: DatatypeSpec) {
  const dtT = tcon(spec.name, spec.params.map(tvar));
  const caseConst = 'case_' + spec.name;
  const dt: Datatype = { name: spec.name, params: spec.params, ctors: spec.ctors, caseConst };
  thy.datatypes.set(spec.name, dt);
  for (const c of spec.ctors) {
    if (thy.consts.has(c.name) && !thy.ctorOf.has(c.name)) throw new EngineError(`Duplicate constant declaration: "${c.name}"`);
    thy.addConst(c.name, funTs(c.argTys, dtT));
    thy.ctorOf.set(c.name, spec.name);
  }
  const r = tvar("'r" + (spec.params.includes("'r") ? 'r' : ''));
  thy.addConst(caseConst, funTs([...spec.ctors.map((c) => funTs(c.argTys, r)), dtT], r));
  // theorems: induct, inject, distinct, exhaust (as propositions for reference)
  const P = mkV('P', funT(dtT, boolT));
  const x = mkV('x', dtT);
  const indPrems: Term[] = [];
  const exhaustPrems: Term[] = [];
  const Q = mkV('Q', boolT);
  spec.ctors.forEach((c) => {
    const vs = c.argTys.map((t, i) => mkF(`x${i + 1}`, t));
    const ct = mkApps(mkC(c.name, funTs(c.argTys, dtT)), vs);
    let prem: Term = mkApps(P, [ct]);
    vs.forEach((v, i) => {
      if (typeEq(c.argTys[i], dtT)) prem = mkMetaImp(mkApps(P, [v]), prem);
    });
    indPrems.push(closeOver(vs, prem));
    exhaustPrems.push(closeOver(vs, mkMetaImp(mkEq(x, ct), Q)));
  });
  let ind: Term = mkApps(P, [x]);
  for (let i = indPrems.length - 1; i >= 0; i--) ind = mkMetaImp(indPrems[i], ind);
  thy.addThms(spec.name + '.induct', [{ name: spec.name + '.induct', prop: ind, global: true }]);
  let ex: Term = Q;
  for (let i = exhaustPrems.length - 1; i >= 0; i--) ex = mkMetaImp(exhaustPrems[i], ex);
  thy.addThms(spec.name + '.exhaust', [{ name: spec.name + '.exhaust', prop: ex, global: true }]);
  // injectivity & distinctness theorems (simp handles these by simproc)
  const inj: Thm[] = [];
  const dist: Thm[] = [];
  spec.ctors.forEach((c, i) => {
    if (c.argTys.length) {
      const as = c.argTys.map((t, j) => mkV(`a${j + 1}`, t));
      const bs = c.argTys.map((t, j) => mkV(`b${j + 1}`, t));
      const C = mkC(c.name, funTs(c.argTys, dtT));
      const lhs = mkEq(mkApps(C, as), mkApps(C, bs));
      const rhs = as.map((a, j) => mkEq(a, bs[j])).reduceRight((acc, e) => mkApps(mkC('conj', funTs([boolT, boolT], boolT)), [e, acc]));
      inj.push({ name: `${spec.name}.inject(${inj.length + 1})`, prop: mkEq(lhs, rhs), global: true });
    }
    spec.ctors.forEach((d, j) => {
      if (j <= i) return;
      const as = c.argTys.map((t, k) => mkV(`a${k + 1}`, t));
      const bs = d.argTys.map((t, k) => mkV(`b${k + 1}`, t));
      const neq = mkApps(mkC('Not', funT(boolT, boolT)), [mkEq(mkApps(mkC(c.name, funTs(c.argTys, dtT)), as), mkApps(mkC(d.name, funTs(d.argTys, dtT)), bs))]);
      dist.push({ name: `${spec.name}.distinct(${dist.length + 1})`, prop: neq, global: true });
    });
  });
  thy.addThms(spec.name + '.inject', inj);
  thy.addThms(spec.name + '.distinct', dist);
  thy.addThms(spec.name + '.simps', [...inj, ...dist]);
}

function closeOver(vs: Term[], t: Term): Term {
  let r = t;
  for (let i = vs.length - 1; i >= 0; i--) {
    const v = vs[i] as Term & { k: 'F' };
    r = { k: 'A', f: mkC('!!', funT(funT(v.ty, boolT), boolT)), a: { k: 'L', x: v.name, ty: v.ty, body: absName(r, v.name, 0) } };
  }
  return r;
}
function absName(t: Term, n: string, lev: number): Term {
  if (t.k === 'F' && t.name === n) return { k: 'B', i: lev };
  if (t.k === 'A') return { k: 'A', f: absName(t.f, n, lev), a: absName(t.a, n, lev) };
  if (t.k === 'L') return { k: 'L', x: t.x, ty: t.ty, body: absName(t.body, n, lev + 1) };
  return t;
}

// ---------------- fun ----------------

/** Normalise a pattern: numerals at nat become Suc^k 0. */
function normPat(thy: Theory, p: Term): Term {
  const v = numVal(p);
  if (v !== null) {
    const ty = typeOf(p);
    if (ty.k === 'T' && ty.name === 'nat' && v > 0) {
      let r: Term = mkC('#0', natT);
      for (let i = 0; i < v; i++) r = mkApps(mkC('Suc', funT(natT, natT)), [r]);
      return r;
    }
    return p;
  }
  const { head, args } = stripApp(p);
  if (head.k === 'F') {
    if (args.length) throw new EngineError('Bad pattern: variable applied to arguments');
    return p;
  }
  if (head.k === 'C') {
    if (head.name === '#0' || thy.isCtor(head.name)) return mkApps(head, args.map((a) => normPat(thy, a)));
    throw new EngineError(`Non-constructor pattern not allowed in sequential mode: "${head.name}"`);
  }
  throw new EngineError('Bad pattern');
}

let pvCounter = 0;

function isCtorTerm(thy: Theory, t: Term): boolean {
  const h = stripApp(t).head;
  return h.k === 'C' && (h.name === '#0' || thy.isCtor(h.name) || numVal(h) !== null);
}

function toVars(t: Term, tag: string): Term {
  switch (t.k) {
    case 'F':
      return mkV(t.name + tag, t.ty);
    case 'A':
      return { k: 'A', f: toVars(t.f, tag), a: toVars(t.a, tag) };
    default:
      return t;
  }
}

function tuple(ts: Term[]): Term {
  return mkApps(mkC('__tuple', boolT), ts);
}

/** p \ q for pattern vectors (as tuples). Returns pieces as substitutions of p's variables. */
function subtract(thy: Theory, p: Term[], q: Term[], used: Set<string>): Term[][] {
  const pv = tuple(p.map((x) => toVars(x, '__p')));
  const qv = tuple(q.map((x) => toVars(x, '__q')));
  if (!unify(pv, qv)) return [p];
  // p instance of q?
  if (match(qv, tuple(p))) return [];
  // find split position: p var vs q ctor
  const find = (a: Term, b: Term): (Term & { k: 'F' }) | null => {
    if (a.k === 'F') {
      if (isCtorTerm(thy, b)) return a as Term & { k: 'F' };
      return null;
    }
    const sa = stripApp(a);
    const sb = stripApp(b);
    if (sb.head.k === 'F') return null;
    for (let i = 0; i < Math.min(sa.args.length, sb.args.length); i++) {
      const r = find(sa.args[i], sb.args[i]);
      if (r) return r;
    }
    return null;
  };
  let v: (Term & { k: 'F' }) | null = null;
  for (let i = 0; i < p.length && !v; i++) v = find(normPat(thy, p[i]), normPat(thy, q[i]));
  if (!v) return [p];
  const dt = thy.datatypeOf(v.ty);
  if (!dt) return [p];
  const out: Term[][] = [];
  for (const c of dt.ctors) {
    const argTys = thy.ctorArgTys(dt, c, v.ty);
    const args = argTys.map((t) => {
      const nm = variant('v', used);
      used.add(nm);
      return mkF(nm, t);
    });
    const ct = c.name === '#0' ? mkC('#0', natT) : mkApps(mkC(c.name, funTs(argTys, v.ty)), args);
    const m = new Map([[v.name, ct]]);
    const p2 = p.map((x) => substFrees(x, m));
    out.push(...subtract(thy, p2, q, used));
  }
  return out;
}

export interface RawEq {
  lhsArgs: Term[];
  rhs: Term;
}

/** Complete sequential patterns into a disjoint set of equations. */
export function completeEquations(thy: Theory, eqs: RawEq[]): FunEq[] {
  const result: FunEq[] = [];
  for (let i = 0; i < eqs.length; i++) {
    const used = new Set<string>();
    for (const a of eqs[i].lhsArgs) for (const k of frees(a).keys()) used.add(k);
    let pieces: Term[][] = [eqs[i].lhsArgs.map((a) => normPat(thy, a))];
    for (let j = 0; j < i; j++) {
      const q = eqs[j].lhsArgs.map((a) => normPat(thy, a));
      const next: Term[][] = [];
      for (const pc of pieces) next.push(...subtract(thy, pc, q, used));
      pieces = next;
    }
    for (const pc of pieces) {
      // compute substitution from original pattern to piece by matching
      const orig = tuple(eqs[i].lhsArgs.map((a) => toVars(normPat(thy, a), '')));
      const s = match(orig, tuple(pc));
      let rhs = eqs[i].rhs;
      if (s) {
        const m = new Map<string, Term>();
        for (const [k, v] of s.t) m.set(k, v);
        rhs = substFrees(rhs, m);
      }
      const vars: Term[] = [];
      for (const a of pc) for (const f of frees(a).values()) if (!vars.some((x) => termEq(x, f))) vars.push(f);
      result.push({ lhsArgs: pc, rhs, vars });
    }
  }
  return result;
}

export function checkLinearPatterns(eq: RawEq) {
  const seen = new Set<string>();
  const go = (t: Term) => {
    if (t.k === 'F') {
      if (seen.has(t.name)) throw new EngineError(`Duplicate variable in pattern: "${t.name}"`);
      seen.add(t.name);
    }
    if (t.k === 'A') {
      go(t.f);
      go(t.a);
    }
  };
  eq.lhsArgs.forEach(go);
}

/** Heuristic termination check: every recursive call must decrease some argument. */
export function checkTermination(thy: Theory, fname: string, arity: number, eqs: FunEq[]): boolean {
  const size = (t: Term): number => {
    const { head, args } = stripApp(t);
    const v = numVal(head);
    if (v !== null) return v + 1;
    if (head.k === 'C' && head.name === 'Suc') return 1 + size(args[0]);
    if (head.k === 'C' && thy.isCtor(head.name)) return 1 + args.reduce((a, x) => a + size(x), 0);
    return 1;
  };
  const varsOf = (t: Term) => [...frees(t).keys()].sort().join(',');
  const subterm = (a: Term, p: Term): boolean => {
    const { head, args } = stripApp(p);
    if (head.k !== 'C') return false;
    return args.some((x) => termEq(x, a) || subterm(a, x));
  };
  const builtFromCtors = (t: Term): boolean => {
    const { head, args } = stripApp(t);
    if (head.k === 'F') return args.length === 0;
    if (head.k === 'C' && (thy.isCtor(head.name) || head.name === '#0' || numVal(head) !== null)) return args.every(builtFromCtors);
    return false;
  };
  const decreases = (a: Term, p: Term, conds: Term[]): boolean => {
    if (subterm(a, p)) return true;
    if (builtFromCtors(a) && size(a) < size(p) && varsOf(a).split(',').every((v) => !v || varsOf(p).includes(v))) return true;
    // n - k, n div k with guard
    const mi = destApp(a, 'minus', 2) ?? destApp(a, 'div', 2);
    if (mi && termEq(mi[0], p) && (numVal(mi[1]) ?? 0) >= 1) {
      if (destApp(a, 'div', 2) && (numVal(mi[1]) ?? 0) < 2) return false;
      return conds.some((c) => mentionsNonzero(c, p));
    }
    if (mi && subterm(mi[0], p)) return true;
    // tl xs, butlast etc. under guard
    const tl = destApp(a, 'tl', 1) ?? destApp(a, 'butlast', 1);
    if (tl && termEq(tl[0], p)) return conds.some((c) => mentionsNonzero(c, p));
    return false;
  };
  for (const eq of eqs) {
    const calls: { args: Term[]; conds: Term[] }[] = [];
    const go = (t: Term, conds: Term[]) => {
      const { head, args } = stripApp(t);
      if (head.k === 'C' && head.name === 'If' && args.length === 3) {
        go(args[0], conds);
        go(args[1], [...conds, args[0]]);
        go(args[2], [...conds, mkApps(mkC('Not', funT(boolT, boolT)), [args[0]])]);
        return;
      }
      if (head.k === 'C' && head.name === fname && args.length >= arity) calls.push({ args: args.slice(0, arity), conds });
      if (head.k === 'L') go(head.body, conds);
      for (const a of args) go(a.k === 'L' ? a.body : a, conds);
    };
    go(eq.rhs, []);
    for (const c of calls) {
      if (c.args.some((x) => hasLooseBound(x))) continue;
      const ok = c.args.some((a, i) => decreases(a, eq.lhsArgs[i], c.conds));
      if (!ok) return false;
    }
  }
  return true;
}

function mentionsNonzero(c: Term, x: Term): boolean {
  // c is ¬(x = 0), 0 < x, x ≠ [], x > 0, ¬ x ≤ 0 ...
  const n = destApp(c, 'Not', 1);
  if (n) {
    const e = destApp(n[0], 'eq', 2);
    if (e && (termEq(e[0], x) || termEq(e[1], x))) return true;
    const le = destApp(n[0], 'less_eq', 2);
    if (le && termEq(le[0], x)) return true;
    const lt = destApp(n[0], 'less', 2);
    if (lt && termEq(lt[0], x)) return true;
  }
  const lt = destApp(c, 'less', 2);
  if (lt && termEq(lt[1], x)) return true;
  const le = destApp(c, 'less_eq', 2);
  if (le && termEq(le[1], x)) return true;
  const e = destApp(c, 'eq', 2);
  if (e && (termEq(e[0], x) || termEq(e[1], x))) return false;
  return false;
}

export function registerFun(thy: Theory, name: string, ty: Type, eqs: FunEq[], addSimp = true) {
  const arity = eqs.length ? eqs[0].lhsArgs.length : 0;
  thy.funs.set(name, { name, eqs, ty, arity });
  const C = mkC(name, ty);
  const ths: Thm[] = eqs.map((eq, i) => ({
    name: eqs.length === 1 ? `${name}.simps` : `${name}.simps(${i + 1})`,
    prop: generalize(mkEq(mkApps(C, eq.lhsArgs), eq.rhs)),
    global: true,
  }));
  thy.addThms(name + '.simps', ths);
  if (addSimp) for (const th of ths) thy.addSimp(th);
  thy.addThms(name + '.induct', []);
}

export { generalize, collectVarNames, mapTypes, tmapV };
