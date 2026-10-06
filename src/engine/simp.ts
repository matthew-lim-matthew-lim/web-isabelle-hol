// The simplifier: conditional higher-order rewriting with simprocs for arithmetic, datatypes and logic.
import {
  Term,
  Type,
  stripApp,
  destApp,
  mkA,
  mkApps,
  mkC,
  mkF,
  mkL,
  mkV,
  substBound,
  abstractOver,
  betaNorm,
  termEq,
  termKey,
  termSize,
  typeOf,
  typeEq,
  boolT,
  natT,
  funT,
  TRUE,
  FALSE,
  mkNot,
  mkConj,
  mkImp,
  mkEq,
  numVal,
  isConst,
  hasLooseBound,
  looseBoundAt,
  incrBound,
  EngineError,
  tsubst,
  conjs,
  destConj,
  mkB,
  occursFree,
} from './terms';
import { Theory, Thm, instThm } from './theory';
import { match, inst, collectVarNames, Subst } from './unify';
import { toPoly, polyAdd, polyIsConst, fromPoly, isArithType, linarith, Poly, isArithRel } from './arith';
import { Goal } from './goal';

export interface SimpRule {
  name: string;
  lhs: Term;
  rhs: Term;
  conds: Term[];
  perm: boolean;
  vars: Set<string>;
}

let ruleVarCounter = 0;

/** Turn a proposition into rewrite rules (Isabelle's mk_rews). */
export function mkRewrites(prop: Term, name: string, freeVarsAsVars = false): SimpRule[] {
  const out: SimpRule[] = [];
  const go = (t: Term, conds: Term[]) => {
    t = betaNorm(t);
    const s = stripApp(t);
    if (s.head.k === 'C') {
      const hn = s.head.name;
      if ((hn === '!!' || hn === 'All') && s.args.length === 1 && s.args[0].k === 'L') {
        const lam = s.args[0];
        const v = mkV(lam.x + '_r' + ++ruleVarCounter, lam.ty);
        return go(substBound(lam.body, v), conds);
      }
      if ((hn === '==>' || hn === 'imp') && s.args.length === 2) return go(s.args[1], [...conds, s.args[0]]);
      if (hn === 'conj' && s.args.length === 2) {
        go(s.args[0], conds);
        go(s.args[1], conds);
        return;
      }
      if (hn === 'True' && s.args.length === 0) return;
      if (hn === 'eq' && s.args.length === 2) {
        const [l, r] = s.args;
        if (termEq(l, r)) return;
        add(l, r, conds);
        return;
      }
      if (hn === 'Not' && s.args.length === 1) {
        const inner = s.args[0];
        add(inner, FALSE, conds);
        const e = destApp(inner, 'eq', 2);
        if (e) add(mkEq(e[1], e[0]), FALSE, conds);
        return;
      }
    }
    add(t, TRUE, conds);
  };
  const add = (lhs: Term, rhs: Term, conds: Term[]) => {
    const lh = stripApp(lhs).head;
    if (lh.k === 'V' || lh.k === 'B' || lh.k === 'L') {
      // variable-headed lhs: unusable as a rewrite rule, use P = True form only if not a var
      if (lhs.k === 'V') return;
      return;
    }
    if (isConst(lhs, 'True') || isConst(lhs, 'False')) return;
    const lv = collectVarNames(lhs);
    const rv = collectVarNames(rhs);
    for (const v of rv) if (!lv.has(v)) return; // rhs has extra vars
    const perm = isPermutative(lhs, rhs);
    out.push({ name, lhs, rhs, conds, perm, vars: lv });
  };
  go(freeVarsAsVars ? prop : prop, []);
  return out;
}

function isPermutative(l: Term, r: Term): boolean {
  if (termSize(l) !== termSize(r)) return false;
  // same shape modulo variable renaming
  const m = new Map<string, string>();
  const eq = (a: Term, b: Term): boolean => {
    if (a.k !== b.k) return false;
    switch (a.k) {
      case 'V': {
        const bn = (b as typeof a).name;
        return true && (m.has(a.name) ? m.get(a.name) === bn : (m.set(a.name, bn), true));
      }
      case 'C':
      case 'F':
        return a.name === (b as typeof a).name;
      case 'B':
        return a.i === (b as typeof a).i;
      case 'L':
        return eq(a.body, (b as typeof a).body);
      case 'A':
        return eq(a.f, (b as typeof a).f) && eq(a.a, (b as typeof a).a);
    }
  };
  return eq(l, r) && !termEq(l, r);
}

/** Term order for ordered rewriting. */
function termLess(a: Term, b: Term): boolean {
  return termOrd(a, b) < 0;
}

function atomName(t: Term): string {
  switch (t.k) {
    case 'C':
      return 'c' + t.name;
    case 'F':
      return 'f' + t.name;
    case 'V':
      return 'v' + t.name;
    case 'B':
      return 'b' + t.i;
    default:
      return 'z';
  }
}

/** Isabelle-like term order: size, then head symbol, then arguments lexicographically. */
function termOrd(a: Term, b: Term): number {
  const sa = termSize(a);
  const sb = termSize(b);
  if (sa !== sb) return sa - sb;
  const A = stripApp(a);
  const B = stripApp(b);
  if (A.head.k === 'L' && B.head.k === 'L') {
    const c = termOrd(A.head.body, B.head.body);
    if (c) return c;
  } else {
    const ha = atomName(A.head);
    const hb = atomName(B.head);
    if (ha !== hb) return ha < hb ? -1 : 1;
  }
  if (A.args.length !== B.args.length) return A.args.length - B.args.length;
  for (let i = 0; i < A.args.length; i++) {
    const c = termOrd(A.args[i], B.args[i]);
    if (c) return c;
  }
  return 0;
}

export class Simpset {
  byHead = new Map<string, SimpRule[]>();
  splits = new Set<string>();
  constructor(rules: SimpRule[] = []) {
    for (const r of rules) this.add(r);
  }
  static headKey(t: Term): string | null {
    const h = stripApp(t).head;
    if (h.k === 'C') return 'C:' + h.name;
    if (h.k === 'F') return 'F:' + h.name;
    return null;
  }
  add(r: SimpRule) {
    const k = Simpset.headKey(r.lhs);
    if (!k) return;
    let l = this.byHead.get(k);
    if (!l) {
      l = [];
      this.byHead.set(k, l);
    }
    l.push(r);
  }
  clone(): Simpset {
    const s = new Simpset();
    for (const [k, v] of this.byHead) s.byHead.set(k, [...v]);
    s.splits = new Set(this.splits);
    return s;
  }
  delName(name: string) {
    for (const [k, v] of this.byHead)
      this.byHead.set(
        k,
        v.filter((r) => r.name !== name && !r.name.startsWith(name + '(')),
      );
  }
}

/** Build the default simpset from theory simp rules plus extra theorems. */
export function buildSimpset(thy: Theory, extra: Thm[] = [], del: string[] = [], only = false): Simpset {
  const ss = new Simpset();
  const src = only ? extra : [...thy.simpRules, ...extra];
  for (const th of src) {
    if (del.some((d) => th.name === d || th.name.startsWith(d + '('))) continue;
    for (const r of mkRewrites(instThm(th), th.name)) ss.add(r);
  }
  for (const s of thy.splitRules) ss.splits.add(s);
  return ss;
}

export class SimpLimit extends EngineError {}

interface Ctx {
  rules: SimpRule[]; // local assumption rules (checked before global)
  facts: Term[]; // assumptions (for arithmetic)
}

let sxCounter = 0;

export interface SimpOptions {
  maxSteps?: number;
  arith?: boolean;
  splitIf?: boolean;
  noAsm?: boolean; // simp (no_asm)
  onlyMode?: boolean; // simp only: no simprocs except beta/numeral evaluation
}

export class Simplifier {
  steps = 0;
  maxSteps: number;
  ctxStack: Ctx[] = [{ rules: [], facts: [] }];
  condDepth = 0;
  cache = new Map<string, Term>();
  constructor(
    public thy: Theory,
    public ss: Simpset,
    public opts: SimpOptions = {},
  ) {
    this.maxSteps = opts.maxSteps ?? 4000;
  }

  get ctx() {
    return this.ctxStack[this.ctxStack.length - 1];
  }

  withAsm<T>(asm: Term, f: () => T): T {
    const rules = asm.k === 'C' ? [] : mkRewrites(asm, 'asm');
    const prev = this.ctx;
    this.ctxStack.push({ rules: [...rules, ...prev.rules], facts: [...prev.facts, asm] });
    const saved = this.cache;
    this.cache = new Map();
    try {
      return f();
    } finally {
      this.ctxStack.pop();
      this.cache = saved;
    }
  }

  tick() {
    if (++this.steps > this.maxSteps) throw new SimpLimit('Simplifier: step limit exceeded (possible non-terminating rewrite rules)');
  }

  norm(t: Term): Term {
    const key = termKey(t);
    const c = this.cache.get(key);
    if (c) return c;
    const r = this.norm1(t);
    this.cache.set(key, r);
    this.cache.set(termKey(r), r);
    return r;
  }

  private norm1(t: Term, top = true): Term {
    this.tick();
    const rewriteTop = (u: Term) => (top ? this.rewriteTop(u) : u);
    switch (t.k) {
      case 'L': {
        const z = mkF('_sx' + ++sxCounter, t.ty);
        const b = this.norm(substBound(t.body, z));
        const lam = mkL(t.x, t.ty, abstractOver(b, z));
        return rewriteTop(betaNorm(lam));
      }
      case 'A': {
        const { head, args } = stripApp(t);
        if (head.k === 'L') return this.norm(betaNorm(t));
        if (head.k === 'C') {
          const n = head.name;
          if (n === 'If' && args.length === 3) {
            const c = this.norm(args[0]);
            if (isConst(c, 'True')) return this.norm(args[1]);
            if (isConst(c, 'False')) return this.norm(args[2]);
            let ity: Type | null = null;
            try {
              ity = typeOf(args[1]);
            } catch {
              ity = null;
            }
            if (ity && ity.k === 'T' && ity.name === 'bool' && !this.opts.onlyMode)
              return this.norm(mkConj(mkImp(c, args[1]), mkImp(this.negate(c), args[2])));
            const a = this.withAsm(c, () => this.norm(args[1]));
            const b = this.withAsm(this.negate(c), () => this.norm(args[2]));
            if (termEq(a, b)) return a;
            return rewriteTop(mkApps(head, [c, a, b]));
          }
          if ((n === 'imp' || n === '==>') && args.length === 2) {
            const a = this.norm(args[0]);
            if (isConst(a, 'False')) return TRUE;
            if (isConst(a, 'True')) return this.norm(args[1]);
            const b = this.opts.noAsm ? this.norm(args[1]) : this.withAsm(a, () => this.norm(args[1]));
            return rewriteTop(mkApps(mkC('imp', head.ty), [a, b]));
          }
          if (n === 'conj' && args.length === 2) {
            const a = this.norm(args[0]);
            if (isConst(a, 'False')) return FALSE;
            const b = this.norm(args[1]);
            return rewriteTop(mkApps(head, [a, b]));
          }
        }
        const h2 = head.k === 'A' ? this.norm(head) : head;
        const nargs = args.map((a) => this.norm(a));
        return rewriteTop(mkApps(h2, nargs));
      }
      default:
        return rewriteTop(t);
    }
  }

  negate(c: Term): Term {
    const n = destApp(c, 'Not', 1);
    return n ? n[0] : mkNot(c);
  }

  rewriteTop(t: Term): Term {
    for (;;) {
      this.tick();
      const r = this.step(t);
      if (r === null) {
        if (this.opts.splitIf !== false && !this.opts.onlyMode) {
          const sp = this.trySplit(t);
          if (sp) return this.norm(sp);
        }
        return t;
      }
      // normalise the subterms of the rewritten term, then continue at the top
      const key = termKey(r);
      const c = this.cache.get(key);
      if (c) return c;
      t = this.norm1(r, false);
    }
  }

  /** One rewrite step at the top; returns null if no rule applies. */
  step(t: Term): Term | null {
    t = betaNorm(t);
    if (!this.opts.onlyMode) {
      const p = this.simproc(t);
      if (p && !termEq(p, t)) return p;
    } else {
      const p = this.numeralProc(t);
      if (p && !termEq(p, t)) return p;
    }
    const k = Simpset.headKey(t);
    if (!k) return null;
    const cands = [...this.ctx.rules.filter((r) => Simpset.headKey(r.lhs) === k), ...(this.ss.byHead.get(k) ?? [])];
    for (const rule of cands) {
      const s = match(rule.lhs, t, undefined, rule.vars);
      if (!s) continue;
      if (!this.condsOk(rule, s)) continue;
      const rhs = inst(rule.rhs, s);
      if (rule.perm && !termLess(rhs, t)) continue;
      if (termEq(rhs, t)) continue;
      return rhs;
    }
    return null;
  }

  private condsOk(rule: SimpRule, s: Subst): boolean {
    if (rule.conds.length === 0) return true;
    if (this.condDepth > 4) return false;
    this.condDepth++;
    try {
      for (const c of rule.conds) {
        const ci = inst(c, s);
        if (collectVarNames(ci).size) {
          // try to instantiate from assumptions
          let found = false;
          for (const f of this.ctx.facts) {
            const m = match(ci, f, s);
            if (m) {
              found = true;
              break;
            }
          }
          if (!found) return false;
          continue;
        }
        if (this.ctx.facts.some((f) => termEq(f, ci))) continue;
        const saved = this.cache;
        const r = this.norm(ci);
        this.cache = saved;
        if (!isConst(r, 'True')) return false;
      }
      return true;
    } finally {
      this.condDepth--;
    }
  }

  // ---------- simprocs ----------
  simproc(t: Term): Term | null {
    const { head, args } = stripApp(t);
    if (head.k !== 'C') return null;
    const n = head.name;
    const num = this.numeralProc(t);
    if (num) return num;
    switch (n) {
      case 'Not':
        if (args.length === 1) {
          const a = args[0];
          if (isConst(a, 'True')) return FALSE;
          if (isConst(a, 'False')) return TRUE;
          const nn = destApp(a, 'Not', 1);
          if (nn) return nn[0];
          // arithmetic negations: ¬ a < b  =  b ≤ a
          const lt = destApp(a, 'less', 2);
          if (lt && this.isLinOrd(lt[0])) return mkApps(mkC('less_eq', (stripApp(a).head as { ty: Type }).ty), [lt[1], lt[0]]);
          const le = destApp(a, 'less_eq', 2);
          if (le && this.isLinOrd(le[0])) return mkApps(mkC('less', (stripApp(a).head as { ty: Type }).ty), [le[1], le[0]]);
          const eqf = this.arithAtom(mkNot(a));
          if (eqf) return eqf;
        }
        break;
      case 'eq':
        if (args.length === 2) return this.eqProc(args[0], args[1], t);
        break;
      case 'less':
      case 'less_eq':
        if (args.length === 2) return this.arithAtom(t);
        break;
      case 'All':
      case 'Ex':
        if (args.length === 1 && args[0].k === 'L') return this.quantProc(n, args[0]);
        break;
      case 'Let':
        if (args.length === 2) return betaNorm(mkA(args[1], args[0]));
        break;
      case 'Ex1':
        break;
      default:
        if (n.startsWith('case_') && args.length >= 1) return this.caseProc(n, args);
    }
    return null;
  }

  private isLinOrd(t: Term): boolean {
    try {
      return isArithType(typeOf(t));
    } catch {
      return false;
    }
  }

  numeralProc(t: Term): Term | null {
    const { head, args } = stripApp(t);
    if (head.k !== 'C') return null;
    const n = head.name;
    if (n === 'Suc' && args.length === 1) {
      const v = numVal(args[0]);
      if (v !== null) return mkC('#' + (v + 1), natT);
      return null;
    }
    if (args.length !== 2) {
      if (n === 'uminus' && args.length === 1) {
        const v = numVal(args[0]);
        if (v === 0) return args[0];
        const inner = destApp(args[0], 'uminus', 1);
        if (inner) return inner[0];
      }
      return null;
    }
    const a = numVal(args[0]);
    const b = numVal(args[1]);
    let ty: Type;
    try {
      ty = typeOf(args[0]);
    } catch {
      return null;
    }
    const isNatT = ty.k === 'T' && ty.name === 'nat';
    const isIntT = ty.k === 'T' && ty.name === 'int';
    if (!isNatT && !isIntT) return null;
    const intVal = (x: Term): number | null => {
      const v = numVal(x);
      if (v !== null) return v;
      const u = destApp(x, 'uminus', 1);
      if (u) {
        const w = numVal(u[0]);
        if (w !== null) return -w;
      }
      return null;
    };
    const x = isIntT ? intVal(args[0]) : a;
    const y = isIntT ? intVal(args[1]) : b;
    if (x === null || y === null) {
      // identities with 0 / 1
      if (n === 'plus') {
        if (x === 0) return args[1];
        if (y === 0) return args[0];
      }
      if (n === 'minus' && y === 0) return args[0];
      if (n === 'times') {
        if (x === 0 || y === 0) return mkC('#0', ty);
        if (x === 1) return args[1];
        if (y === 1) return args[0];
      }
      if (n === 'power' && b === 0) return mkC('#1', ty);
      if (n === 'power' && b === 1) return args[0];
      if ((n === 'div') && y === 1) return args[0];
      if ((n === 'mod') && y === 1) return mkC('#0', ty);
      if ((n === 'div' || n === 'mod') && x === 0) return mkC('#0', ty);
      return null;
    }
    const mk = (v: number): Term => {
      if (v < 0) return mkApps(mkC('uminus', funT(ty, ty)), [mkC('#' + -v, ty)]);
      return mkC('#' + v, ty);
    };
    const floorDiv = (p: number, q: number) => Math.floor(p / q);
    switch (n) {
      case 'plus':
        return mk(x + y);
      case 'minus':
        return mk(isNatT ? Math.max(0, x - y) : x - y);
      case 'times':
        return mk(x * y);
      case 'div':
        return mk(y === 0 ? 0 : floorDiv(x, y));
      case 'mod':
        return mk(y === 0 ? x : x - y * floorDiv(x, y));
      case 'power':
        if (b !== null && b <= 64) return mk(Math.pow(x, b));
        return null;
      case 'max':
        return mk(Math.max(x, y));
      case 'min':
        return mk(Math.min(x, y));
      case 'less':
        return x < y ? TRUE : FALSE;
      case 'less_eq':
        return x <= y ? TRUE : FALSE;
      case 'eq':
        return x === y ? TRUE : FALSE;
      case 'dvd':
        return (x === 0 ? y === 0 : y % x === 0) ? TRUE : FALSE;
    }
    return null;
  }

  private eqProc(a: Term, b: Term, t: Term): Term | null {
    if (termEq(a, b)) return TRUE;
    let ty: Type;
    try {
      ty = typeOf(a);
    } catch {
      return null;
    }
    // bool equalities
    if (ty.k === 'T' && ty.name === 'bool') {
      if (isConst(a, 'True')) return b;
      if (isConst(b, 'True')) return a;
      if (isConst(a, 'False')) return mkNot(b);
      if (isConst(b, 'False')) return mkNot(a);
      return null;
    }
    // datatype constructors
    const ca = this.ctorView(a, ty);
    const cb = this.ctorView(b, ty);
    if (ca && cb) {
      if (ca.ctor !== cb.ctor) return FALSE;
      if (ca.args.length === 0) return TRUE;
      return conjs(ca.args.map((x, i) => mkEq(x, cb.args[i])));
    }
    if (isArithType(ty)) return this.arithAtom(t);
    // function equality by extensionality is not automatic
    return null;
  }

  /** View a term as constructor application (including numerals for nat). */
  ctorView(t: Term, ty: Type): { ctor: string; args: Term[] } | null {
    const v = numVal(t);
    if (v !== null && ty.k === 'T' && ty.name === 'nat') return v === 0 ? { ctor: '#0', args: [] } : { ctor: 'Suc', args: [mkC('#' + (v - 1), natT)] };
    const { head, args } = stripApp(t);
    if (head.k === 'C' && (this.thy.isCtor(head.name) || head.name === '#0')) {
      const dtn = head.name === '#0' ? 'nat' : this.thy.ctorOf.get(head.name)!;
      const dt = this.thy.datatypes.get(dtn);
      const c = dt?.ctors.find((c) => c.name === head.name);
      if (c && c.argTys.length === args.length) return { ctor: head.name, args };
    }
    return null;
  }

  /** Decide / normalise arithmetic relations. */
  arithAtom(t: Term): Term | null {
    let negated = false;
    let atom = t;
    const nt = destApp(t, 'Not', 1);
    if (nt) {
      negated = true;
      atom = nt[0];
    }
    const { head, args } = stripApp(atom);
    if (head.k !== 'C' || args.length !== 2) return null;
    const rel = head.name;
    if (rel !== 'eq' && rel !== 'less' && rel !== 'less_eq') return null;
    let ty: Type;
    try {
      ty = typeOf(args[0]);
    } catch {
      return null;
    }
    if (!isArithType(ty)) return null;
    const isNatT = (ty as { name: string }).name === 'nat';
    const pa = toPoly(args[0], ty);
    const pb = toPoly(args[1], ty);
    const d = polyAdd(pa, pb, -1); // a - b
    const dc = polyIsConst(d);
    const res = (v: boolean) => ((v !== negated) ? TRUE : FALSE);
    if (dc !== null) {
      if (rel === 'eq') return res(dc === 0);
      if (rel === 'less') return res(dc < 0);
      return res(dc <= 0);
    }
    if (isNatT && rel !== 'eq') {
      // b - a has all nonneg coefficients -> a <= b
      const e = polyAdd(pb, pa, -1);
      const allNonneg = [...e.values()].every((m) => m.coeff >= 0);
      const allNonpos = [...e.values()].every((m) => m.coeff <= 0);
      if (allNonneg) {
        const c = e.get('')?.coeff ?? 0;
        if (rel === 'less_eq') return res(true);
        if (c > 0) return res(true);
      }
      if (allNonpos) {
        const c = e.get('')?.coeff ?? 0;
        if (rel === 'less' && true) return res(false); // b - a <= 0  =>  not a < b
        if (rel === 'less_eq' && c < 0) return res(false);
      }
    }
    // use arithmetic facts from context
    if (this.opts.arith !== false && this.ctx.facts.some((f) => isArithRel(f) || destConj(f).some(isArithRel))) {
      try {
        if (linarith(this.ctx.facts, atom)) return res(true);
        if (linarith(this.ctx.facts, mkNot(atom))) return res(false);
      } catch {
        /* ignore */
      }
    } else if (this.opts.arith !== false && (rel !== 'eq' || isNatT)) {
      try {
        if (linarith([], atom)) return res(true);
        if (linarith([], mkNot(atom))) return res(false);
      } catch {
        /* ignore */
      }
    }
    // cancellation of common monomials
    if (!negated) {
      const pos: Poly = new Map();
      const neg: Poly = new Map();
      for (const [k, m] of d) {
        if (m.coeff > 0) pos.set(k, m);
        else neg.set(k, { ...m, coeff: -m.coeff });
      }
      const common = [...pa.keys()].some((k) => pb.has(k));
      if (common) {
        const na = fromPoly(pos, ty);
        const nb = fromPoly(neg, ty);
        const r = mkApps(head, [na, nb]);
        if (!termEq(r, atom)) return r;
      }
    }
    return null;
  }

  private quantProc(q: string, lam: Term & { k: 'L' }): Term | null {
    const body = lam.body;
    if (!looseBoundAt(body, 0)) return incrBound(body, -1);
    // one-point rules
    if (q === 'Ex') {
      const cs = destConj(body);
      for (let i = 0; i < cs.length; i++) {
        const e = destApp(cs[i], 'eq', 2);
        if (!e) continue;
        let val: Term | null = null;
        if (e[0].k === 'B' && e[0].i === 0 && !looseBoundAt(e[1], 0)) val = e[1];
        else if (e[1].k === 'B' && e[1].i === 0 && !looseBoundAt(e[0], 0)) val = e[0];
        if (!val) continue;
        const rest = cs.filter((_, j) => j !== i);
        const restT = rest.length ? conjs(rest) : TRUE;
        return betaNorm(substBound(restT, incrBound(val, -1)));
      }
    } else {
      // ∀x. x = t ⟶ P x
      const im = destApp(body, 'imp', 2);
      if (im) {
        const cs = destConj(im[0]);
        for (let i = 0; i < cs.length; i++) {
          const e = destApp(cs[i], 'eq', 2);
          if (!e) continue;
          let val: Term | null = null;
          if (e[0].k === 'B' && e[0].i === 0 && !looseBoundAt(e[1], 0)) val = e[1];
          else if (e[1].k === 'B' && e[1].i === 0 && !looseBoundAt(e[0], 0)) val = e[0];
          if (!val) continue;
          const rest = cs.filter((_, j) => j !== i);
          const nb = rest.length ? mkImp(conjs(rest), im[1]) : im[1];
          return betaNorm(substBound(nb, incrBound(val, -1)));
        }
      }
      // ∀x. (A ∨ B) ⟶ C  =  (∀x. A ⟶ C) ∧ (∀x. B ⟶ C)
      if (im) {
        const dj = destApp(im[0], 'disj', 2);
        if (dj) {
          const allC = mkC('All', funT(funT(lam.ty, boolT), boolT));
          return mkConj(mkA(allC, mkL(lam.x, lam.ty, mkImp(dj[0], im[1]))), mkA(allC, mkL(lam.x, lam.ty, mkImp(dj[1], im[1]))));
        }
      }
      // ∀x. P x ∧ Q x  = (∀x. P x) ∧ (∀x. Q x)
      const cj = destApp(body, 'conj', 2);
      if (cj) {
        const allC = mkC('All', funT(funT(lam.ty, boolT), boolT));
        return mkConj(mkA(allC, mkL(lam.x, lam.ty, cj[0])), mkA(allC, mkL(lam.x, lam.ty, cj[1])));
      }
    }
    if (q === 'Ex') {
      const dj = destApp(body, 'disj', 2);
      if (dj) {
        const exC = mkC('Ex', funT(funT(lam.ty, boolT), boolT));
        return mkApps(mkC('disj', funT(boolT, funT(boolT, boolT))), [mkA(exC, mkL(lam.x, lam.ty, dj[0])), mkA(exC, mkL(lam.x, lam.ty, dj[1]))]);
      }
    }
    return null;
  }

  private caseProc(n: string, args: Term[]): Term | null {
    const dt = [...this.thy.datatypes.values()].find((d) => d.caseConst === n);
    if (!dt || args.length < dt.ctors.length + 1) return null;
    const scrut = args[dt.ctors.length];
    let ty: Type;
    try {
      ty = typeOf(scrut);
    } catch {
      return null;
    }
    const cv = this.ctorView(scrut, ty);
    if (!cv) return null;
    const i = dt.ctors.findIndex((c) => c.name === cv.ctor);
    if (i < 0) return null;
    return betaNorm(mkApps(args[i], [...cv.args, ...args.slice(dt.ctors.length + 1)]));
  }

  // ---------- splitting ----------
  private trySplit(t: Term): Term | null {
    let ty: Type;
    try {
      ty = typeOf(t);
    } catch {
      return null;
    }
    if (!(ty.k === 'T' && ty.name === 'bool')) return null;
    const h = stripApp(t).head;
    if (h.k === 'C' && ['conj', 'disj', 'imp', 'Not', 'If', 'All', 'Ex', '==>', '!!'].includes(h.name)) return null;
    if (h.k === 'C' && h.name === 'eq' && stripApp(t).args.length === 2) {
      try {
        const at = typeOf(stripApp(t).args[0]);
        if (at.k === 'T' && at.name === 'bool') return null;
      } catch {
        return null;
      }
    }
    // find a splittable subterm (not under binders, no loose bounds)
    const found = this.findSplittable(t);
    if (!found) return null;
    if (found.kind === 'if') {
      const [c, a, b] = found.args;
      const ta = replaceFirst(t, found.term, a);
      const tb = replaceFirst(t, found.term, b);
      return mkConj(mkImp(c, ta), mkImp(mkNot(c), tb));
    }
    // datatype case split
    const dt = found.dt!;
    const scrut = found.args[dt.ctors.length];
    let sty: Type;
    try {
      sty = typeOf(scrut);
    } catch {
      return null;
    }
    const parts: Term[] = [];
    dt.ctors.forEach((c, i) => {
      const argTys = this.thy.ctorArgTys(dt, c, sty);
      const vs = argTys.map((aty, j) => mkF('_cs' + ++sxCounter + '_' + j, aty));
      const ctorT = c.name === '#0' ? mkC('#0', natT) : mkApps(mkC(c.name, argTys.reduceRight((acc, a) => funT(a, acc), sty)), vs);
      const branch = betaNorm(mkApps(found.args[i], [...vs, ...found.args.slice(dt.ctors.length + 1)]));
      let body = mkImp(mkEq(scrut, ctorT), replaceFirst(t, found.term, branch));
      for (let j = vs.length - 1; j >= 0; j--) {
        body = mkA(mkC('All', funT(funT(argTys[j], boolT), boolT)), mkL(c.name === 'Cons' ? (j === 0 ? 'x' : 'xs') : 'x' + (j + 1), argTys[j], abstractOver(body, vs[j])));
      }
      parts.push(body);
    });
    return conjs(parts);
  }

  private findSplittable(t: Term): { kind: 'if' | 'case'; term: Term; args: Term[]; dt?: import('./theory').Datatype } | null {
    const { head, args } = stripApp(t);
    // search arguments first (innermost)
    for (const a of args) {
      if (a.k === 'L') continue;
      const r = this.findSplittable(a);
      if (r) return r;
    }
    if (head.k === 'C') {
      if (head.name === 'If' && args.length === 3 && !hasLooseBound(t)) return { kind: 'if', term: t, args };
      if (head.name.startsWith('case_') && this.ss.splits.has(head.name)) {
        const dt = [...this.thy.datatypes.values()].find((d) => d.caseConst === head.name);
        if (dt && args.length === dt.ctors.length + 1 && !hasLooseBound(t)) return { kind: 'case', term: t, args, dt };
      }
    }
    return null;
  }
}

function replaceFirst(t: Term, from: Term, to: Term): Term {
  let done = false;
  const go = (u: Term): Term => {
    if (done) return u;
    if (termEq(u, from)) {
      done = true;
      return to;
    }
    if (u.k === 'A') {
      const f = go(u.f);
      const a = go(u.a);
      return f === u.f && a === u.a ? u : mkA(f, a);
    }
    return u;
  };
  return go(t);
}

// ---------- goal-level simplification ----------

export type SimpResult = { kind: 'solved' } | { kind: 'goal'; goal: Goal } | { kind: 'unchanged' };

export function simpGoal(thy: Theory, ss: Simpset, g: Goal, opts: SimpOptions & { useAsms?: boolean; simpAsms?: boolean } = {}): SimpResult {
  const S = new Simplifier(thy, ss, opts);
  const useAsms = opts.useAsms !== false;
  const simpAsms = opts.simpAsms !== false;
  const newPrems: Term[] = [];
  let changed = false;
  const runWithPrems = <T>(prems: Term[], f: () => T): T => {
    if (prems.length === 0) return f();
    return S.withAsm(prems[0], () => runWithPrems(prems.slice(1), f));
  };
  for (const p of g.prems) {
    let np = p;
    if (simpAsms) {
      np = runWithPrems(useAsms ? newPrems : [], () => S.norm(p));
    }
    if (!termEq(np, p)) changed = true;
    if (isConst(np, 'False')) return { kind: 'solved' };
    if (isConst(np, 'True')) {
      changed = true;
      continue;
    }
    newPrems.push(np);
  }
  const concl = runWithPrems(useAsms ? newPrems : [], () => S.norm(g.concl));
  if (!termEq(concl, g.concl)) changed = true;
  if (isConst(concl, 'True')) return { kind: 'solved' };
  if (newPrems.some((p) => termEq(p, concl))) return { kind: 'solved' };
  // contradictory prems P and ¬P
  for (const p of newPrems) {
    const n = destApp(p, 'Not', 1);
    if (n && newPrems.some((q) => termEq(q, n[0]))) return { kind: 'solved' };
  }
  // arithmetic solver
  if (opts.arith !== false) {
    const arithGoal = isArithRel(concl) || isConst(concl, 'False') || destConj(concl).every(isArithRel) || isArithDisj(concl);
    if (arithGoal && (isArithRel(concl) || newPrems.some((p) => isArithRel(p) || destConj(p).some(isArithRel)))) {
      try {
        if (linarith(newPrems, concl)) return { kind: 'solved' };
      } catch {
        /* ignore */
      }
    }
  }
  if (!changed) return { kind: 'unchanged' };
  return { kind: 'goal', goal: { params: g.params, prems: newPrems, concl } };
}

function isArithDisj(t: Term): boolean {
  const d = destApp(t, 'disj', 2);
  if (d) return (isArithRel(d[0]) || isArithDisj(d[0])) && (isArithRel(d[1]) || isArithDisj(d[1]));
  const i = destApp(t, 'imp', 2);
  if (i) return isArithRel(i[1]) || isArithDisj(i[1]);
  return false;
}

/** Simplify a closed term (for `value`). */
export function simpTerm(thy: Theory, ss: Simpset, t: Term, maxSteps = 20000): Term {
  const S = new Simplifier(thy, ss, { maxSteps });
  return S.norm(t);
}

export { tsubst, typeEq, occursFree, mkB, boolT };
