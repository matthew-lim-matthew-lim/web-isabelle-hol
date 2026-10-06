// Basic tactics: resolution with rules, assumption, induction, case analysis, substitution.
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
  typeOf,
  typeEq,
  funT,
  boolT,
  natT,
  mkNot,
  mkEq,
  mkMetaImp,
  mkMetaAll,
  substFrees,
  frees,
  occursFree,
  variant,
  EngineError,
  hasLooseBound,
  isConst,
  tsubst,
  mapTypes,
  replaceTerm,
  occursTerm,
} from './terms';
import { Goal, termToGoal, goalFrees, goalToTerm, freshFree } from './goal';
import { Theory, Thm, instThm, FunInfo, Datatype } from './theory';
import { unify, inst, Subst, emptySubst, collectVarNames, match } from './unify';

export interface CaseInfo {
  name: string;
  fixes: (Term & { k: 'F' })[];
  assumes: Term[];
  ih: Term[];
  prems: Term[];
  concl: Term;
}

export interface TacResult {
  goals: Goal[]; // replaces the focused goal(s)
  subst?: Subst; // schematic instantiation to apply to the rest of the state
  cases?: CaseInfo[];
}

export function instGoal(g: Goal, s: Subst): Goal {
  if (s.t.size === 0 && s.ty.size === 0) return g;
  const ty = (t: Term) => (s.ty.size ? mapTypes(t, (x) => tsubst(x, s.ty)) : t);
  return {
    params: g.params.map((p) => ty(p) as Term & { k: 'F' }),
    prems: g.prems.map((p) => ty(inst(p, s))),
    concl: ty(inst(g.concl, s)),
  };
}

/** Decompose a rule proposition into premises and conclusion. Top-level ⋀ become schematic variables. */
export function decomposeRule(prop: Term): { prems: Term[]; concl: Term } {
  let t = prop;
  const prems: Term[] = [];
  let c = 0;
  for (;;) {
    const s = stripApp(t);
    if (s.head.k === 'C' && s.head.name === '!!' && s.args.length === 1 && s.args[0].k === 'L') {
      const lam = s.args[0];
      t = substBound(lam.body, mkV(lam.x + '_q' + ++c + '_' + Math.random().toString(36).slice(2, 6), lam.ty));
      continue;
    }
    const imp = destApp(t, '==>', 2);
    if (imp) {
      prems.push(imp[0]);
      t = imp[1];
      continue;
    }
    break;
  }
  return { prems, concl: t };
}

/** Lift a rule premise into a new subgoal under goal g. */
function liftPrem(g: Goal, prem: Term): Goal {
  const used = goalFrees(g);
  const sub = termToGoal(prem, used);
  return { params: [...g.params, ...sub.params], prems: [...g.prems, ...sub.prems], concl: sub.concl };
}

/** rule: resolve conclusion of the rule with the goal conclusion. */
export function resolveRule(g: Goal, ruleProp: Term, facts: Term[] = []): TacResult | null {
  const r = decomposeRule(ruleProp);
  let s = unify(r.concl, g.concl);
  if (!s) return null;
  let prems = r.prems;
  // chained facts discharge leading premises
  for (const f of facts) {
    let done = false;
    for (let i = 0; i < prems.length; i++) {
      const s2 = unify(prems[i], f, s);
      if (s2) {
        s = s2;
        prems = prems.filter((_, j) => j !== i);
        done = true;
        break;
      }
    }
    if (!done) return null;
  }
  const goals = prems.map((p) => instGoal(liftPrem(g, p), s!));
  return { goals, subst: s };
}

/** erule: conclusion with goal, first premise with some assumption (which is consumed). */
export function eresolveRule(g: Goal, ruleProp: Term): TacResult | null {
  const r = decomposeRule(ruleProp);
  if (r.prems.length === 0) return null;
  const s0 = unify(r.concl, g.concl);
  if (!s0) return null;
  for (let i = 0; i < g.prems.length; i++) {
    const s = unify(r.prems[0], g.prems[i], s0);
    if (!s) continue;
    const g2: Goal = { ...g, prems: g.prems.filter((_, j) => j !== i) };
    const goals = r.prems.slice(1).map((p) => instGoal(liftPrem(g2, p), s));
    return { goals, subst: s };
  }
  return null;
}

/** drule / frule: first premise with an assumption; the conclusion becomes a new assumption. */
export function dresolveRule(g: Goal, ruleProp: Term, keep = false): TacResult | null {
  const r = decomposeRule(ruleProp);
  if (r.prems.length === 0) return null;
  for (let i = 0; i < g.prems.length; i++) {
    const s = unify(r.prems[0], g.prems[i]);
    if (!s) continue;
    const prems = keep ? g.prems : g.prems.filter((_, j) => j !== i);
    const g2: Goal = { ...g, prems };
    const side = r.prems.slice(1).map((p) => instGoal(liftPrem(g2, p), s));
    const main = instGoal({ ...g2, prems: [...prems, r.concl] }, s);
    return { goals: [...side, main], subst: s };
  }
  return null;
}

export function assumptionTac(g: Goal): TacResult | null {
  for (const p of g.prems) {
    if (isConst(p, 'False')) return { goals: [] };
    const pg = termToGoal(p, goalFrees(g));
    if (pg.params.length === 0 && pg.prems.length === 0) {
      const s = unify(p, g.concl);
      if (s) return { goals: [], subst: s };
    }
  }
  if (isConst(g.concl, 'True')) return { goals: [] };
  return null;
}

/** Close goal by a fact proposition (possibly with schematic vars) whose premises are all assumptions. */
export function closeByFact(g: Goal, fact: Term): TacResult | null {
  const r = decomposeRule(fact);
  const s = unify(r.concl, g.concl);
  if (!s) return null;
  let cur = s;
  for (const p of r.prems) {
    let ok = false;
    for (const h of g.prems) {
      const s2 = unify(p, h, cur);
      if (s2) {
        cur = s2;
        ok = true;
        break;
      }
    }
    if (!ok) return null;
  }
  return { goals: [], subst: cur };
}

// ---------------- induction ----------------

function findVar(g: Goal, name: string): Term & { k: 'F' } {
  const p = g.params.find((p) => p.name === name);
  if (p) return p;
  const fs = new Map<string, Term>();
  for (const t of [...g.prems, g.concl]) frees(t, fs);
  const f = fs.get(name);
  if (f && f.k === 'F') return f as Term & { k: 'F' };
  throw new EngineError(`Variable "${name}" does not occur in the goal`);
}

function goalBody(g: Goal): Term {
  let t = g.concl;
  for (let i = g.prems.length - 1; i >= 0; i--) t = mkMetaImp(g.prems[i], t);
  return t;
}

function ctorTerm(thy: Theory, dt: Datatype, ctorName: string, argTys: Type[], ty: Type, args: Term[]): Term {
  if (ctorName === '#0') return mkC('#0', natT);
  return mkApps(mkC(ctorName, argTys.reduceRight((acc, a) => funT(a, acc), ty)), args);
}

/** Structural induction on variable x with optional arbitrary variables. */
export function inductTac(thy: Theory, g: Goal, xName: string, arbitrary: string[], tag: 'induct' | 'induction' = 'induct'): TacResult {
  const x = findVar(g, xName);
  const ty = x.ty;
  const dt = thy.datatypeOf(ty);
  if (!dt) throw new EngineError(`Unable to figure out induct rule: "${xName}" has type without induction rule`);
  const arbs = arbitrary.map((a) => findVar(g, a));
  const outerParams = g.params.filter((p) => p.name !== x.name && !arbs.some((a) => a.name === p.name));
  const body = goalBody(g); // prems ==> concl
  const used = goalFrees(g);
  const goals: Goal[] = [];
  const cases: CaseInfo[] = [];
  dt.ctors.forEach((c) => {
    const argTys = thy.ctorArgTys(dt, c, ty);
    const recIdx = argTys.map((a, j) => (typeEq(a, ty) ? j : -1)).filter((j) => j >= 0);
    const u = new Set(used);
    u.delete(x.name);
    for (const a of arbs) u.delete(a.name);
    const args = argTys.map((aty, j) => {
      const base = recIdx.includes(j) && recIdx.length === 1 ? x.name : `x${j + 1}`;
      return freshFree(base, aty, u);
    });
    const arbFresh = arbs.map((a) => freshFree(a.name, a.ty, u));
    const cT = ctorTerm(thy, dt, c.name, argTys, ty, args);
    const ihs: Term[] = recIdx.map((j) => {
      let ih = substFrees(body, new Map([[x.name, args[j] as Term]]));
      for (let k = arbs.length - 1; k >= 0; k--) ih = mkMetaAll(arbs[k], ih);
      return ih;
    });
    const sub = new Map<string, Term>([[x.name, cT]]);
    arbs.forEach((a, k) => sub.set(a.name, arbFresh[k]));
    const premsC = g.prems.map((p) => betaNorm(substFrees(p, sub)));
    const conclC = betaNorm(substFrees(g.concl, sub));
    const ihsN = ihs.map((h) => normalizeIH(h));
    goals.push({ params: [...outerParams, ...args, ...arbFresh], prems: [...ihsN, ...premsC], concl: conclC });
    cases.push({
      name: c.name === '#0' ? '0' : c.name,
      fixes: [...args, ...arbFresh],
      assumes: [...ihsN, ...premsC],
      ih: ihsN,
      prems: premsC,
      concl: conclC,
    });
  });
  void tag;
  return { goals, cases };
}

/** Make IH readable: (⋀y. A ⟹ B) stays; pure term otherwise */
function normalizeIH(t: Term): Term {
  return betaNorm(t);
}

/** Computation induction using f.induct derived from fun equations. */
export function funInductTac(thy: Theory, g: Goal, fi: FunInfo, xs: string[], arbitrary: string[]): TacResult {
  if (xs.length !== fi.arity) throw new EngineError(`Rule ${fi.name}.induct expects ${fi.arity} induction variable(s)`);
  const vs = xs.map((n) => findVar(g, n));
  const arbs = arbitrary.map((a) => findVar(g, a));
  const outer = g.params.filter((p) => !vs.some((v) => v.name === p.name) && !arbs.some((a) => a.name === p.name));
  const body = goalBody(g);
  const used = goalFrees(g);
  const goals: Goal[] = [];
  const cases: CaseInfo[] = [];
  fi.eqs.forEach((eq, idx) => {
    const u = new Set(used);
    for (const v of vs) u.delete(v.name);
    for (const a of arbs) u.delete(a.name);
    // rename pattern variables
    const ren = new Map<string, Term>();
    const fixes: (Term & { k: 'F' })[] = [];
    for (const pv of eq.vars) {
      const f = freshFree((pv as { name: string }).name, (pv as { ty: Type }).ty, u);
      ren.set((pv as { name: string }).name, f);
      fixes.push(f);
    }
    const arbFresh = arbs.map((a) => freshFree(a.name, a.ty, u));
    const pats = eq.lhsArgs.map((p) => substFrees(p, ren));
    const rhs = substFrees(eq.rhs, ren);
    const calls = collectCalls(fi.name, fi.arity, rhs, []);
    const ihs = calls.map(({ args, conds }) => {
      let ih = substFrees(body, new Map(vs.map((v, i) => [v.name, args[i]])));
      for (let k = conds.length - 1; k >= 0; k--) ih = mkMetaImp(conds[k], ih);
      for (let k = arbs.length - 1; k >= 0; k--) ih = mkMetaAll(arbs[k], ih);
      return betaNorm(ih);
    });
    const sub = new Map<string, Term>(vs.map((v, i) => [v.name, pats[i]]));
    arbs.forEach((a, k) => sub.set(a.name, arbFresh[k]));
    const premsC = g.prems.map((p) => betaNorm(substFrees(p, sub)));
    const conclC = betaNorm(substFrees(g.concl, sub));
    goals.push({ params: [...outer, ...fixes, ...arbFresh], prems: [...ihs, ...premsC], concl: conclC });
    cases.push({ name: String(idx + 1), fixes: [...fixes, ...arbFresh], assumes: [...ihs, ...premsC], ih: ihs, prems: premsC, concl: conclC });
  });
  return { goals, cases };
}

function collectCalls(f: string, arity: number, t: Term, conds: Term[]): { args: Term[]; conds: Term[] }[] {
  const out: { args: Term[]; conds: Term[] }[] = [];
  const go = (u: Term, cs: Term[]) => {
    const { head, args } = stripApp(u);
    if (head.k === 'C' && head.name === 'If' && args.length === 3) {
      go(args[0], cs);
      go(args[1], [...cs, args[0]]);
      go(args[2], [...cs, mkNot(args[0])]);
      return;
    }
    if (head.k === 'C' && head.name === f && args.length >= arity) {
      const a = args.slice(0, arity);
      if (!a.some((x) => hasLooseBound(x))) out.push({ args: a, conds: cs });
    }
    if (head.k === 'L') go(head.body, cs);
    for (const a of args) {
      if (a.k === 'L') {
        // look inside lambdas only for calls not depending on the bound variable
        go(a.body, cs);
      } else go(a, cs);
    }
  };
  go(t, conds);
  return out;
}

/** Case analysis on a term (datatype) or a boolean formula. */
export function casesTac(thy: Theory, g: Goal, t: Term): TacResult {
  let ty: Type;
  try {
    ty = typeOf(t);
  } catch {
    throw new EngineError('cases: ill-typed term');
  }
  if (ty.k === 'T' && ty.name === 'bool') {
    const g1: Goal = { ...g, prems: [...g.prems, t] };
    const g2: Goal = { ...g, prems: [...g.prems, mkNot(t)] };
    return {
      goals: [g1, g2],
      cases: [
        { name: 'True', fixes: [], assumes: [t], ih: [], prems: [t], concl: g.concl },
        { name: 'False', fixes: [], assumes: [mkNot(t)], ih: [], prems: [mkNot(t)], concl: g.concl },
      ],
    };
  }
  const dt = thy.datatypeOf(ty);
  if (!dt) throw new EngineError(`cases: no case analysis rule for type ${ty.k === 'T' ? ty.name : '?'}`);
  const used = goalFrees(g);
  const goals: Goal[] = [];
  const cases: CaseInfo[] = [];
  dt.ctors.forEach((c, ci) => {
    const argTys = thy.ctorArgTys(dt, c, ty);
    const u = new Set(used);
    const args = argTys.map((aty, j) => freshFree(argTys.length === 1 ? `x${ci + 1}` : `x${ci + 1}${j + 1}`, aty, u));
    const cT = ctorTerm(thy, dt, c.name, argTys, ty, args);
    const eq = mkEq(t, cT, ty);
    goals.push({ params: [...g.params, ...args], prems: [...g.prems, eq], concl: g.concl });
    cases.push({ name: c.name === '#0' ? '0' : c.name, fixes: args, assumes: [eq], ih: [], prems: [eq], concl: g.concl });
  });
  return { goals, cases };
}

/** subst: rewrite with an equation once (first matching position) in the conclusion or an assumption. */
export function substTac(g: Goal, eqProp: Term, asm = false): TacResult | null {
  const r = decomposeRule(eqProp);
  const e = destApp(r.concl, 'eq', 2);
  if (!e) return null;
  const [l, rr] = e;
  const tryIn = (t: Term): { t: Term; s: Subst } | null => {
    let res: { t: Term; s: Subst } | null = null;
    const go = (u: Term): Term => {
      if (res) return u;
      const s = match(l, u, undefined, collectVarNames(l));
      if (s && !hasLooseBound(u)) {
        res = { t: rr, s };
        return inst(rr, s);
      }
      if (u.k === 'A') return mkA(go(u.f), go(u.a));
      if (u.k === 'L') return mkL(u.x, u.ty, go(u.body));
      return u;
    };
    const nt = go(t);
    return res ? { t: nt, s: (res as { s: Subst }).s } : null;
  };
  if (!asm) {
    const r1 = tryIn(g.concl);
    if (!r1) return null;
    const side = r.prems.map((p) => instGoal(liftPrem(g, p), r1.s));
    return { goals: [{ ...g, concl: betaNorm(r1.t) }, ...side] };
  }
  for (let i = 0; i < g.prems.length; i++) {
    const r1 = tryIn(g.prems[i]);
    if (r1) {
      const prems = [...g.prems];
      prems[i] = betaNorm(r1.t);
      const side = r.prems.map((p) => instGoal(liftPrem(g, p), r1.s));
      return { goals: [{ ...g, prems }, ...side] };
    }
  }
  return null;
}

/** Substitute equations x = t / t = x for parameters/frees x (hyp_subst). */
export function hypSubst(g: Goal): Goal | null {
  for (let i = 0; i < g.prems.length; i++) {
    const e = destApp(g.prems[i], 'eq', 2);
    if (!e) continue;
    for (const [a, b] of [
      [e[0], e[1]],
      [e[1], e[0]],
    ]) {
      if (a.k === 'F' && !a.name.startsWith('_') && !occursFree(a.name, b)) {
        const m = new Map([[a.name, b]]);
        const prems = g.prems.filter((_, j) => j !== i).map((p) => betaNorm(substFrees(p, m)));
        return { params: g.params.filter((p) => p.name !== a.name), prems, concl: betaNorm(substFrees(g.concl, m)) };
      }
    }
  }
  return null;
}

export { goalToTerm, instThm, emptySubst, variant, mkF, abstractOver, replaceTerm, occursTerm, mkV, mkEq, boolT };
