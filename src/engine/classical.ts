// Classical reasoning: safe decomposition (clarify/safe), auto, and a tableau prover (blast/fast/metis).
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
  betaNorm,
  termEq,
  typeOf,
  funT,
  boolT,
  mkNot,
  mkConj,
  mkDisj,
  mkImp,
  mkEq,
  isConst,
  occursFree,
  substFrees,
  frees,
  TRUE,
  FALSE,
  termKey,
  abstractOver,
} from './terms';
import { Goal, goalFrees, freshFree, termToGoal } from './goal';
import { Theory } from './theory';
import { unify, inst, Subst, emptySubst, collectVarNames } from './unify';
import { Simpset, simpGoal, SimpOptions } from './simp';
import { hypSubst, instGoal } from './tactics';
import { linarith, isArithRel } from './arith';

const isSetT = (ty: Type) => ty.k === 'T' && ty.name === 'set';
function tyOf(t: Term): Type | null {
  try {
    return typeOf(t);
  } catch {
    return null;
  }
}

/** Expand set-theoretic atoms into logic (membership rules). Returns null if not applicable. */
export function expandSetAtom(t: Term): Term | null {
  const m = destApp(t, 'member', 2);
  if (m) {
    const [x, A] = m;
    const { head, args } = stripApp(A);
    if (head.k === 'C') {
      switch (head.name) {
        case 'union':
          if (args.length === 2) return mkDisj(mkMem(x, args[0]), mkMem(x, args[1]));
          break;
        case 'inter':
          if (args.length === 2) return mkConj(mkMem(x, args[0]), mkMem(x, args[1]));
          break;
        case 'minus':
          if (args.length === 2) return mkConj(mkMem(x, args[0]), mkNot(mkMem(x, args[1])));
          break;
        case 'bot_set':
          if (args.length === 0) return FALSE;
          break;
        case 'UNIV':
          if (args.length === 0) return TRUE;
          break;
        case 'insert':
          if (args.length === 2) return mkDisj(mkEq(x, args[0]), mkMem(x, args[1]));
          break;
        case 'Collect':
          if (args.length === 1) return betaNorm(mkA(args[0], x));
          break;
        case 'uminus':
          if (args.length === 1) return mkNot(mkMem(x, args[0]));
          break;
      }
    }
    return null;
  }
  const sub = destApp(t, 'subset_eq', 2);
  if (sub) {
    const ty = tyOf(sub[0]);
    if (!ty || ty.k !== 'T') return null;
    const el = ty.args[0];
    const z = mkF('_setx', el) as Term & { k: 'F' };
    return mkAllT(z, mkImp(mkMem(z, sub[0]), mkMem(z, sub[1])));
  }
  const e = destApp(t, 'eq', 2);
  if (e) {
    const ty = tyOf(e[0]);
    if (ty && isSetT(ty) && ty.k === 'T') {
      const z = mkF('_setx', ty.args[0]) as Term & { k: 'F' };
      return mkAllT(z, mkEq(mkMem(z, e[0]), mkMem(z, e[1]), boolT));
    }
  }
  return null;
}

function mkMem(x: Term, A: Term): Term {
  const ty = tyOf(x) ?? boolT;
  return mkApps(mkC('member', funT(ty, funT(tyOf(A) ?? boolT, boolT))), [x, A]);
}
function mkAllT(v: Term & { k: 'F' }, body: Term): Term {
  return mkA(mkC('All', funT(funT(v.ty, boolT), boolT)), mkL('x', v.ty, abstractOver(body, v)));
}

// ---------------- safe steps ----------------

/** One round of safe decomposition on a goal. Returns null when nothing applies. */
export function safeStep(g: Goal, opts: { splitDisj?: boolean } = {}): Goal[] | null {
  const c = g.concl;
  if (isConst(c, 'True')) return [];
  for (const p of g.prems) {
    if (isConst(p, 'False')) return [];
    if (termEq(p, c)) return [];
  }
  // conclusion
  const s = stripApp(c);
  if (s.head.k === 'C') {
    const n = s.head.name;
    if (n === 'conj' && s.args.length === 2) return [{ ...g, concl: s.args[0] }, { ...g, concl: s.args[1] }];
    if ((n === 'imp' || n === '==>') && s.args.length === 2) return [{ ...g, prems: [...g.prems, s.args[0]], concl: s.args[1] }];
    if ((n === 'All' || n === '!!') && s.args.length === 1 && s.args[0].k === 'L') {
      const used = goalFrees(g);
      const lam = s.args[0];
      const v = freshFree(lam.x === '_' || lam.x.startsWith('_') ? 'x' : lam.x, lam.ty, used);
      return [{ params: [...g.params, v], prems: g.prems, concl: betaNorm(substBound(lam.body, v)) }];
    }
    if (n === 'Not' && s.args.length === 1 && !isConst(s.args[0], 'False')) return [{ ...g, prems: [...g.prems, s.args[0]], concl: FALSE }];
    if (n === 'eq' && s.args.length === 2) {
      const ty = tyOf(s.args[0]);
      if (ty && ty.k === 'T' && ty.name === 'bool')
        return [
          { ...g, prems: [...g.prems, s.args[0]], concl: s.args[1] },
          { ...g, prems: [...g.prems, s.args[1]], concl: s.args[0] },
        ];
      if (ty && isSetT(ty)) {
        const ex = expandSetAtom(c);
        if (ex) return [{ ...g, concl: ex }];
      }
    }
    if (n === 'subset_eq') {
      const ex = expandSetAtom(c);
      if (ex) return [{ ...g, concl: ex }];
    }
    if (n === 'disj' && s.args.length === 2 && opts.splitDisj !== false) {
      // disjCI: ¬B ⟹ A
      const nb = destApp(s.args[1], 'Not', 1);
      return [{ ...g, prems: [...g.prems, nb ? nb[0] : mkNot(s.args[1])], concl: s.args[0] }];
    }
    if (n === 'member') {
      const ex = expandSetAtom(c);
      if (ex) return [{ ...g, concl: ex }];
    }
  }
  // premises
  for (let i = 0; i < g.prems.length; i++) {
    const p = g.prems[i];
    const ps = stripApp(p);
    const rest = g.prems.filter((_, j) => j !== i);
    if (ps.head.k !== 'C') continue;
    const n = ps.head.name;
    if (n === 'True') return [{ ...g, prems: rest }];
    if (n === 'conj' && ps.args.length === 2) return [{ ...g, prems: [...rest, ps.args[0], ps.args[1]] }];
    if (n === 'Ex' && ps.args.length === 1 && ps.args[0].k === 'L') {
      const used = goalFrees(g);
      const lam = ps.args[0];
      const v = freshFree(lam.x === '_' || lam.x.startsWith('_') ? 'x' : lam.x, lam.ty, used);
      return [{ params: [...g.params, v], prems: [...rest, betaNorm(substBound(lam.body, v))], concl: g.concl }];
    }
    if (n === 'disj' && ps.args.length === 2)
      return [
        { ...g, prems: [...rest, ps.args[0]] },
        { ...g, prems: [...rest, ps.args[1]] },
      ];
    if (n === 'member' || n === 'subset_eq') {
      const ex = expandSetAtom(p);
      if (ex) return [{ ...g, prems: [...rest, ex] }];
    }
    if (n === 'Not' && ps.args.length === 1) {
      const inner = destApp(ps.args[0], 'Not', 1);
      if (inner) return [{ ...g, prems: [...rest, inner[0]] }];
    }
  }
  const hs = hypSubst(g);
  if (hs) return [hs];
  return null;
}

export function clarify(g: Goal, maxRounds = 50): Goal[] {
  let goals = [g];
  let changed = true;
  let rounds = 0;
  while (changed && rounds++ < maxRounds) {
    changed = false;
    const next: Goal[] = [];
    for (const h of goals) {
      const r = safeStep(h, { splitDisj: false });
      if (r) {
        changed = true;
        next.push(...r);
      } else next.push(h);
    }
    goals = next;
  }
  return goals;
}

// ---------------- auto ----------------

export interface AutoOpts extends SimpOptions {
  facts?: Term[]; // extra intro/dest/elim facts for the search
  blastDepth?: number;
  maxGoals?: number;
}

function goalKey(g: Goal) {
  return [...g.prems.map(termKey), '|-', termKey(g.concl)].join(';');
}

export function autoGoal(thy: Theory, ss: Simpset, g: Goal, opts: AutoOpts = {}): Goal[] {
  let goals: Goal[] = [g];
  for (let round = 0; round < 30; round++) {
    let changed = false;
    const next: Goal[] = [];
    for (const h of goals) {
      const r = simpGoal(thy, ss, h, opts);
      if (r.kind === 'solved') {
        changed = true;
        continue;
      }
      const h2 = r.kind === 'goal' ? r.goal : h;
      if (r.kind === 'goal') changed = true;
      const st = safeStep(h2);
      if (st) {
        changed = true;
        next.push(...st);
      } else next.push(h2);
    }
    goals = next;
    if (goals.length > (opts.maxGoals ?? 60)) break;
    if (!changed) break;
  }
  // try to finish remaining goals with the tableau prover / arithmetic
  const rest: Goal[] = [];
  for (const h of goals) {
    if (tryArith(h)) continue;
    const r = blastGoal(h, opts.facts ?? [], opts.blastDepth ?? 2, 3000);
    if (r) continue;
    rest.push(h);
  }
  return rest;
}

export function tryArith(g: Goal): boolean {
  const relevant = isArithRel(g.concl) || isConst(g.concl, 'False') || g.prems.some(isArithRel);
  if (!relevant) return false;
  try {
    return linarith(g.prems, g.concl);
  } catch {
    return false;
  }
}

export function sameGoals(a: Goal[], b: Goal[]) {
  return a.length === b.length && a.every((g, i) => goalKey(g) === goalKey(b[i]));
}

// ---------------- tableau prover ----------------

interface Branch {
  L: Term[];
  R: Term[];
  gammaL: Term[]; // universally quantified hyps (∀, ⋀, schematic facts) for instantiation
  gammaR: Term[]; // existential goals
  uses: number;
}

let skCounter = 0;
let mvCounter = 0;

class Tableau {
  nodes = 0;
  mvMaxSk = new Map<string, number>();
  constructor(
    public maxNodes: number,
    public maxDepth: number,
  ) {}

  canBind = (name: string, t: Term): boolean => {
    const lim = this.mvMaxSk.get(name);
    if (lim === undefined) return true;
    for (const f of frees(t).keys()) {
      const m = /^_sk(\d+)$/.exec(f);
      if (m && Number(m[1]) > lim) return false;
    }
    return true;
  };

  freshMV(ty: Type): Term {
    const name = '_m' + ++mvCounter;
    this.mvMaxSk.set(name, skCounter);
    return mkV(name, ty);
  }

  freshSk(ty: Type, hint: string): Term & { k: 'F' } {
    void hint;
    return mkF('_sk' + ++skCounter, ty) as Term & { k: 'F' };
  }

  prove(branches: Branch[], s: Subst): Subst | null {
    if (branches.length === 0) return s;
    if (++this.nodes > this.maxNodes) return null;
    const b = branches[0];
    const rest = branches.slice(1);
    // close?
    const cands: Subst[] = [];
    const L = b.L.map((x) => inst(x, s));
    const R = b.R.map((x) => inst(x, s));
    for (const l of L) if (isConst(l, 'False')) return this.prove(rest, s);
    for (const r of R) {
      if (isConst(r, 'True')) return this.prove(rest, s);
      const e = destApp(r, 'eq', 2);
      if (e) {
        if (termEq(e[0], e[1])) return this.prove(rest, s);
        const u = unify(e[0], e[1], s, { canBind: this.canBind });
        if (u) cands.push(u);
      }
    }
    for (const l of L)
      for (const r of R) {
        if (termEq(l, r)) return this.prove(rest, s);
        const u = unify(l, r, s, { canBind: this.canBind });
        if (u) cands.push(u);
      }
    // arithmetic closure
    if ((R.some(isArithRel) || L.some(isArithRel)) && L.every((x) => collectVarNames(x).size === 0)) {
      try {
        const concl = R.length ? R.reduce((a, c) => mkDisj(a, c)) : FALSE;
        if (collectVarNames(concl).size === 0 && linarith(L, concl)) return this.prove(rest, s);
      } catch {
        /* ignore */
      }
    }
    for (const c of cands) {
      const r = this.prove(rest, c);
      if (r) return r;
    }
    // expansions
    const ex = this.expand(b, s);
    if (ex === null) return null;
    if (ex === 'closed') return this.prove(rest, s);
    for (const alt of ex) {
      const r = this.prove([...alt, ...rest], s);
      if (r) return r;
    }
    return null;
  }

  /** returns list of alternatives (each a list of branches replacing b), or null if exhausted */
  expand(b: Branch, s: Subst): Branch[][] | 'closed' | null {
    // α / β on L
    for (let i = 0; i < b.L.length; i++) {
      const f = betaNorm(inst(b.L[i], s));
      const Lr = b.L.filter((_, j) => j !== i);
      const st = stripApp(f);
      if (st.head.k === 'C') {
        const n = st.head.name;
        const a = st.args;
        if (n === 'True') return [[{ ...b, L: Lr }]];
        if (n === 'conj' && a.length === 2) return [[{ ...b, L: [...Lr, a[0], a[1]] }]];
        if (n === 'Not' && a.length === 1) return [[{ ...b, L: Lr, R: [...b.R, a[0]] }]];
        if (n === 'Ex' && a.length === 1 && a[0].k === 'L') {
          const sk = this.freshSk(a[0].ty, a[0].x);
          return [[{ ...b, L: [...Lr, betaNorm(substBound(a[0].body, sk))] }]];
        }
        if (n === 'disj' && a.length === 2) return [[{ ...b, L: [...Lr, a[0]] }, { ...b, L: [...Lr, a[1]] }]];
        if ((n === 'imp' || n === '==>') && a.length === 2) {
          // impE: prove A or use B
          return [[{ ...b, L: Lr, R: [...b.R, a[0]] }, { ...b, L: [...Lr, a[1]] }]];
        }
        if (n === 'eq' && a.length === 2) {
          const ty = tyOf(a[0]);
          if (ty && ty.k === 'T' && ty.name === 'bool')
            return [[{ ...b, L: [...Lr, a[0], a[1]] }, { ...b, L: Lr, R: [...b.R, a[0], a[1]] }]];
          // substitution x = t
          for (const [x, t] of [
            [a[0], a[1]],
            [a[1], a[0]],
          ]) {
            if (x.k === 'F' && !occursFree(x.name, t) && collectVarNames(t).size === 0) {
              const m = new Map([[x.name, t]]);
              const sub = (u: Term) => betaNorm(substFrees(u, m));
              return [[{ ...b, L: Lr.map(sub), R: b.R.map(sub), gammaL: b.gammaL.map(sub), gammaR: b.gammaR.map(sub) }]];
            }
          }
        }
        if ((n === 'All' || n === '!!') && a.length === 1 && a[0].k === 'L') return [[{ ...b, L: Lr, gammaL: [...b.gammaL, f] }]];
        if (n === 'member' || n === 'subset_eq' || n === 'eq') {
          const ex = expandSetAtom(f);
          if (ex) return [[{ ...b, L: [...Lr, ex] }]];
        }
      }
    }
    for (let i = 0; i < b.R.length; i++) {
      const f = betaNorm(inst(b.R[i], s));
      const Rr = b.R.filter((_, j) => j !== i);
      const st = stripApp(f);
      if (st.head.k === 'C') {
        const n = st.head.name;
        const a = st.args;
        if (n === 'False') return [[{ ...b, R: Rr }]];
        if (n === 'disj' && a.length === 2) return [[{ ...b, R: [...Rr, a[0], a[1]] }]];
        if ((n === 'imp' || n === '==>') && a.length === 2) return [[{ ...b, L: [...b.L, a[0]], R: [...Rr, a[1]] }]];
        if (n === 'Not' && a.length === 1) return [[{ ...b, L: [...b.L, a[0]], R: Rr }]];
        if ((n === 'All' || n === '!!') && a.length === 1 && a[0].k === 'L') {
          const sk = this.freshSk(a[0].ty, a[0].x);
          return [[{ ...b, R: [...Rr, betaNorm(substBound(a[0].body, sk))] }]];
        }
        if (n === 'conj' && a.length === 2) return [[{ ...b, R: [...Rr, a[0]] }, { ...b, R: [...Rr, a[1]] }]];
        if (n === 'eq' && a.length === 2) {
          const ty = tyOf(a[0]);
          if (ty && ty.k === 'T' && ty.name === 'bool')
            return [
              [
                { ...b, L: [...b.L, a[0]], R: [...Rr, a[1]] },
                { ...b, L: [...b.L, a[1]], R: [...Rr, a[0]] },
              ],
            ];
        }
        if (n === 'Ex' && a.length === 1 && a[0].k === 'L') return [[{ ...b, R: Rr, gammaR: [...b.gammaR, f] }]];
        if (n === 'member' || n === 'subset_eq' || n === 'eq') {
          const ex = expandSetAtom(f);
          if (ex) return [[{ ...b, R: [...Rr, ex] }]];
        }
      }
    }
    // γ
    if (b.uses >= this.maxDepth) return null;
    const alts: Branch[][] = [];
    for (let i = 0; i < b.gammaL.length; i++) {
      const f = inst(b.gammaL[i], s);
      const st = stripApp(f);
      const lam = st.args[0] as Term & { k: 'L' };
      const mv = this.freshMV(lam.ty);
      const g2 = [...b.gammaL.slice(0, i), ...b.gammaL.slice(i + 1), b.gammaL[i]];
      alts.push([{ ...b, L: [...b.L, betaNorm(substBound(lam.body, mv))], gammaL: g2, uses: b.uses + 1 }]);
    }
    for (let i = 0; i < b.gammaR.length; i++) {
      const f = inst(b.gammaR[i], s);
      const st = stripApp(f);
      const lam = st.args[0] as Term & { k: 'L' };
      const mv = this.freshMV(lam.ty);
      const g2 = [...b.gammaR.slice(0, i), ...b.gammaR.slice(i + 1), b.gammaR[i]];
      alts.push([{ ...b, R: [...b.R, betaNorm(substBound(lam.body, mv))], gammaR: g2, uses: b.uses + 1 }]);
    }
    return alts.length ? alts : null;
  }
}

/** Universal closure of schematic variables as ∀ (facts used as hypotheses). */
function closeFact(t: Term): Term {
  const vs = [...collectVarNames(t)];
  let r = t;
  const vm = new Map<string, Term>();
  const collect = (u: Term) => {
    if (u.k === 'V') vm.set(u.name, u);
    if (u.k === 'A') {
      collect(u.f);
      collect(u.a);
    }
    if (u.k === 'L') collect(u.body);
  };
  collect(t);
  for (const v of vs) {
    const vt = vm.get(v) as Term & { k: 'V' };
    const f = mkF('_cv' + v, vt.ty);
    r = replaceVar(r, v, f);
    r = mkA(mkC('All', funT(funT(vt.ty, boolT), boolT)), mkL(v.replace(/_.*$/, ''), vt.ty, abstractOver(r, f)));
  }
  return r;
}
function replaceVar(t: Term, name: string, by: Term): Term {
  switch (t.k) {
    case 'V':
      return t.name === name ? by : t;
    case 'A':
      return mkA(replaceVar(t.f, name, by), replaceVar(t.a, name, by));
    case 'L':
      return mkL(t.x, t.ty, replaceVar(t.body, name, by));
    default:
      return t;
  }
}

/** Try to prove goal by tableau search with iterative deepening. Returns substitution for goal schematic vars. */
export function blastGoal(g: Goal, facts: Term[], maxDepth = 4, maxNodes = 20000): Subst | null {
  const L = [...g.prems, ...facts.map(closeFact)];
  for (let d = 0; d <= maxDepth; d++) {
    const tb = new Tableau(maxNodes, d);
    const r = tb.prove([{ L, R: [g.concl], gammaL: [], gammaR: [], uses: 0 }], emptySubst());
    if (r) return r;
    if (tb.nodes > maxNodes) break;
  }
  return null;
}

export { termToGoal, instGoal, mkImp, mkEq };
