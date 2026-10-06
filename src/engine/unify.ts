// Higher-order pattern unification and matching (locally nameless: binders are opened with fresh frees).
import {
  Term,
  Type,
  TSubst,
  tsubst,
  tunify,
  mkF,
  mkA,
  mkApps,
  mkL,
  substBound,
  stripApp,
  betaNorm,
  typeOf,
  abstractOver,
  numVal,
  mkC,
  natT,
  funT,
  typeEq,
  mapTypes,
} from './terms';

export interface Subst {
  t: Map<string, Term>;
  ty: TSubst;
}

export const emptySubst = (): Subst => ({ t: new Map(), ty: new Map() });
export const copySubst = (s: Subst): Subst => ({ t: new Map(s.t), ty: new Map(s.ty) });

export interface UnifyOpts {
  bindable?: (name: string) => boolean;
  canBind?: (name: string, t: Term) => boolean;
}

let bzCounter = 0;
const BZ = '_bz';

/** Fully instantiate term with substitution and beta-normalise. */
export function inst(t: Term, s: Subst, depth = 0): Term {
  if (s.t.size === 0 && s.ty.size === 0) return t;
  if (depth > 200) throw new Error('inst: substitution too deep');
  const go = (u: Term): Term => {
    switch (u.k) {
      case 'V': {
        const r = s.t.get(u.name);
        if (r) return inst(r, s, depth + 1);
        return s.ty.size ? { ...u, ty: tsubst(u.ty, s.ty) } : u;
      }
      case 'C':
      case 'F':
        return s.ty.size ? { ...u, ty: tsubst(u.ty, s.ty) } : u;
      case 'B':
        return u;
      case 'L':
        return mkL(u.x, s.ty.size ? tsubst(u.ty, s.ty) : u.ty, go(u.body));
      case 'A':
        return mkA(go(u.f), go(u.a));
    }
  };
  return betaNorm(go(t));
}

export function instType(ty: Type, s: Subst): Type {
  return tsubst(ty, s.ty);
}

function headNorm(t: Term, s: Subst): Term {
  for (;;) {
    const { head, args } = stripApp(t);
    if (head.k === 'V' && s.t.has(head.name)) {
      t = betaNorm(mkApps(s.t.get(head.name)!, args));
      continue;
    }
    if (head.k === 'L' && args.length) {
      t = betaNorm(t);
      continue;
    }
    return t;
  }
}

function occursVar(name: string, t: Term, s: Subst): boolean {
  switch (t.k) {
    case 'V':
      if (t.name === name) return true;
      if (s.t.has(t.name)) return occursVar(name, s.t.get(t.name)!, s);
      return false;
    case 'L':
      return occursVar(name, t.body, s);
    case 'A':
      return occursVar(name, t.f, s) || occursVar(name, t.a, s);
    default:
      return false;
  }
}

function binderFrees(t: Term, acc: Set<string> = new Set()): Set<string> {
  switch (t.k) {
    case 'F':
      if (t.name.startsWith(BZ)) acc.add(t.name);
      break;
    case 'L':
      binderFrees(t.body, acc);
      break;
    case 'A':
      binderFrees(t.f, acc);
      binderFrees(t.a, acc);
      break;
  }
  return acc;
}

class Unifier {
  steps = 0;
  constructor(
    public s: Subst,
    public opts: UnifyOpts,
  ) {}

  bindable(name: string) {
    return this.opts.bindable ? this.opts.bindable(name) : true;
  }

  tyOf(t: Term): Type {
    return tsubst(typeOf(t), this.s.ty);
  }

  unify(a: Term, b: Term): boolean {
    if (++this.steps > 5000) return false;
    a = headNorm(a, this.s);
    b = headNorm(b, this.s);
    if (a.k === 'L' && b.k === 'L') {
      if (!tunify(a.ty, b.ty, this.s.ty)) return false;
      const z = mkF(BZ + ++bzCounter, a.ty);
      return this.unify(substBound(a.body, z), substBound(b.body, z));
    }
    if (a.k === 'L') {
      const z = mkF(BZ + ++bzCounter, a.ty);
      return this.unify(substBound(a.body, z), mkA(b, z));
    }
    if (b.k === 'L') {
      const z = mkF(BZ + ++bzCounter, b.ty);
      return this.unify(mkA(a, z), substBound(b.body, z));
    }
    const sa = stripApp(a);
    const sb = stripApp(b);
    if (sa.head.k === 'V' && this.bindable(sa.head.name)) {
      if (sb.head.k === 'V' && sb.head.name === sa.head.name && sa.args.length === sb.args.length) {
        let ok = true;
        for (let i = 0; i < sa.args.length && ok; i++) ok = this.unify(sa.args[i], sb.args[i]);
        if (ok) return true;
      }
      return this.flex(sa.head, sa.args, b);
    }
    if (sb.head.k === 'V' && this.bindable(sb.head.name)) return this.flex(sb.head, sb.args, a);
    return this.rigid(sa.head, sa.args, sb.head, sb.args);
  }

  private rigid(ha: Term, aa: Term[], hb: Term, ab: Term[]): boolean {
    // numeral vs Suc
    if (aa.length === 0 && ab.length === 1 && hb.k === 'C' && hb.name === 'Suc') return this.sucNum(ha, ab[0]);
    if (ab.length === 0 && aa.length === 1 && ha.k === 'C' && ha.name === 'Suc') return this.sucNum(hb, aa[0]);
    if (aa.length !== ab.length) return false;
    if (ha.k !== hb.k) return false;
    switch (ha.k) {
      case 'C':
        if (ha.name !== (hb as typeof ha).name) return false;
        if (!tunify(ha.ty, (hb as typeof ha).ty, this.s.ty)) return false;
        break;
      case 'F':
        if (ha.name !== (hb as typeof ha).name) return false;
        if (!tunify(ha.ty, (hb as typeof ha).ty, this.s.ty)) return false;
        break;
      case 'V':
        if (ha.name !== (hb as typeof ha).name) return false;
        break;
      case 'B':
        if (ha.i !== (hb as typeof ha).i) return false;
        break;
      default:
        return false;
    }
    for (let i = 0; i < aa.length; i++) if (!this.unify(aa[i], ab[i])) return false;
    return true;
  }

  private sucNum(numT: Term, arg: Term): boolean {
    const v = numVal(numT);
    if (v === null || v <= 0) return false;
    if (numT.k === 'C' && !typeEq(tsubst(numT.ty, this.s.ty), natT)) {
      if (!tunify(numT.ty, natT, this.s.ty)) return false;
    }
    return this.unify(arg, mkC('#' + (v - 1), natT));
  }

  private flex(v: Term & { k: 'V' }, args: Term[], t: Term): boolean {
    const tI = inst(t, this.s);
    if (args.length === 0) {
      if (tI.k === 'V' && tI.name === v.name) return true;
      if (occursVar(v.name, tI, this.s)) return false;
      if (binderFrees(tI).size) return false;
      if (this.opts.canBind && !this.opts.canBind(v.name, tI)) return false;
      let tt: Type;
      try {
        tt = this.tyOf(tI);
      } catch {
        return false;
      }
      if (!tunify(v.ty, tt, this.s.ty)) return false;
      this.s.t.set(v.name, tI);
      return true;
    }
    const argsN = args.map((a) => headNorm(a, this.s));
    const isPattern =
      argsN.every((a) => a.k === 'F' && a.name.startsWith(BZ)) && new Set(argsN.map((a) => (a as { name: string }).name)).size === argsN.length;
    if (isPattern) {
      const allowed = new Set(argsN.map((a) => (a as { name: string }).name));
      for (const bf of binderFrees(tI)) if (!allowed.has(bf)) return this.flexFallback(v, args, t);
      if (occursVar(v.name, tI, this.s)) return false;
      let body = tI;
      for (let i = argsN.length - 1; i >= 0; i--) {
        const a = argsN[i] as Term & { k: 'F' };
        body = mkL('x', a.ty, abstractOver(body, a));
      }
      if (this.opts.canBind && !this.opts.canBind(v.name, body)) return false;
      let tt: Type;
      try {
        tt = this.tyOf(body);
      } catch {
        return false;
      }
      if (!tunify(v.ty, tt, this.s.ty)) return false;
      this.s.t.set(v.name, betaNorm(body));
      return true;
    }
    return this.flexFallback(v, args, t);
  }

  // first-order approximation for non-pattern flex terms
  private flexFallback(v: Term & { k: 'V' }, args: Term[], t: Term): boolean {
    const { head, args: targs } = stripApp(headNorm(t, this.s));
    if (targs.length < args.length) {
      // try projection: ?F a = a  (when t equals some argument)
      return false;
    }
    const k = targs.length - args.length;
    const tf = mkApps(head, targs.slice(0, k));
    if (!this.flex(v, [], tf)) return false;
    for (let i = 0; i < args.length; i++) if (!this.unify(args[i], targs[k + i])) return false;
    return true;
  }
}

export function unify(a: Term, b: Term, s: Subst = emptySubst(), opts: UnifyOpts = {}): Subst | null {
  const u = new Unifier(copySubst(s), opts);
  try {
    return u.unify(a, b) ? u.s : null;
  } catch {
    return null;
  }
}

/** One-sided matching: only variables of `pattern` may be instantiated. */
export function match(pattern: Term, term: Term, s: Subst = emptySubst(), patVars?: Set<string>): Subst | null {
  const pv = patVars ?? collectVarNames(pattern);
  return unify(pattern, term, s, { bindable: (n) => pv.has(n) });
}

export function collectVarNames(t: Term, acc: Set<string> = new Set()): Set<string> {
  switch (t.k) {
    case 'V':
      acc.add(t.name);
      break;
    case 'L':
      collectVarNames(t.body, acc);
      break;
    case 'A':
      collectVarNames(t.f, acc);
      collectVarNames(t.a, acc);
      break;
  }
  return acc;
}

/** Instantiate the term then also apply type substitution to all type annotations. */
export function instFull(t: Term, s: Subst): Term {
  const r = inst(t, s);
  return s.ty.size ? mapTypes(r, (ty) => tsubst(ty, s.ty)) : r;
}

export { funT };
