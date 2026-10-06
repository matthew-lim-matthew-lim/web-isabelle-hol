// Type inference (Hindley-Milner style) from preterms to typed terms.
import { PT, PTy, parseTerm, parseType } from './syntax';
import {
  Term,
  Type,
  TSubst,
  tsubst,
  tunify,
  freshTS,
  funT,
  boolT,
  natT,
  tvar,
  tmapV,
  mkC,
  mkF,
  mkV,
  mkB,
  mkL,
  mkA,
  mkApps,
  mapTypes,
  EngineError,
  typeOf,
  tsvarsOf,
  tvarsOf,
  isFunT,
  stripFunT,
  substFrees,
  abstractOver,
} from './terms';
import { Theory } from './theory';
import { printType } from './printer';

export interface TermCtx {
  thy: Theory;
  fixed: Map<string, Type>; // fixed (local) variables
  abbrevs: Map<string, Term>; // ?x term abbreviations (let, ?case, ?thesis)
  dots?: Term;
}

export function emptyCtx(thy: Theory): TermCtx {
  return { thy, fixed: new Map(), abbrevs: new Map() };
}

export class Elab {
  s: TSubst = new Map();
  numeric = new Set<number>();
  newFrees = new Map<string, Type>();
  dummyCount = 0;
  constructor(public ctx: TermCtx) {}

  ty(p: PTy, tvEnv?: Map<string, Type>): Type {
    switch (p.t) {
      case 'tvar':
        return tvEnv?.get(p.name) ?? tvar(p.name);
      case 'tdummy':
        return freshTS();
      case 'tcon':
        return this.ctx.thy.resolveTypeName(
          p.name,
          p.args.map((a) => this.ty(a, tvEnv)),
        );
    }
  }

  private unify(a: Type, b: Type, what: () => string) {
    if (!tunify(a, b, this.s)) {
      throw new EngineError(
        `Type unification failed: Clash of types "${printType(tsubst(a, this.s))}" and "${printType(tsubst(b, this.s))}"\n${what()}`,
      );
    }
  }

  private constTerm(name: string): Term {
    const ci = this.ctx.thy.consts.get(name);
    if (!ci) throw new EngineError(`Undefined constant: "${name}"`);
    const m = new Map<string, Type>();
    const ty = tmapV(ci.ty, (n) => {
      let r = m.get(n);
      if (!r) {
        r = freshTS();
        m.set(n, r);
        if (ci.numeric && n === "'a") this.numeric.add((r as { id: number }).id);
      }
      return r;
    });
    return mkC(name, ty);
  }

  elab(p: PT, env: { name: string; ty: Type }[]): Term {
    switch (p.t) {
      case 'num': {
        const ty = freshTS();
        this.numeric.add((ty as { id: number }).id);
        return mkC('#' + p.n, ty);
      }
      case 'const': {
        if (p.name === 'iff') {
          return mkC('eq', funT(boolT, funT(boolT, boolT)));
        }
        const fxc = this.ctx.fixed.get(p.name);
        if (fxc && !this.ctx.thy.consts.has(p.name)) return mkF(p.name, fxc);
        return this.constTerm(p.name);
      }
      case 'id': {
        for (let i = env.length - 1; i >= 0; i--) if (env[i].name === p.name) return mkB(env.length - 1 - i);
        const fx = this.ctx.fixed.get(p.name);
        if (fx) return mkF(p.name, fx);
        if (this.ctx.thy.consts.has(p.name)) return this.constTerm(p.name);
        let ty = this.newFrees.get(p.name);
        if (!ty) {
          ty = freshTS();
          this.newFrees.set(p.name, ty);
        }
        return mkF(p.name, ty);
      }
      case 'var': {
        const ab = this.ctx.abbrevs.get(p.name);
        if (ab) return ab;
        const key = '?' + p.name;
        let ty = this.newFrees.get(key);
        if (!ty) {
          ty = freshTS();
          this.newFrees.set(key, ty);
        }
        return mkV(p.name, ty);
      }
      case 'dummy':
        return mkV('_dummy' + ++this.dummyCount, freshTS());
      case 'dots':
        if (!this.ctx.dots) throw new EngineError('Unbound "..." (no previous calculational statement)');
        return this.ctx.dots;
      case 'constraint': {
        const t = this.elab(p.e, env);
        this.unify(this.typeOfE(t, env), this.ty(p.ty), () => 'in type constraint');
        return t;
      }
      case 'app': {
        const f = this.elab(p.f, env);
        const a = this.elab(p.a, env);
        const ft = this.typeOfE(f, env);
        const at = this.typeOfE(a, env);
        const r = freshTS();
        this.unify(ft, funT(at, r), () => 'Operator applied to wrong argument type');
        return mkA(f, a);
      }
      case 'abs': {
        if (p.pat) return this.elabPatAbs(p.pat, p.body, env);
        const ty = p.ty ? this.ty(p.ty) : freshTS();
        const body = this.elab(p.body, [...env, { name: p.x, ty }]);
        return mkL(p.x, ty, body);
      }
      case 'q': {
        const ty = p.ty ? this.ty(p.ty) : freshTS();
        const body = this.elab(p.body, [...env, { name: p.x, ty }]);
        const qc = this.constTerm(p.q);
        const lam = mkL(p.x, ty, body);
        const bt = this.typeOfE(body, [...env, { name: p.x, ty }]);
        if (p.q === 'Eps' || p.q === 'The') this.unify(bt, boolT, () => 'body of binder must be boolean');
        else this.unify(bt, boolT, () => 'body of quantifier must be boolean');
        this.unify(this.typeOfE(qc, env), funT(funT(ty, boolT), freshTS()), () => 'quantifier');
        return mkA(qc, lam);
      }
      case 'case':
        return this.elabCase(p.e, p.clauses, env);
    }
  }

  private elabPatAbs(pat: PT, body: PT, env: { name: string; ty: Type }[]): Term {
    // λ(x, y). body  ==>  case_prod (λx y. body)
    const build = (pt: PT, inner: PT): PT => {
      if (pt.t === 'id') return { t: 'abs', x: pt.name, body: inner };
      if (pt.t === 'constraint' && pt.e.t === 'id') return { t: 'abs', x: pt.e.name, ty: pt.ty, body: inner };
      if (pt.t === 'app' && pt.f.t === 'app' && pt.f.f.t === 'const' && pt.f.f.name === 'Pair') {
        const curried = build(pt.f.a, build(pt.a, inner));
        return { t: 'app', f: { t: 'const', name: 'case_prod' }, a: curried };
      }
      throw new EngineError('Unsupported pattern in λ-abstraction');
    };
    return this.elab(build(pat, body), env);
  }

  private elabCase(e: PT, clauses: { pat: PT; rhs: PT }[], env: { name: string; ty: Type }[]): Term {
    const thy = this.ctx.thy;
    const headOf = (pt: PT): { ctor: string | null; args: PT[] } => {
      const args: PT[] = [];
      while (pt.t === 'app') {
        args.unshift(pt.a);
        pt = pt.f;
      }
      if (pt.t === 'num') return { ctor: pt.n === 0 ? '#0' : null, args };
      if (pt.t === 'const' && thy.isCtor(pt.name)) return { ctor: pt.name, args };
      if (pt.t === 'id' && thy.isCtor(pt.name)) return { ctor: pt.name, args };
      return { ctor: null, args };
    };
    let dtName: string | undefined;
    for (const c of clauses) {
      const h = headOf(c.pat);
      if (h.ctor) {
        dtName = h.ctor === '#0' ? 'nat' : thy.ctorOf.get(h.ctor);
        break;
      }
    }
    if (!dtName) {
      // only variable pattern: case e of x => rhs   ==> Let
      const c = clauses[0];
      if (c.pat.t === 'id') return this.elab({ t: 'app', f: { t: 'app', f: { t: 'const', name: 'Let' }, a: e }, a: { t: 'abs', x: c.pat.name, body: c.rhs } }, env);
      throw new EngineError('Bad case pattern');
    }
    const dt = thy.datatypes.get(dtName)!;
    const fns: PT[] = [];
    for (const ctor of dt.ctors) {
      let fn: PT | undefined;
      for (const c of clauses) {
        const h = headOf(c.pat);
        if (h.ctor === ctor.name) {
          if (h.args.length !== ctor.argTys.length) throw new EngineError(`Wrong number of arguments for constructor ${ctor.name} in case pattern`);
          let body = c.rhs;
          for (let i = h.args.length - 1; i >= 0; i--) {
            const a = h.args[i];
            if (a.t === 'id') body = { t: 'abs', x: a.name, body };
            else if (a.t === 'dummy') body = { t: 'abs', x: '_', body };
            else throw new EngineError('Nested patterns in case expressions are not supported');
          }
          fn = body;
          break;
        }
        if (!h.ctor && (c.pat.t === 'id' || c.pat.t === 'dummy')) {
          // catch-all: substitute variable by constructor application
          const argNames = ctor.argTys.map((_, i) => `__a${i}`);
          let ctorApp: PT = ctor.name === '#0' ? { t: 'num', n: 0 } : { t: 'const', name: ctor.name };
          for (const an of argNames) ctorApp = { t: 'app', f: ctorApp, a: { t: 'id', name: an } };
          let body: PT = c.pat.t === 'id' ? { t: 'app', f: { t: 'abs', x: c.pat.name, body: c.rhs }, a: ctorApp } : c.rhs;
          for (let i = argNames.length - 1; i >= 0; i--) body = { t: 'abs', x: argNames[i], body };
          fn = body;
          break;
        }
      }
      if (!fn) {
        fn = { t: 'const', name: 'undefined' };
        for (let i = 0; i < ctor.argTys.length; i++) fn = { t: 'abs', x: '_', body: fn };
      }
      fns.push(fn);
    }
    let r: PT = { t: 'const', name: dt.caseConst };
    for (const f of fns) r = { t: 'app', f: r, a: f };
    r = { t: 'app', f: r, a: e };
    return this.elab(r, env);
  }

  typeOfE(t: Term, env: { name: string; ty: Type }[]): Type {
    try {
      return tsubst(typeOf(t, env.map((e) => e.ty)), this.s);
    } catch {
      // application with not-yet-resolved function types: resolve through subst
      return this.typeOfSubst(t, env.map((e) => e.ty));
    }
  }

  private typeOfSubst(t: Term, env: Type[]): Type {
    switch (t.k) {
      case 'C':
      case 'F':
      case 'V':
        return tsubst(t.ty, this.s);
      case 'B':
        return tsubst(env[env.length - 1 - t.i], this.s);
      case 'L':
        return funT(tsubst(t.ty, this.s), this.typeOfSubst(t.body, [...env, t.ty]));
      case 'A': {
        const ft = this.typeOfSubst(t.f, env);
        if (isFunT(ft)) return tsubst(ft.args[1], this.s);
        const r = freshTS();
        tunify(ft, funT(freshTS(), r), this.s);
        return r;
      }
    }
  }

  /** Apply substitution, default numerics to nat, and generalise remaining type vars to fixed type vars. */
  finish(ts: Term[], used: Set<string> = new Set()): Term[] {
    for (const id of this.numeric) {
      const r = tsubst({ k: 'S', id }, this.s);
      if (r.k === 'S') this.s.set(r.id, natT);
    }
    const res = ts.map((t) => mapTypes(t, (ty) => tsubst(ty, this.s)));
    // collect remaining S vars
    const usedNames = new Set(used);
    for (const ty of this.ctx.fixed.values()) tvarsOf(tsubst(ty, this.s), usedNames);
    const collect = (t: Term, acc: Set<number>, accV: Set<string>) => {
      mapTypes(t, (ty) => {
        tsvarsOf(ty, acc);
        tvarsOf(ty, accV);
        return ty;
      });
    };
    const svs = new Set<number>();
    for (const t of res) collect(t, svs, usedNames);
    if (svs.size === 0) return res;
    const names = "abcdefghijklmnopqrstuvwxyz".split('');
    let ni = 0;
    for (const id of svs) {
      let nm: string;
      do {
        nm = "'" + names[ni % 26] + (ni >= 26 ? String(Math.floor(ni / 26)) : '');
        ni++;
      } while (usedNames.has(nm));
      usedNames.add(nm);
      this.s.set(id, tvar(nm));
    }
    return ts.map((t) => mapTypes(t, (ty) => tsubst(ty, this.s)));
  }

  /** Resolved types of fixed variables that were still schematic. */
  updatedFixed(): Map<string, Type> {
    const m = new Map<string, Type>();
    for (const [k, v] of this.ctx.fixed) m.set(k, tsubst(v, this.s));
    return m;
  }
}

/** Read terms (strings) in a context, sharing free variables; constrains each to `ty` if given. */
export function readTerms(ctx: TermCtx, srcs: { src: string; ty?: Type }[]): { terms: Term[]; newFrees: Map<string, Type>; fixed: Map<string, Type> } {
  const e = new Elab(ctx);
  const raw: Term[] = [];
  for (const { src, ty } of srcs) {
    const pt = parseTerm(src);
    const t = e.elab(pt, []);
    if (ty) {
      const tt = e.typeOfE(t, []);
      if (!tunify(tt, ty, e.s))
        throw new EngineError(`Type unification failed: Clash of types "${printType(tsubst(tt, e.s))}" and "${printType(ty)}"\nTerm: ${src}`);
    }
    raw.push(t);
  }
  const terms = e.finish(raw);
  const newFrees = new Map<string, Type>();
  for (const [k, v] of e.newFrees) newFrees.set(k, tsubst(v, e.s));
  return { terms, newFrees, fixed: e.updatedFixed() };
}

export function readProp(ctx: TermCtx, src: string): Term {
  return readTerms(ctx, [{ src, ty: boolT }]).terms[0];
}

export function readTerm(ctx: TermCtx, src: string): Term {
  return readTerms(ctx, [{ src }]).terms[0];
}

export function readType(thy: Theory, src: string): Type {
  const e = new Elab(emptyCtx(thy));
  return e.ty(parseType(src));
}

export { mkApps, stripFunT, substFrees, abstractOver, mkF };
