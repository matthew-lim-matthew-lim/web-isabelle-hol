// Theory context: constants, types, datatypes, theorems, simp sets.
import {
  Term,
  Type,
  tcon,
  tvar,
  funT,
  funTs,
  boolT,
  natT,
  listT,
  setT,
  prodT,
  mkF,
  mkV,
  mapTypes,
  freshTS,
  tmapV,
  EngineError,
  frees,
  vars,
} from './terms';

export interface Thm {
  name: string;
  prop: Term; // may contain schematic Vars (generalised) or Frees (local facts)
  global?: boolean; // global theorems get fresh type variables on instantiation
}

export interface Ctor {
  name: string;
  argTys: Type[]; // in terms of datatype params (V types)
}

export interface Datatype {
  name: string;
  params: string[]; // type variable names e.g. 'a
  ctors: Ctor[];
  caseConst: string;
}

export interface FunEq {
  lhsArgs: Term[]; // patterns (Frees as pattern vars)
  rhs: Term;
  vars: Term[]; // pattern variables (Frees)
}

export interface FunInfo {
  name: string;
  eqs: FunEq[]; // completed, non-overlapping equations
  ty: Type;
  arity: number;
}

export interface ConstInfo {
  ty: Type; // scheme with V type vars
  numeric?: boolean; // overloaded arithmetic: defaults type to nat
}

export class Theory {
  consts = new Map<string, ConstInfo>();
  types = new Map<string, number>(); // name -> arity
  typeSyns = new Map<string, { params: string[]; rhs: Type }>();
  datatypes = new Map<string, Datatype>();
  ctorOf = new Map<string, string>();
  thms = new Map<string, Thm[]>();
  simpNames = new Set<string>(); // keys "name" or "name(i)" of theorems in default simpset
  simpRules: Thm[] = [];
  introRules: Thm[] = [];
  elimRules: Thm[] = [];
  destRules: Thm[] = [];
  splitRules = new Set<string>();
  funs = new Map<string, FunInfo>();
  defs = new Map<string, Thm[]>();
  name = 'Scratch';

  clone(): Theory {
    const t = new Theory();
    t.consts = new Map(this.consts);
    t.types = new Map(this.types);
    t.typeSyns = new Map(this.typeSyns);
    t.datatypes = new Map(this.datatypes);
    t.ctorOf = new Map(this.ctorOf);
    t.thms = new Map(this.thms);
    t.simpNames = new Set(this.simpNames);
    t.simpRules = [...this.simpRules];
    t.introRules = [...this.introRules];
    t.elimRules = [...this.elimRules];
    t.destRules = [...this.destRules];
    t.splitRules = new Set(this.splitRules);
    t.funs = new Map(this.funs);
    t.defs = new Map(this.defs);
    t.name = this.name;
    return t;
  }

  addConst(name: string, ty: Type, numeric = false) {
    this.consts.set(name, { ty, numeric });
  }

  addThms(name: string, ths: Thm[]) {
    this.thms.set(name, ths);
  }

  addSimp(th: Thm) {
    this.simpRules = this.simpRules.filter((r) => r.name !== th.name || r.prop !== th.prop);
    this.simpRules.push(th);
  }
  delSimp(name: string) {
    this.simpRules = this.simpRules.filter((r) => r.name !== name && !r.name.startsWith(name + '('));
  }

  isCtor(name: string): boolean {
    return this.ctorOf.has(name);
  }

  /** datatype of a type, if it is a datatype */
  datatypeOf(ty: Type): Datatype | undefined {
    if (ty.k !== 'T') return undefined;
    return this.datatypes.get(ty.name);
  }

  /** Instantiated constructor argument types for a datatype type instance. */
  ctorArgTys(dt: Datatype, ctor: Ctor, ty: Type): Type[] {
    const inst = new Map<string, Type>();
    if (ty.k === 'T') dt.params.forEach((p, i) => inst.set(p, ty.args[i]));
    return ctor.argTys.map((a) => tmapV(a, (n) => inst.get(n) ?? tvar(n)));
  }

  resolveTypeName(name: string, args: Type[]): Type {
    const syn = this.typeSyns.get(name);
    if (syn) {
      if (syn.params.length !== args.length) throw new EngineError(`Bad number of arguments for type synonym "${name}"`);
      const m = new Map<string, Type>();
      syn.params.forEach((p, i) => m.set(p, args[i]));
      return tmapV(syn.rhs, (n) => m.get(n) ?? tvar(n));
    }
    const ar = this.types.get(name);
    if (ar === undefined) throw new EngineError(`Undefined type name: "${name}"`);
    if (ar !== args.length) throw new EngineError(`Bad number of arguments for type constructor: "${name}"`);
    return tcon(name, args);
  }
}

/** Instantiate a theorem for use: frees stay (local facts), schematic vars get fresh names, type vars fresh if global. */
let instCounter = 0;
export function instThm(th: Thm): Term {
  instCounter++;
  const tmap = new Map<string, Type>();
  const tyf = (ty: Type): Type =>
    th.global
      ? tmapV(ty, (n) => {
          let r = tmap.get(n);
          if (!r) {
            r = freshTS();
            tmap.set(n, r);
          }
          return r;
        })
      : ty;
  const rename = (t: Term): Term => {
    switch (t.k) {
      case 'V':
        return mkV(t.name.replace(/__\d+$/, '') + '__' + instCounter, tyf(t.ty));
      case 'A':
        return { k: 'A', f: rename(t.f), a: rename(t.a) };
      case 'L':
        return { k: 'L', x: t.x, ty: tyf(t.ty), body: rename(t.body) };
      case 'C':
      case 'F':
        return th.global ? { ...t, ty: tyf(t.ty) } : t;
      default:
        return t;
    }
  };
  return rename(th.prop);
}

/** Turn frees (not in keep) into schematic variables: theorem export. */
export function generalize(t: Term, keep: Set<string> = new Set()): Term {
  const fs = frees(t);
  const used = new Set([...vars(t).keys()].map((n) => n.replace(/__\d+$/, '')));
  const m = new Map<string, Term>();
  for (const [n, f] of fs) {
    if (keep.has(n)) continue;
    let nm = n;
    while (used.has(nm)) nm = nm + "'";
    used.add(nm);
    m.set(n, mkV(nm, (f as { ty: Type }).ty));
  }
  const go = (u: Term): Term => {
    switch (u.k) {
      case 'F':
        return m.get(u.name) ?? u;
      case 'A':
        return { k: 'A', f: go(u.f), a: go(u.a) };
      case 'L':
        return { k: 'L', x: u.x, ty: u.ty, body: go(u.body) };
      default:
        return u;
    }
  };
  return go(t);
}

/** Replace schematic variables by frees (e.g. for using a theorem as a goal). */
export function varsToFrees(t: Term): Term {
  switch (t.k) {
    case 'V':
      return mkF(t.name.replace(/__\d+$/, ''), t.ty);
    case 'A':
      return { k: 'A', f: varsToFrees(t.f), a: varsToFrees(t.a) };
    case 'L':
      return { k: 'L', x: t.x, ty: t.ty, body: varsToFrees(t.body) };
    default:
      return t;
  }
}

export function baseTheory(): Theory {
  const thy = new Theory();
  thy.name = 'Main';
  const a = tvar("'a");
  const b = tvar("'b");
  const c = tvar("'c");
  for (const [n, ar] of [
    ['bool', 0],
    ['fun', 2],
    ['nat', 0],
    ['int', 0],
    ['set', 1],
    ['unit', 0],
  ] as [string, number][])
    thy.types.set(n, ar);
  const B = boolT;
  const bb = funT(B, B);
  const bbb = funT(B, bb);
  thy.addConst('True', B);
  thy.addConst('False', B);
  thy.addConst('Not', bb);
  thy.addConst('conj', bbb);
  thy.addConst('disj', bbb);
  thy.addConst('imp', bbb);
  thy.addConst('==>', bbb);
  thy.addConst('eq', funTs([a, a], B));
  thy.addConst('!!', funT(funT(a, B), B));
  thy.addConst('All', funT(funT(a, B), B));
  thy.addConst('Ex', funT(funT(a, B), B));
  thy.addConst('Ex1', funT(funT(a, B), B));
  thy.addConst('Eps', funT(funT(a, B), a));
  thy.addConst('The', funT(funT(a, B), a));
  thy.addConst('If', funTs([B, a, a], a));
  thy.addConst('Let', funTs([a, funT(a, b)], b));
  thy.addConst('Unity', tcon('unit'));
  thy.addConst('undefined', a);
  for (const op of ['plus', 'minus', 'times', 'div', 'mod', 'divide']) thy.addConst(op, funTs([a, a], a), true);
  thy.addConst('uminus', funT(a, a), true);
  thy.addConst('power', funTs([a, natT], a), true);
  thy.addConst('less', funTs([a, a], B), true);
  thy.addConst('less_eq', funTs([a, a], B), true);
  thy.addConst('dvd', funTs([a, a], B), true);
  thy.addConst('max', funTs([a, a], a), true);
  thy.addConst('min', funTs([a, a], a), true);
  thy.addConst('abs', funT(a, a), true);
  thy.addConst('Suc', funT(natT, natT));
  thy.addConst('int', funT(natT, tcon('int')));
  thy.addConst('comp', funTs([funT(b, c), funT(a, b)], funT(a, c)));
  thy.addConst('id', funT(a, a));
  // sets
  const sa = setT(a);
  thy.addConst('member', funTs([a, sa], B));
  thy.addConst('Collect', funT(funT(a, B), sa));
  thy.addConst('bot_set', sa);
  thy.addConst('UNIV', sa);
  thy.addConst('insert', funTs([a, sa], sa));
  thy.addConst('union', funTs([sa, sa], sa));
  thy.addConst('inter', funTs([sa, sa], sa));
  thy.addConst('subset_eq', funTs([sa, sa], B));
  thy.addConst('subset', funTs([sa, sa], B));
  thy.addConst('image', funTs([funT(a, b), sa], setT(b)));
  // nat as a datatype with constructors 0 and Suc
  thy.datatypes.set('nat', {
    name: 'nat',
    params: [],
    ctors: [
      { name: '#0', argTys: [] },
      { name: 'Suc', argTys: [natT] },
    ],
    caseConst: 'case_nat',
  });
  thy.ctorOf.set('Suc', 'nat');
  thy.addConst('case_nat', funTs([b, funT(natT, b), natT], b));
  thy.datatypes.set('bool', {
    name: 'bool',
    params: [],
    ctors: [
      { name: 'True', argTys: [] },
      { name: 'False', argTys: [] },
    ],
    caseConst: 'case_bool',
  });
  thy.addConst('case_bool', funTs([b, b, B], b));
  void listT;
  void prodT;
  return thy;
}
