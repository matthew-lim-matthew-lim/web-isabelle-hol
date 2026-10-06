// Proof methods: parsing of method expressions and their evaluation on proof states.
import { OTok, TokReader, OuterError, Command } from './outer';
import {
  Term,
  Type,
  EngineError,
  destApp,
  stripApp,
  isConst,
  termEq,
  mkNot,
  betaNorm,
  typeOf,
  tsubst,
  tunify,
  mapTypes,
  mkEq,
  boolT,
  mkMetaImp,
  frees,
} from './terms';
import { Goal, goalFrees, termToGoal } from './goal';
import { Theory, Thm, instThm, FunInfo } from './theory';
import { buildSimpset, simpGoal, Simpset, SimpLimit } from './simp';
import {
  resolveRule,
  eresolveRule,
  dresolveRule,
  assumptionTac,
  closeByFact,
  inductTac,
  funInductTac,
  casesTac,
  substTac,
  instGoal,
  CaseInfo,
  TacResult,
  decomposeRule,
} from './tactics';
import { autoGoal, blastGoal, clarify, safeStep, sameGoals, tryArith } from './classical';
import { linarith } from './arith';
import { unify, inst, emptySubst, collectVarNames, Subst } from './unify';

export type Meth =
  | { m: 'name'; name: string; args: OTok[]; from: number; to: number }
  | { m: 'seq'; ms: Meth[] }
  | { m: 'all'; a: Meth; b: Meth }
  | { m: 'alt'; ms: Meth[] }
  | { m: 'rep'; inner: Meth }
  | { m: 'try'; inner: Meth }
  | { m: 'sel'; inner: Meth; n: number };

export class MethodFail extends EngineError {}

// ---------------- parsing ----------------

/** Parse a method in "top" position: name | (expr) | - , plus postfix modifiers */
export function parseMethodTop(r: TokReader): Meth {
  let m: Meth;
  const t = r.peek();
  if (!t) r.fail('method expected');
  if (t.kind === 'sym' && t.v === '(') {
    r.next();
    m = parseMethodExpr(r);
    r.expectSym(')');
  } else if (t.kind === 'sym' && t.v === '-') {
    r.next();
    m = { m: 'name', name: '-', args: [], from: t.from, to: t.to };
  } else if (t.kind === 'ident') {
    r.next();
    m = { m: 'name', name: t.v, args: [], from: t.from, to: t.to };
  } else r.fail('method expected');
  return parsePostfix(r, m);
}

function parsePostfix(r: TokReader, m: Meth): Meth {
  for (;;) {
    if (r.isSym('+')) {
      r.next();
      m = { m: 'rep', inner: m };
    } else if (r.isSym('?')) {
      r.next();
      m = { m: 'try', inner: m };
    } else if (r.isSym('[') && r.peek(1)?.kind === 'nat' && r.isSym(']', 2)) {
      r.next();
      const n = Number(r.next().v);
      r.next();
      m = { m: 'sel', inner: m, n };
    } else break;
  }
  return m;
}

function parseMethodExpr(r: TokReader): Meth {
  const alts: Meth[] = [parseSeq(r)];
  while (r.isSym('|')) {
    r.next();
    alts.push(parseSeq(r));
  }
  return alts.length === 1 ? alts[0] : { m: 'alt', ms: alts };
}

function parseSeq(r: TokReader): Meth {
  let left = parseSingle(r);
  const seq: Meth[] = [left];
  for (;;) {
    if (r.isSym(',')) {
      r.next();
      seq.push(parseSingle(r));
    } else if (r.isSym(';')) {
      r.next();
      const right = parseSingle(r);
      left = { m: 'all', a: seq.length === 1 ? seq[0] : { m: 'seq', ms: [...seq] }, b: right };
      seq.length = 0;
      seq.push(left);
    } else break;
  }
  return seq.length === 1 ? seq[0] : { m: 'seq', ms: seq };
}

function parseSingle(r: TokReader): Meth {
  const t = r.peek();
  if (!t) r.fail('method expected');
  if (t.kind === 'sym' && t.v === '(') {
    r.next();
    const m = parseMethodExpr(r);
    r.expectSym(')');
    return parsePostfix(r, m);
  }
  if (t.kind === 'sym' && t.v === '-') {
    r.next();
    return parsePostfix(r, { m: 'name', name: '-', args: [], from: t.from, to: t.to });
  }
  if (t.kind !== 'ident') r.fail('method name expected');
  r.next();
  // arguments: tokens until , ; | ) at depth 0, or postfix + ? at depth 0 directly followed by delimiter
  const args: OTok[] = [];
  let depth = 0;
  for (;;) {
    const a = r.peek();
    if (!a) break;
    if (depth === 0 && a.kind === 'sym' && [',', ';', '|', ')'].includes(a.v)) break;
    if (depth === 0 && a.kind === 'sym' && (a.v === '+' || a.v === '?')) {
      const nx = r.peek(1);
      if (!nx || (nx.kind === 'sym' && [',', ';', '|', ')', '+', '?', '['].includes(nx.v))) break;
    }
    if (a.kind === 'sym' && (a.v === '(' || a.v === '[')) depth++;
    if (a.kind === 'sym' && (a.v === ')' || a.v === ']')) depth--;
    args.push(r.next());
  }
  return parsePostfix(r, { m: 'name', name: t.v, args, from: t.from, to: t.to });
}

// ---------------- fact references ----------------

export interface FactRef {
  name: string;
  sel?: number[]; // 1-based indices
  attrs: { name: string; args: OTok[] }[];
  literal?: string; // ‹prop› fact literal
  tok: OTok;
}

export function parseFactRefs(r: TokReader, stopWords: Set<string> = new Set()): FactRef[] {
  const refs: FactRef[] = [];
  for (;;) {
    const t = r.peek();
    if (!t) break;
    if (t.kind === 'ident' && stopWords.has(t.v)) break;
    if (t.kind === 'ident' && r.isSym(':', 1)) break; // next modifier section
    if (t.kind === 'ident' && (r.isIdent('add', 1) || r.isIdent('del', 1) || r.isIdent('only', 1)) && r.isSym(':', 2)) break;
    if (t.kind === 'ident' && r.isSym('!', 1) && r.isSym(':', 2)) break;
    if (t.kind === 'cartouche') {
      r.next();
      refs.push({ name: '', literal: t.v, attrs: parseAttrsOpt(r), tok: t });
      continue;
    }
    if (t.kind === 'ident' || (t.kind === 'nat' && false)) {
      r.next();
      let sel: number[] | undefined;
      if (r.isSym('(') && r.peek(1)?.kind === 'nat') {
        r.next();
        sel = [];
        while (!r.isSym(')')) {
          const a = r.next();
          if (a.kind !== 'nat') r.fail('bad fact selection');
          const lo = Number(a.v);
          if (r.isSym('-')) {
            r.next();
            if (r.peek()?.kind === 'nat') {
              const hi = Number(r.next().v);
              for (let i = lo; i <= hi; i++) sel.push(i);
            } else sel.push(-lo); // open range marker
          } else sel.push(lo);
          if (r.isSym(',')) r.next();
        }
        r.expectSym(')');
      }
      refs.push({ name: t.v, sel, attrs: parseAttrsOpt(r), tok: t });
      continue;
    }
    break;
  }
  return refs;
}

export function parseAttrsOpt(r: TokReader): { name: string; args: OTok[] }[] {
  if (!r.isSym('[')) return [];
  r.next();
  const attrs: { name: string; args: OTok[] }[] = [];
  while (!r.isSym(']')) {
    const n = r.next();
    if (n.kind !== 'ident') r.fail('attribute name expected');
    const args: OTok[] = [];
    let depth = 0;
    for (;;) {
      const a = r.peek();
      if (!a) r.fail('unclosed attribute list');
      if (depth === 0 && a.kind === 'sym' && (a.v === ',' || a.v === ']')) break;
      if (a.kind === 'sym' && (a.v === '[' || a.v === '(')) depth++;
      if (a.kind === 'sym' && (a.v === ']' || a.v === ')')) depth--;
      args.push(r.next());
    }
    attrs.push({ name: n.v, args });
    if (r.isSym(',')) r.next();
  }
  r.expectSym(']');
  return attrs;
}

// ---------------- environment ----------------

export interface MethodEnv {
  thy: Theory;
  resolveFacts(refs: FactRef[]): Thm[];
  readTerm(src: string, goal?: Goal): Term;
  getFun(name: string): FunInfo | undefined;
  getInductive(name: string): InductiveInfo | undefined;
  stepLimit?: number;
}

export interface InductiveInfo {
  name: string;
  arity: number;
  intros: Thm[];
}

export interface ProofState {
  goals: Goal[];
  facts: Thm[]; // chained facts
  cases?: CaseInfo[];
}

function factProps(ths: Thm[]): Term[] {
  return ths.map((t) => instThm(t));
}

function insertFacts(g: Goal, facts: Thm[]): Goal {
  if (!facts.length) return g;
  const props = facts.map((f) => instThm(f)).filter((p) => collectVarNames(p).size === 0);
  const more = props.filter((p) => !g.prems.some((q) => termEq(p, q)));
  return { ...g, prems: [...g.prems, ...more] };
}

function argReader(m: Meth & { m: 'name' }) {
  const cmd: Command = { kw: m.name, toks: m.args, from: m.from, to: m.args.length ? m.args[m.args.length - 1].to : m.to };
  return new TokReader(m.args, cmd);
}

interface Mods {
  simpAdd: FactRef[];
  simpDel: FactRef[];
  simpOnly: FactRef[] | null;
  split: FactRef[];
  intro: FactRef[];
  dest: FactRef[];
  elim: FactRef[];
  plain: FactRef[];
  arbitrary: OTok[];
  rule: FactRef[];
  terms: OTok[];
  asm: boolean;
}

function parseMods(m: Meth & { m: 'name' }, termMode = false): Mods {
  const r = argReader(m);
  const mods: Mods = { simpAdd: [], simpDel: [], simpOnly: null, split: [], intro: [], dest: [], elim: [], plain: [], arbitrary: [], rule: [], terms: [], asm: false };
  if (r.isSym('(') && r.isIdent('asm', 1) && r.isSym(')', 2)) {
    r.next();
    r.next();
    r.next();
    mods.asm = true;
  }
  // leading terms / facts
  if (termMode) {
    while (!r.atEnd() && !(r.isIdent() && r.isSym(':', 1))) {
      const t = r.next();
      if (t.kind === 'sym' && t.v === '(') continue;
      if (t.kind === 'ident' && t.v === 'and') continue;
      mods.terms.push(t);
    }
  } else mods.plain = parseFactRefs(r);
  while (!r.atEnd()) {
    const k = r.next();
    if (k.kind !== 'ident') r.fail('modifier expected');
    let key = k.v;
    if (r.isIdent('add') || r.isIdent('del') || r.isIdent('only')) key += ' ' + r.next().v;
    if (r.isSym('!')) {
      r.next();
    }
    r.expectSym(':');
    if (key === 'arbitrary') {
      while (r.isIdent() && !r.isSym(':', 1)) mods.arbitrary.push(r.next());
      continue;
    }
    const refs = parseFactRefs(r);
    switch (key) {
      case 'add':
      case 'simp':
      case 'simp add':
        mods.simpAdd.push(...refs);
        break;
      case 'del':
      case 'simp del':
        mods.simpDel.push(...refs);
        break;
      case 'only':
      case 'simp only':
        mods.simpOnly = [...(mods.simpOnly ?? []), ...refs];
        break;
      case 'split':
        mods.split.push(...refs);
        break;
      case 'intro':
        mods.intro.push(...refs);
        break;
      case 'dest':
        mods.dest.push(...refs);
        break;
      case 'elim':
        mods.elim.push(...refs);
        break;
      case 'iff':
        mods.simpAdd.push(...refs);
        mods.intro.push(...refs);
        break;
      case 'rule':
        mods.rule.push(...refs);
        break;
      case 'cong':
      case 'cong add':
        break;
      default:
        r.fail(`unknown modifier "${key}"`);
    }
  }
  return mods;
}

function mkSimpset(env: MethodEnv, mods: Mods): Simpset {
  const add = env.resolveFacts(mods.simpAdd);
  const del = mods.simpDel.map((d) => d.name);
  let ss: Simpset;
  if (mods.simpOnly) ss = buildSimpset(env.thy, env.resolveFacts(mods.simpOnly), [], true);
  else ss = buildSimpset(env.thy, add, del);
  for (const s of mods.split) {
    const nm = s.name.replace(/\.split(_asm)?$/, '');
    const dt = env.thy.datatypes.get(nm);
    if (dt) ss.splits.add(dt.caseConst);
  }
  return ss;
}

// ---------------- evaluation ----------------

type GoalTac = (g: Goal, facts: Thm[]) => TacResult | null;

function onFirst(st: ProofState, tac: GoalTac, name: string): ProofState {
  if (st.goals.length === 0) throw new MethodFail(`No subgoals!`);
  const [g, ...rest] = st.goals;
  const r = tac(g, st.facts);
  if (!r) throw new MethodFail(`Failed to apply proof method "${name}"`);
  const restI = r.subst ? rest.map((x) => instGoal(x, r.subst!)) : rest;
  return { goals: [...r.goals, ...restI], facts: [], cases: r.cases };
}

function onAll(st: ProofState, f: (g: Goal) => Goal[] | null, name: string): ProofState {
  if (st.goals.length === 0) throw new MethodFail('No subgoals!');
  let changed = false;
  const out: Goal[] = [];
  for (const g of st.goals) {
    const r = f(insertFacts(g, st.facts));
    if (r === null) out.push(g);
    else {
      changed = true;
      out.push(...r);
    }
  }
  if (!changed) throw new MethodFail(`Failed to apply proof method "${name}"`);
  return { goals: out, facts: [] };
}

const STD_INTRO = ['conjI', 'impI', 'allI', 'iffI', 'notI', 'subsetI', 'set_eqI', 'ballI'];
const STD_ELIM = ['conjE', 'disjE', 'exE', 'FalseE', 'bexE'];

export function evalMethod(env: MethodEnv, m: Meth, st: ProofState): ProofState {
  switch (m.m) {
    case 'seq': {
      let s = st;
      for (const x of m.ms) s = evalMethod(env, x, s);
      return s;
    }
    case 'alt': {
      let last: unknown;
      for (const x of m.ms) {
        try {
          return evalMethod(env, x, st);
        } catch (e) {
          last = e;
        }
      }
      throw last;
    }
    case 'try':
      try {
        return evalMethod(env, m.inner, st);
      } catch (e) {
        if (e instanceof MethodFail || e instanceof SimpLimit || e instanceof EngineError) return { ...st, facts: [] };
        throw e;
      }
    case 'rep': {
      let s = evalMethod(env, m.inner, st);
      for (let i = 0; i < 100; i++) {
        try {
          const s2 = evalMethod(env, m.inner, s);
          if (sameGoals(s2.goals, s.goals)) break;
          s = s2;
        } catch {
          break;
        }
      }
      return s;
    }
    case 'sel': {
      const head = st.goals.slice(0, m.n);
      const tail = st.goals.slice(m.n);
      const r = evalMethod(env, m.inner, { goals: head, facts: st.facts });
      return { goals: [...r.goals, ...tail], facts: [], cases: r.cases };
    }
    case 'all': {
      const n = st.goals.length;
      const r1 = evalMethod(env, m.a, st);
      const newCount = Math.max(0, r1.goals.length - (n - 1));
      const fresh = r1.goals.slice(0, newCount);
      const rest = r1.goals.slice(newCount);
      const out: Goal[] = [];
      for (const g of fresh) {
        const r2 = evalMethod(env, m.b, { goals: [g], facts: [] });
        out.push(...r2.goals);
      }
      return { goals: [...out, ...rest], facts: [], cases: r1.cases };
    }
    case 'name':
      return evalNamed(env, m, st);
  }
}

function evalNamed(env: MethodEnv, m: Meth & { m: 'name' }, st: ProofState): ProofState {
  const thy = env.thy;
  const name = m.name;
  const simpLike = (useAsms = true) => {
    const mods = parseMods(m);
    const ss = mkSimpset(env, mods);
    return { mods, ss, useAsms };
  };
  switch (name) {
    case '-':
      return { goals: st.goals.map((g) => insertFacts(g, st.facts)), facts: [] };
    case 'succeed':
      return st;
    case 'fail':
      throw new MethodFail('Failed to apply proof method "fail"');
    case 'simp':
    case 'simp_all':
    case 'eval':
    case 'code_simp':
    case 'normalization': {
      const { ss } = simpLike();
      const run = (g: Goal): Goal[] | null => {
        const r = simpGoal(thy, ss, g, { maxSteps: env.stepLimit ?? 6000 });
        if (r.kind === 'solved') return [];
        if (r.kind === 'goal') return [r.goal];
        return null;
      };
      if (name === 'simp_all') return onAll(st, run, name);
      if (name !== 'simp') {
        return onFirst(
          st,
          (g, facts) => {
            const r = run(insertFacts(g, facts));
            return r && r.length === 0 ? { goals: [] } : null;
          },
          name,
        );
      }
      return onFirst(
        st,
        (g, facts) => {
          const r = run(insertFacts(g, facts));
          return r ? { goals: r } : null;
        },
        name,
      );
    }
    case 'auto':
    case 'force':
    case 'fastforce':
    case 'bestsimp':
    case 'fastsimp':
    case 'clarsimp': {
      const mods = parseMods(m);
      const ss = mkSimpset(env, mods);
      const facts = factProps(env.resolveFacts([...mods.intro, ...mods.dest, ...mods.elim, ...mods.plain]));
      if (name === 'auto') {
        return onAll(
          st,
          (g) => {
            const r = autoGoal(thy, ss, g, { facts, maxSteps: env.stepLimit ?? 6000 });
            if (sameGoals(r, [g])) return null;
            return r;
          },
          name,
        );
      }
      if (name === 'clarsimp') {
        return onFirst(
          st,
          (g, fs) => {
            const g0 = insertFacts(g, fs);
            let goals = [g0];
            for (let i = 0; i < 10; i++) {
              const next: Goal[] = [];
              for (const h of goals) {
                const r = simpGoal(thy, ss, h, { maxSteps: env.stepLimit ?? 6000 });
                if (r.kind === 'solved') continue;
                const h2 = r.kind === 'goal' ? r.goal : h;
                next.push(...clarify(h2));
              }
              if (sameGoals(next, goals)) break;
              goals = next;
            }
            if (sameGoals(goals, [g0]) && sameGoals(goals, [g])) return null;
            return { goals };
          },
          name,
        );
      }
      return onFirst(
        st,
        (g, fs) => {
          const r = autoGoal(thy, ss, insertFacts(g, fs), { facts, blastDepth: 3, maxSteps: env.stepLimit ?? 6000 });
          return r.length === 0 ? { goals: [] } : null;
        },
        name,
      );
    }
    case 'clarify':
      return onFirst(
        st,
        (g, fs) => {
          const g0 = insertFacts(g, fs);
          const r = clarify(g0);
          return sameGoals(r, [g]) ? null : { goals: r };
        },
        name,
      );
    case 'safe':
      return onAll(
        st,
        (g) => {
          let goals = [g];
          for (let i = 0; i < 50; i++) {
            const next: Goal[] = [];
            let ch = false;
            for (const h of goals) {
              const r = safeStep(h);
              if (r) {
                ch = true;
                next.push(...r);
              } else next.push(h);
            }
            goals = next;
            if (!ch) break;
          }
          return sameGoals(goals, [g]) ? null : goals;
        },
        name,
      );
    case 'blast':
    case 'fast':
    case 'best':
    case 'slow':
    case 'iprover':
    case 'meson':
    case 'metis':
    case 'smt':
    case 'argo': {
      const mods = parseMods(m);
      const facts = factProps(env.resolveFacts([...mods.plain, ...mods.intro, ...mods.dest, ...mods.elim]));
      return onFirst(
        st,
        (g, fs) => {
          const g0 = insertFacts(g, fs);
          const s = blastGoal(g0, facts, 5, 20000);
          if (s) return { goals: [], subst: s };
          if (tryArith(g0)) return { goals: [] };
          if (name === 'metis' || name === 'smt' || name === 'meson') {
            // metis also does equational reasoning: try simp with the facts
            const ss = buildSimpset(thy, env.resolveFacts(mods.plain));
            const r = autoGoal(thy, ss, g0, { facts, maxSteps: env.stepLimit ?? 6000 });
            if (r.length === 0) return { goals: [] };
          }
          return null;
        },
        name,
      );
    }
    case 'arith':
    case 'linarith':
    case 'presburger':
    case 'algebra':
      return onFirst(
        st,
        (g, fs) => {
          const g0 = insertFacts(g, fs);
          const parts = clarify(g0);
          for (const p of parts) {
            if (!linarithGoal(p)) {
              // try after simplification of arithmetic only
              const r = simpGoal(thy, buildSimpset(thy, [], [], true), p, { maxSteps: 2000 });
              if (r.kind === 'solved') continue;
              if (r.kind === 'goal' && linarithGoal(r.goal)) continue;
              return null;
            }
          }
          return { goals: [] };
        },
        name,
      );
    case 'assumption':
      return onFirst(st, (g, fs) => assumptionTac(insertFacts(g, fs)), name);
    case 'this':
    case 'fact': {
      const mods = name === 'fact' ? parseMods(m) : null;
      const ths = mods && mods.plain.length ? env.resolveFacts(mods.plain) : st.facts;
      return onFirst(
        st,
        (g) => {
          for (const th of ths) {
            const r = closeByFact(g, instThm(th));
            if (r) return r;
          }
          return assumptionTac(g);
        },
        name,
      );
    }
    case 'contradiction':
      return onFirst(
        st,
        (g, fs) => {
          const g0 = insertFacts(g, fs);
          for (const p of g0.prems) {
            const n = destApp(p, 'Not', 1);
            if (n && g0.prems.some((q) => termEq(q, n[0]))) return { goals: [] };
            if (isConst(p, 'False')) return { goals: [] };
          }
          return null;
        },
        name,
      );
    case 'standard':
    case 'rule':
    case 'intro':
    case 'erule':
    case 'drule':
    case 'frule':
    case 'elim':
    case 'rule_tac':
    case 'erule_tac':
    case 'drule_tac':
    case 'frule_tac':
      return ruleMethod(env, m, st);
    case 'induct':
    case 'induction':
    case 'induct_tac':
      return inductMethod(env, m, st);
    case 'cases':
    case 'case_tac':
      return casesMethod(env, m, st);
    case 'subst': {
      const mods = parseMods(m);
      const ths = env.resolveFacts(mods.plain);
      return onFirst(
        st,
        (g) => {
          for (const th of ths) {
            const r = substTac(g, instThm(th), mods.asm);
            if (r) return r;
            // try reversed orientation for symmetric use? Isabelle does not.
          }
          return null;
        },
        name,
      );
    }
    case 'unfold':
    case 'unfolding': {
      const mods = parseMods(m);
      const ths = env.resolveFacts(mods.plain);
      const ss = buildSimpset(thy, ths, [], true);
      return onAll(
        st,
        (g) => {
          const r = simpGoal(thy, ss, g, { onlyMode: true, useAsms: false, arith: false, splitIf: false });
          if (r.kind === 'solved') return [];
          if (r.kind === 'goal') return [r.goal];
          return null;
        },
        name,
      );
    }
    case 'insert': {
      const mods = parseMods(m);
      const ths = env.resolveFacts(mods.plain);
      return { goals: st.goals.map((g) => insertFacts(insertFacts(g, st.facts), ths)), facts: [] };
    }
    case 'split': {
      const mods = parseMods(m);
      const ss = buildSimpset(thy, [], [], true);
      for (const s of mods.plain) {
        const nm = s.name.replace(/\.split(_asm)?$/, '');
        const dt = thy.datatypes.get(nm);
        if (dt) ss.splits.add(dt.caseConst);
      }
      return onFirst(
        st,
        (g) => {
          const r = simpGoal(thy, ss, g, { onlyMode: false, useAsms: false });
          if (r.kind === 'solved') return { goals: [] };
          if (r.kind === 'goal') return { goals: [r.goal] };
          return null;
        },
        name,
      );
    }
    case 'sorry':
      return { goals: [], facts: [] };
    case 'pat_completeness':
    case 'lexicographic_order':
    case 'size_change':
    case 'relation':
      return { goals: [], facts: [] };
  }
  throw new MethodFail(`Undefined method: "${name}"`);
}

function linarithGoal(g: Goal): boolean {
  try {
    return linarith(g.prems, g.concl);
  } catch {
    return false;
  }
}

// ---------- rule methods ----------
function ruleMethod(env: MethodEnv, m: Meth & { m: 'name' }, st: ProofState): ProofState {
  const thy = env.thy;
  const name = m.name;
  const r = argReader(m);
  // *_tac instantiations: x = "t" and y = "u" in thm
  const insts: { v: string; src: string }[] = [];
  if (name.endsWith('_tac')) {
    while (!r.atEnd() && !r.isIdent('in')) {
      const v = r.next();
      if (v.kind === 'ident' && v.v === 'and') continue;
      if (v.kind !== 'ident' && v.kind !== 'var') r.fail('variable expected');
      r.expectSym('=');
      const t = r.termArg();
      insts.push({ v: v.v, src: t.v });
    }
    if (r.isIdent('in')) r.next();
  }
  const refs = parseFactRefs(r);
  let ths = env.resolveFacts(refs);
  const kind = name.replace(/_tac$/, '');
  if (ths.length === 0 && (kind === 'rule' || kind === 'standard' || kind === 'intro' || kind === 'elim')) {
    const useElim = st.facts.length > 0 && (kind === 'rule' || kind === 'standard');
    const names = kind === 'elim' ? STD_ELIM : useElim ? [...STD_ELIM, ...STD_INTRO] : STD_INTRO;
    ths = [...names.flatMap((n) => thy.thms.get(n) ?? []), ...thy.introRules];
    if (kind === 'elim' || useElim) {
      // try elimination with chained facts first
      if (useElim) {
        for (const th of thy.thms.get('conjE') ? STD_ELIM.flatMap((n) => thy.thms.get(n) ?? []) : []) {
          const res = tryElimWithFacts(st, instThm(th));
          if (res) return res;
        }
      }
    }
  }
  const prepare = (th: Thm, g: Goal): Term => {
    let p = instThm(th);
    if (insts.length) p = instantiateNamed(env, p, insts, g);
    return p;
  };
  if (kind === 'intro' || kind === 'elim') {
    // repeatedly apply to all resulting goals
    if (st.goals.length === 0) throw new MethodFail('No subgoals!');
    const [g0, ...rest] = st.goals;
    let changed = false;
    const work = (g: Goal, depth: number): Goal[] => {
      if (depth > 30) return [g];
      for (const th of ths) {
        const res = kind === 'intro' ? resolveRule(g, prepare(th, g)) : eresolveRule(g, prepare(th, g));
        if (res) {
          changed = true;
          return res.goals.flatMap((x) => work(x, depth + 1));
        }
      }
      return [g];
    };
    const out = work(insertFacts(g0, kind === 'elim' ? st.facts : []), 0);
    if (!changed) throw new MethodFail(`Failed to apply proof method "${name}"`);
    return { goals: [...out, ...rest], facts: [] };
  }
  return onFirst(
    st,
    (g, facts) => {
      for (const th of ths) {
        const p = prepare(th, g);
        let res: TacResult | null = null;
        switch (kind) {
          case 'rule':
          case 'standard':
            res = resolveRule(g, p, factProps(facts));
            if (!res && facts.length) {
              // facts may also be used as elimination major premises
              res = tryElimFacts(g, p, facts);
            }
            break;
          case 'erule':
            res = eresolveRule(insertFacts(g, facts), p);
            break;
          case 'drule':
            res = dresolveRule(insertFacts(g, facts), p, false);
            break;
          case 'frule':
            res = dresolveRule(insertFacts(g, facts), p, true);
            break;
        }
        if (res) return res;
      }
      return null;
    },
    name,
  );
}

function tryElimFacts(g: Goal, p: Term, facts: Thm[]): TacResult | null {
  return eresolveRule(insertFacts(g, facts), p);
}

function tryElimWithFacts(st: ProofState, rule: Term): ProofState | null {
  if (st.goals.length === 0) return null;
  const [g, ...rest] = st.goals;
  const r = decomposeRule(rule);
  if (r.prems.length === 0) return null;
  for (const f of st.facts) {
    const fp = instThm(f);
    const s0 = unify(r.prems[0], fp);
    if (!s0) continue;
    const s = unify(r.concl, g.concl, s0);
    if (!s) continue;
    const goals = r.prems.slice(1).map((pp) => {
      const sub = termToGoal(inst(pp, s), goalFrees(g));
      return { params: [...g.params, ...sub.params], prems: [...g.prems, ...sub.prems], concl: sub.concl };
    });
    return { goals: [...goals, ...rest.map((x) => instGoal(x, s))], facts: [] };
  }
  return null;
}

/** rule_tac x="t" in thm: instantiate schematic variables by base name. */
function instantiateNamed(env: MethodEnv, p: Term, insts: { v: string; src: string }[], g: Goal): Term {
  const vs = new Map<string, Term>();
  const collect = (t: Term) => {
    if (t.k === 'V') vs.set(t.name, t);
    if (t.k === 'A') {
      collect(t.f);
      collect(t.a);
    }
    if (t.k === 'L') collect(t.body);
  };
  collect(p);
  let s: Subst = emptySubst();
  for (const { v, src } of insts) {
    const target = [...vs.values()].find((x) => (x as { name: string }).name.replace(/(__\d+|_q\d+_\w+)$/, '') === v);
    if (!target) throw new MethodFail(`No such variable in theorem: "?${v}"`);
    const t = env.readTerm(src, g);
    const s2 = unify(target, t, s);
    if (!s2) throw new MethodFail(`Type unification failed instantiating ?${v}`);
    s = s2;
  }
  return inst(p, s);
}

// ---------- induction / cases ----------
function inductMethod(env: MethodEnv, m: Meth & { m: 'name' }, st: ProofState): ProofState {
  const mods = parseMods(m, true);
  const vars = mods.terms.filter((t) => t.kind === 'ident' || t.kind === 'string' || t.kind === 'cartouche').map((t) => t.v);
  const arbitrary = mods.arbitrary.map((t) => t.v);
  return onFirst(
    st,
    (g0, facts) => {
      const g = insertFacts(g0, facts);
      // rule induction for inductive predicates
      let ruleName = mods.rule[0]?.name;
      if (ruleName) {
        const base = ruleName.replace(/\.induct$/, '');
        const fi = env.getFun(base);
        if (fi) return funInductTac(env.thy, g, fi, vars, arbitrary);
        const ind = env.getInductive(base);
        if (ind) return ruleInduct(env, g, ind, arbitrary);
        // datatype induct rule given explicitly
        const dt = env.thy.datatypes.get(base);
        if (dt && vars.length === 1) return inductTac(env.thy, g, vars[0], arbitrary);
        throw new MethodFail(`Unknown induction rule: ${ruleName}`);
      }
      if (vars.length === 0) {
        // rule induction on first inductive premise
        for (const p of g.prems) {
          const h = stripApp(p).head;
          if (h.k === 'C') {
            const ind = env.getInductive(h.name);
            if (ind) return ruleInduct(env, g, ind, arbitrary);
          }
        }
        throw new MethodFail('Unable to figure out induct rule');
      }
      if (vars.length > 1) throw new MethodFail('Simultaneous induction on several variables needs an explicit rule');
      return inductTac(env.thy, g, vars[0], arbitrary, m.name === 'induction' ? 'induction' : 'induct');
    },
    m.name,
  );
}

function ruleInduct(env: MethodEnv, g: Goal, ind: InductiveInfo, arbitrary: string[]): TacResult {
  // find the premise `p t1 .. tn`
  const idx = g.prems.findIndex((p) => {
    const s = stripApp(p);
    return s.head.k === 'C' && s.head.name === ind.name && s.args.length === ind.arity;
  });
  if (idx < 0) throw new MethodFail(`No premise of the form ${ind.name} ... for rule induction`);
  const major = stripApp(g.prems[idx]).args;
  if (!major.every((a) => a.k === 'F') || new Set(major.map((a) => (a as { name: string }).name)).size !== major.length)
    throw new MethodFail('Rule induction requires distinct variables as arguments of the inductive premise');
  const xs = major as (Term & { k: 'F' })[];
  const otherPrems = g.prems.filter((_, i) => i !== idx);
  const used = goalFrees(g);
  const arbs = arbitrary.map((a) => {
    const p = g.params.find((x) => x.name === a);
    if (p) return p;
    const f = [...frees(goalBodyTerm(g)).values()].find((x) => (x as { name: string }).name === a);
    if (!f) throw new MethodFail(`Variable "${a}" does not occur in the goal`);
    return f as Term & { k: 'F' };
  });
  const outer = g.params.filter((p) => !xs.some((x) => x.name === p.name) && !arbs.some((a) => a.name === p.name));
  let P = g.concl;
  for (let i = otherPrems.length - 1; i >= 0; i--) P = mkMetaImp(otherPrems[i], P);
  const Pof = (args: Term[], arbSub?: Map<string, Term>): Term => {
    const mp = new Map<string, Term>(xs.map((x, i) => [x.name, args[i]]));
    if (arbSub) for (const [k, v] of arbSub) mp.set(k, v);
    return betaNorm(substFreesM(P, mp));
  };
  const goals: Goal[] = [];
  const cases: CaseInfo[] = [];
  ind.intros.forEach((th, i) => {
    const prop = instThm(th);
    const created: (Term & { k: 'F' })[] = [];
    const tg = termToGoal(varsToFreshFrees(prop, used, created), used);
    const concl = stripApp(tg.concl);
    const prems: Term[] = [];
    const ihs: Term[] = [];
    for (const h of tg.prems) {
      prems.push(h);
      const hs = stripApp(h);
      if (hs.head.k === 'C' && hs.head.name === ind.name && hs.args.length === ind.arity) {
        let ih = Pof(hs.args);
        for (let k = arbs.length - 1; k >= 0; k--) ih = { k: 'A', f: { k: 'C', name: '!!', ty: { k: 'T', name: 'fun', args: [{ k: 'T', name: 'fun', args: [arbs[k].ty, boolT] }, boolT] } }, a: { k: 'L', x: arbs[k].name, ty: arbs[k].ty, body: abstractOverName(ih, arbs[k]) } };
        ihs.push(ih);
        prems.push(ih);
      }
    }
    const fixes = [...created, ...tg.params];
    const conclP = Pof(concl.args);
    const cg = termToGoal(conclP, new Set([...used, ...fixes.map((f) => f.name)]));
    goals.push({ params: [...outer, ...fixes, ...cg.params], prems: [...prems, ...cg.prems], concl: cg.concl });
    cases.push({ name: th.name.includes('(') ? String(i + 1) : th.name.split('.').pop()!, fixes, assumes: [...prems, ...cg.prems], ih: ihs, prems: cg.prems, concl: cg.concl });
  });
  return { goals, cases };
}

function goalBodyTerm(g: Goal): Term {
  let t = g.concl;
  for (let i = g.prems.length - 1; i >= 0; i--) t = mkMetaImp(g.prems[i], t);
  return t;
}

function abstractOverName(t: Term, v: Term & { k: 'F' }): Term {
  const go = (u: Term, lev: number): Term => {
    if (u.k === 'F' && u.name === v.name) return { k: 'B', i: lev };
    if (u.k === 'A') return { k: 'A', f: go(u.f, lev), a: go(u.a, lev) };
    if (u.k === 'L') return { k: 'L', x: u.x, ty: u.ty, body: go(u.body, lev + 1) };
    return u;
  };
  return go(t, 0);
}

function substFreesM(t: Term, m: Map<string, Term>): Term {
  switch (t.k) {
    case 'F':
      return m.get(t.name) ?? t;
    case 'A':
      return { k: 'A', f: substFreesM(t.f, m), a: substFreesM(t.a, m) };
    case 'L':
      return { k: 'L', x: t.x, ty: t.ty, body: substFreesM(t.body, m) };
    default:
      return t;
  }
}

function varsToFreshFrees(t: Term, used: Set<string>, created: (Term & { k: 'F' })[] = []): Term {
  const m = new Map<string, Term>();
  const go = (u: Term): Term => {
    switch (u.k) {
      case 'V': {
        let r = m.get(u.name);
        if (!r) {
          let base = u.name.replace(/(__\d+|_q\d+_\w+)$/, '');
          if (!base) base = 'x';
          let nm = base;
          let i = 0;
          while (used.has(nm)) nm = base + String.fromCharCode(97 + i++);
          used.add(nm);
          r = { k: 'F', name: nm, ty: u.ty };
          created.push(r as Term & { k: 'F' });
          m.set(u.name, r);
        }
        return r;
      }
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

function casesMethod(env: MethodEnv, m: Meth & { m: 'name' }, st: ProofState): ProofState {
  const mods = parseMods(m, true);
  const terms = mods.terms.filter((t) => t.kind !== 'sym');
  return onFirst(
    st,
    (g0, facts) => {
      const g = insertFacts(g0, facts);
      if (terms.length === 0) {
        // rule inversion on an inductive premise
        for (let i = 0; i < g.prems.length; i++) {
          const h = stripApp(g.prems[i]);
          if (h.head.k === 'C') {
            const ind = env.getInductive(h.head.name);
            if (ind) return invertInductive(env, g, i, ind);
          }
        }
        throw new MethodFail('cases: no term given');
      }
      const t = env.readTerm(terms[0].v, g);
      return casesTac(env.thy, g, t);
    },
    m.name,
  );
}

/** Rule inversion: case split on which introduction rule could have produced premise i. */
export function invertInductive(env: MethodEnv, g: Goal, i: number, ind: InductiveInfo): TacResult {
  const major = stripApp(g.prems[i]).args;
  const rest = g.prems.filter((_, j) => j !== i);
  const goals: Goal[] = [];
  const cases: CaseInfo[] = [];
  const used = goalFrees(g);
  const ss = buildSimpset(env.thy, [], [], true);
  ind.intros.forEach((th, k) => {
    const created: (Term & { k: 'F' })[] = [];
    const prop = varsToFreshFrees(instThm(th), used, created);
    const tg = termToGoal(prop, used);
    const cargs = stripApp(tg.concl).args;
    let fixes = [...created, ...tg.params];
    // simplify constructor equations; drop impossible cases
    let eqs: Term[] = [];
    let impossible = false;
    for (let j = 0; j < major.length; j++) {
      const e = mkEq(major[j], cargs[j]);
      const r = simpGoal(env.thy, ss, { params: [], prems: [], concl: e }, { useAsms: false, arith: true });
      if (r.kind === 'solved') continue;
      const c = r.kind === 'goal' ? r.goal.concl : e;
      if (isConst(c, 'False')) {
        impossible = true;
        break;
      }
      eqs.push(...splitConj(c));
    }
    if (impossible) return;
    let prems = [...tg.prems];
    let concl = g.concl;
    let restP = rest;
    // substitute equations "fix = t" / "t = fix"
    for (let changed = true; changed; ) {
      changed = false;
      for (let j = 0; j < eqs.length; j++) {
        const e = destApp(eqs[j], 'eq', 2);
        if (!e) continue;
        for (const [a, b] of [
          [e[0], e[1]],
          [e[1], e[0]],
        ]) {
          if (a.k === 'F' && fixes.some((f) => f.name === a.name) && !frees(b).has(a.name)) {
            const m = new Map([[a.name, b]]);
            const sb = (t: Term) => betaNorm(substFreesM(t, m));
            eqs = eqs.filter((_, q) => q !== j).map(sb);
            prems = prems.map(sb);
            fixes = fixes.filter((f) => f.name !== a.name);
            changed = true;
            break;
          }
        }
        if (changed) break;
      }
    }
    void restP;
    goals.push({ params: [...g.params, ...fixes], prems: [...rest, ...eqs, ...prems], concl });
    cases.push({ name: th.name.split('.').pop()?.replace(/\(\d+\)$/, '') ?? String(k + 1), fixes, assumes: [...eqs, ...prems], ih: [], prems, concl });
  });
  return { goals, cases };
}

function splitConj(t: Term): Term[] {
  const c = destApp(t, 'conj', 2);
  return c ? [...splitConj(c[0]), ...splitConj(c[1])] : [t];
}

export { mkNot, typeOf, tsubst, tunify, mapTypes, OuterError };
export type { Type };
