// Goals (subgoals of a proof state) and helpers.
import {
  Term,
  Type,
  stripApp,
  destApp,
  substBound,
  mkF,
  mkMetaImp,
  mkMetaAll,
  frees,
  variant,
  boolT,
} from './terms';
import { printTerm } from './printer';

export interface Goal {
  params: (Term & { k: 'F' })[];
  prems: Term[];
  concl: Term;
}

export function goalToTerm(g: Goal): Term {
  let t = g.concl;
  for (let i = g.prems.length - 1; i >= 0; i--) t = mkMetaImp(g.prems[i], t);
  for (let i = g.params.length - 1; i >= 0; i--) t = mkMetaAll(g.params[i], t);
  return t;
}

export function usedNames(ts: Term[]): Set<string> {
  const s = new Set<string>();
  for (const t of ts) for (const k of frees(t).keys()) s.add(k);
  return s;
}

/** Strip outer ⋀ and ⟹ into a goal; bound variables become fresh frees avoiding `used`. */
export function termToGoal(t: Term, used: Set<string> = new Set(), base?: Goal): Goal {
  const params: (Term & { k: 'F' })[] = base ? [...base.params] : [];
  const prems: Term[] = base ? [...base.prems] : [];
  const u = new Set(used);
  for (const k of frees(t).keys()) u.add(k);
  for (const p of params) u.add(p.name);
  for (;;) {
    const s = stripApp(t);
    if (s.head.k === 'C' && s.head.name === '!!' && s.args.length === 1 && s.args[0].k === 'L') {
      const lam = s.args[0];
      const nm = variant(lam.x === '_' || lam.x.startsWith('__') ? 'x' : lam.x, u);
      u.add(nm);
      const f = mkF(nm, lam.ty) as Term & { k: 'F' };
      params.push(f);
      t = substBound(lam.body, f);
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
  return { params, prems, concl: t };
}

export function goalFrees(g: Goal): Set<string> {
  const s = usedNames([...g.prems, g.concl]);
  for (const p of g.params) s.add(p.name);
  return s;
}

export function printGoal(g: Goal, i: number): string {
  const body = printGoalBody(g);
  return ` ${i}. ${body.replace(/\n/g, '\n    ')}`;
}

export function printGoalBody(g: Goal): string {
  let s = '';
  if (g.params.length) s += `⋀${g.params.map((p) => p.name).join(' ')}. `;
  const c = printTerm(g.concl);
  if (g.prems.length === 0) s += c;
  else if (g.prems.length === 1) s += `${printTerm(mkMetaImpWrap(g.prems[0]))} ⟹ ${c}`;
  else s += `⟦${g.prems.map((p) => printTerm(p)).join('; ')}⟧ ⟹ ${c}`;
  return s;
}

function mkMetaImpWrap(t: Term): Term {
  // a premise that is itself a meta implication needs parentheses: printTerm handles precedence via wrapper
  const imp = destApp(t, '==>', 2);
  if (imp || (stripApp(t).head.k === 'C' && (stripApp(t).head as { name: string }).name === '!!')) {
    return { k: 'A', f: { k: 'C', name: '__paren', ty: boolT }, a: t };
  }
  return t;
}

export function printGoals(goals: Goal[]): string {
  if (goals.length === 0) return 'No subgoals!';
  const hdr = `goal (${goals.length} subgoal${goals.length === 1 ? '' : 's'}):`;
  return [hdr, ...goals.map((g, i) => printGoal(g, i + 1))].join('\n');
}

export function freshFree(base: string, ty: Type, used: Set<string>): Term & { k: 'F' } {
  const nm = variant(base, used);
  used.add(nm);
  return mkF(nm, ty) as Term & { k: 'F' };
}
