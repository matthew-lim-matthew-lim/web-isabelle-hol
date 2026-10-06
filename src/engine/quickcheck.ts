// A small exhaustive counterexample finder (in the spirit of quickcheck/nitpick).
import { Term, Type, mkC, mkApps, funTs, frees, substFrees, mapTypes, tmapV, natT, intT, boolT, isConst, mkImp, betaNorm } from './terms';
import { Theory } from './theory';
import { Goal } from './goal';
import { buildSimpset, Simplifier } from './simp';
import { printTerm } from './printer';

function values(thy: Theory, ty: Type, depth: number): Term[] {
  if (ty.k !== 'T') return [];
  switch (ty.name) {
    case 'nat':
      return [0, 1, 2, 3, 4].slice(0, depth + 2).map((n) => mkC('#' + n, natT));
    case 'int':
      return [0, 1, -1, 2, -2].slice(0, depth + 2).map((n) => (n < 0 ? mkApps(mkC('uminus', funTs([intT], intT)), [mkC('#' + -n, intT)]) : mkC('#' + n, intT)));
    case 'bool':
      return [mkC('True', boolT), mkC('False', boolT)];
    case 'fun':
      return [];
  }
  const dt = thy.datatypeOf(ty);
  if (!dt) return [];
  const out: Term[] = [];
  for (const c of dt.ctors) {
    const argTys = thy.ctorArgTys(dt, c, ty);
    if (argTys.length && depth <= 0) continue;
    let combos: Term[][] = [[]];
    for (const at of argTys) {
      const vs = values(thy, at, depth - 1);
      const next: Term[][] = [];
      for (const cmb of combos) for (const v of vs.slice(0, 3)) next.push([...cmb, v]);
      combos = next;
      if (combos.length > 30) combos = combos.slice(0, 30);
    }
    for (const cmb of combos) out.push(mkApps(mkC(c.name, funTs(argTys, ty)), cmb));
    if (out.length > 40) break;
  }
  return out;
}

export function quickcheck(thy: Theory, g: Goal): { found: boolean; text: string } {
  let prop: Term = g.concl;
  for (let i = g.prems.length - 1; i >= 0; i--) prop = mkImp(g.prems[i], prop);
  // instantiate type variables with nat
  prop = mapTypes(prop, (t) => tmapV(t, () => natT));
  const fv = [...frees(prop).values()] as (Term & { k: 'F' })[];
  if (fv.length === 0) return { found: false, text: 'Quickcheck: no free variables to instantiate' };
  const doms = fv.map((v) => values(thy, v.ty, 3));
  if (doms.some((d) => d.length === 0)) return { found: false, text: 'Quickcheck: cannot enumerate values of some variable types (e.g. functions); no counterexample search performed' };
  const ss = buildSimpset(thy);
  let tested = 0;
  const idx = fv.map(() => 0);
  for (;;) {
    if (tested > 400) break;
    const m = new Map<string, Term>();
    fv.forEach((v, i) => m.set(v.name, doms[i][idx[i]]));
    const inst = betaNorm(substFrees(prop, m));
    tested++;
    try {
      const S = new Simplifier(thy, ss, { maxSteps: 3000 });
      const r = S.norm(inst);
      if (isConst(r, 'False')) {
        const assign = fv.map((v, i) => `  ${v.name} = ${printTerm(doms[i][idx[i]])}`).join('\n');
        return { found: true, text: `Quickcheck found a counterexample:\n${assign}` };
      }
    } catch {
      /* skip */
    }
    let k = 0;
    while (k < idx.length) {
      idx[k]++;
      if (idx[k] < doms[k].length) break;
      idx[k] = 0;
      k++;
    }
    if (k === idx.length) break;
  }
  return { found: false, text: `Quickcheck found no counterexample (tested ${tested} cases).` };
}
