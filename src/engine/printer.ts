// Pretty printing of types and terms in Isabelle style (Unicode symbols).
import { Term, Type, stripApp, numVal, variant, frees, substBound, mkF, termEq } from './terms';
import type { Theory } from './theory';

let printThy: Theory | null = null;
export function setPrintTheory(t: Theory | null) {
  printThy = t;
}

export function printType(t: Type, prec = 0): string {
  switch (t.k) {
    case 'V':
      return t.name;
    case 'S':
      return '?\'t' + t.id;
    case 'T': {
      if (t.name === 'fun') {
        const s = `${printType(t.args[0], 1)} ⇒ ${printType(t.args[1], 0)}`;
        return prec > 0 ? `(${s})` : s;
      }
      if (t.name === 'prod') {
        const s = `${printType(t.args[0], 21)} × ${printType(t.args[1], 20)}`;
        return prec > 20 ? `(${s})` : s;
      }
      if (t.args.length === 0) return t.name;
      if (t.args.length === 1) return `${printType(t.args[0], 100)} ${t.name}`;
      return `(${t.args.map((a) => printType(a, 0)).join(', ')}) ${t.name}`;
    }
  }
}

interface OpInfo {
  sym: string;
  prec: number;
  assoc: 'l' | 'r' | 'n';
}
const BINOPS: Record<string, OpInfo> = {
  '==>': { sym: '⟹', prec: 1, assoc: 'r' },
  imp: { sym: '⟶', prec: 25, assoc: 'r' },
  disj: { sym: '∨', prec: 30, assoc: 'r' },
  conj: { sym: '∧', prec: 35, assoc: 'r' },
  eq: { sym: '=', prec: 50, assoc: 'l' },
  less: { sym: '<', prec: 50, assoc: 'n' },
  less_eq: { sym: '≤', prec: 50, assoc: 'n' },
  member: { sym: '∈', prec: 50, assoc: 'n' },
  subset_eq: { sym: '⊆', prec: 50, assoc: 'n' },
  subset: { sym: '⊂', prec: 50, assoc: 'n' },
  dvd: { sym: 'dvd', prec: 50, assoc: 'n' },
  comp: { sym: '∘', prec: 55, assoc: 'l' },
  Cons: { sym: '#', prec: 65, assoc: 'r' },
  append: { sym: '@', prec: 65, assoc: 'r' },
  plus: { sym: '+', prec: 65, assoc: 'l' },
  minus: { sym: '-', prec: 65, assoc: 'l' },
  union: { sym: '∪', prec: 65, assoc: 'l' },
  inter: { sym: '∩', prec: 70, assoc: 'l' },
  times: { sym: '*', prec: 70, assoc: 'l' },
  divide: { sym: '/', prec: 70, assoc: 'l' },
  div: { sym: 'div', prec: 70, assoc: 'l' },
  mod: { sym: 'mod', prec: 70, assoc: 'l' },
  power: { sym: '^', prec: 80, assoc: 'r' },
  nth: { sym: '!', prec: 100, assoc: 'l' },
  image: { sym: '`', prec: 90, assoc: 'r' },
};

const BINDERS: Record<string, string> = { All: '∀', Ex: '∃', Ex1: '∃!', '!!': '⋀', Eps: 'SOME ', The: 'THE ' };

/** Display name of constants (strip internal prefixes). */
function constName(name: string): string {
  if (name.startsWith('#')) return name.slice(1);
  switch (name) {
    case 'Nil':
      return '[]';
    case 'bot_set':
      return '{}';
    case 'Unity':
      return '()';
    case 'Not':
      return '¬';
  }
  return name;
}

export function printTerm(t: Term): string {
  const used = new Set<string>();
  for (const k of frees(t).keys()) used.add(k);
  return pr(t, 0, [], used);
}

function paren(s: string, cond: boolean) {
  return cond ? `(${s})` : s;
}

function boundName(env: string[], i: number) {
  return env[env.length - 1 - i] ?? `B${i}`;
}

// open a lambda: pick fresh name
function openAbs(t: Term & { k: 'L' }, used: Set<string>): { name: string; body: Term; used: Set<string> } {
  const base = t.x === '_' || t.x.startsWith('__') ? 'x' : t.x;
  const nm = variant(base, used);
  const u2 = new Set(used);
  u2.add(nm);
  return { name: nm, body: substBound(t.body, mkF(nm, t.ty)), used: u2 };
}

function pr(t: Term, prec: number, env: string[], used: Set<string>): string {
  switch (t.k) {
    case 'F':
      return t.name;
    case 'V':
      return '?' + t.name.replace(/__\d+$/, '');
    case 'B':
      return boundName(env, t.i);
    case 'C':
      return constName(t.name);
    case 'L': {
      const vs: string[] = [];
      let cur: Term = t;
      let u = used;
      while (cur.k === 'L') {
        const o = openAbs(cur, u);
        vs.push(o.name);
        cur = o.body;
        u = o.used;
      }
      return paren(`λ${vs.join(' ')}. ${pr(cur, 3, env, u)}`, prec > 3);
    }
    case 'A':
      return prApp(t, prec, env, used);
  }
}

function prApp(t: Term, prec: number, env: string[], used: Set<string>): string {
  const { head, args } = stripApp(t);
  if (head.k === 'C') {
    const n = head.name;
    if (n === '__paren' && args.length === 1) return `(${pr(args[0], 0, env, used)})`;
    // binders
    if (BINDERS[n] && args.length === 1 && args[0].k === 'L') {
      const sym = BINDERS[n];
      const vs: string[] = [];
      let cur: Term = args[0];
      let u = used;
      for (;;) {
        if (cur.k !== 'L') break;
        const o = openAbs(cur, u);
        vs.push(o.name);
        cur = o.body;
        u = o.used;
        const nx = stripApp(cur);
        if (!(nx.head.k === 'C' && nx.head.name === n && nx.args.length === 1 && nx.args[0].k === 'L')) break;
        cur = nx.args[0];
      }
      const bp = n === '!!' ? 0 : 10;
      return paren(`${sym}${vs.join(' ')}. ${pr(cur, bp, env, u)}`, prec > bp);
    }
    if (n === 'Not' && args.length === 1) {
      const inner = stripApp(args[0]);
      if (inner.head.k === 'C' && inner.args.length === 2 && inner.head.name === 'eq')
        return paren(`${pr(inner.args[0], 51, env, used)} ≠ ${pr(inner.args[1], 51, env, used)}`, prec > 50);
      if (inner.head.k === 'C' && inner.args.length === 2 && inner.head.name === 'member')
        return paren(`${pr(inner.args[0], 51, env, used)} ∉ ${pr(inner.args[1], 51, env, used)}`, prec > 50);
      return paren(`¬ ${pr(args[0], 40, env, used)}`, prec > 40);
    }
    if (n === 'uminus' && args.length === 1) return paren(`- ${pr(args[0], 81, env, used)}`, prec > 80);
    if (n === '==>' && args.length === 2) {
      const prems: Term[] = [];
      let cur: Term = t;
      for (;;) {
        const s = stripApp(cur);
        if (s.head.k === 'C' && s.head.name === '==>' && s.args.length === 2) {
          prems.push(s.args[0]);
          cur = s.args[1];
        } else break;
      }
      const concl = pr(cur, 1, env, used);
      if (prems.length === 1) return paren(`${pr(prems[0], 2, env, used)} ⟹ ${concl}`, prec > 1);
      return paren(`⟦${prems.map((p) => pr(p, 0, env, used)).join('; ')}⟧ ⟹ ${concl}`, prec > 1);
    }
    if (n === 'If' && args.length === 3)
      return paren(`if ${pr(args[0], 0, env, used)} then ${pr(args[1], 0, env, used)} else ${pr(args[2], 10, env, used)}`, prec > 10);
    if (n === 'Let' && args.length === 2 && args[1].k === 'L') {
      const o = openAbs(args[1], used);
      return paren(`let ${o.name} = ${pr(args[0], 0, env, used)} in ${pr(o.body, 10, env, o.used)}`, prec > 10);
    }
    if (n === 'Pair' && args.length === 2) {
      const items = [args[0]];
      let cur = args[1];
      for (;;) {
        const s = stripApp(cur);
        if (s.head.k === 'C' && s.head.name === 'Pair' && s.args.length === 2) {
          items.push(s.args[0]);
          cur = s.args[1];
        } else break;
      }
      items.push(cur);
      return `(${items.map((x) => pr(x, 0, env, used)).join(', ')})`;
    }
    if (n === 'Cons' && args.length === 2) {
      // list literal?
      const items: Term[] = [];
      let cur: Term = t;
      for (;;) {
        const s = stripApp(cur);
        if (s.head.k === 'C' && s.head.name === 'Cons' && s.args.length === 2) {
          items.push(s.args[0]);
          cur = s.args[1];
        } else break;
      }
      if (cur.k === 'C' && cur.name === 'Nil') return `[${items.map((x) => pr(x, 0, env, used)).join(', ')}]`;
    }
    if (n === 'insert' && args.length === 2) {
      const items: Term[] = [];
      let cur: Term = t;
      for (;;) {
        const s = stripApp(cur);
        if (s.head.k === 'C' && s.head.name === 'insert' && s.args.length === 2) {
          items.push(s.args[0]);
          cur = s.args[1];
        } else break;
      }
      if (cur.k === 'C' && cur.name === 'bot_set') return `{${items.map((x) => pr(x, 0, env, used)).join(', ')}}`;
    }
    if (n === 'Collect' && args.length === 1 && args[0].k === 'L') {
      const o = openAbs(args[0], used);
      return `{${o.name}. ${pr(o.body, 0, env, o.used)}}`;
    }
    if (n === 'upt' && args.length === 2) return `[${pr(args[0], 0, env, used)}..<${pr(args[1], 0, env, used)}]`;
    if (n === 'case_prod' && args.length === 1 && args[0].k === 'L' && args[0].body.k === 'L') {
      const o1 = openAbs(args[0], used);
      const o2 = openAbs(o1.body as Term & { k: 'L' }, o1.used);
      return paren(`λ(${o1.name}, ${o2.name}). ${pr(o2.body, 3, env, o2.used)}`, prec > 3);
    }
    if (n.startsWith('case_') && printThy) {
      const dt = [...printThy.datatypes.values()].find((d) => d.caseConst === n);
      if (dt && args.length === dt.ctors.length + 1) {
        const clauses: string[] = [];
        let u = used;
        dt.ctors.forEach((c, i) => {
          let f = args[i];
          const names: string[] = [];
          for (let j = 0; j < c.argTys.length; j++) {
            if (f.k === 'L') {
              const o = openAbs(f, u);
              names.push(o.name);
              f = o.body;
              u = o.used;
            } else {
              const nm = variant('x', u);
              u = new Set(u);
              u.add(nm);
              names.push(nm);
              f = { k: 'A', f, a: mkF(nm, c.argTys[j]) };
            }
          }
          const pat = patternString(c.name, names);
          clauses.push(`${pat} ⇒ ${pr(f, 11, env, u)}`);
        });
        return paren(`case ${pr(args[args.length - 1], 0, env, used)} of ${clauses.join(' | ')}`, prec > 10);
      }
    }
    const op = BINOPS[n];
    if (op && args.length === 2) {
      // bool equality shown as ⟷? Isabelle shows "=", keep it
      const lp = op.assoc === 'l' ? op.prec : op.prec + 1;
      const rp = op.assoc === 'r' ? op.prec : op.prec + 1;
      const s = `${pr(args[0], lp, env, used)} ${op.sym} ${pr(args[1], rp, env, used)}`;
      return paren(s, prec > op.prec);
    }
    if (op && args.length > 2) {
      const s = `(${pr(args[0], op.prec, env, used)} ${op.sym} ${pr(args[1], op.prec + 1, env, used)}) ${args
        .slice(2)
        .map((a) => pr(a, 1001, env, used))
        .join(' ')}`;
      return paren(s, prec > 1000);
    }
    if (op && args.length === 1) {
      return paren(`(${op.sym}) ${pr(args[0], 1001, env, used)}`, prec > 1000);
    }
  }
  const hs = pr(head, 1000, env, used);
  const s = `${hs} ${args.map((a) => pr(a, 1001, env, used)).join(' ')}`;
  return paren(s, prec > 1000);
}

function patternString(ctor: string, names: string[]): string {
  if (ctor === 'Nil') return '[]';
  if (ctor === 'Cons' && names.length === 2) return `${names[0]} # ${names[1]}`;
  if (ctor === 'Pair' && names.length === 2) return `(${names[0]}, ${names[1]})`;
  if (ctor === '#0') return '0';
  return [ctor, ...names].join(' ');
}

export function printNum(t: Term): string | null {
  const v = numVal(t);
  return v === null ? null : String(v);
}

export { termEq };
