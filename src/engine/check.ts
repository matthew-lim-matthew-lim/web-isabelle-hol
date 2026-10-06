// Theory checker: executes outer syntax commands (theory level + Isar proofs) and records per-command results.
import { tokenizeOuter, splitCommands, Command, OTok, TokReader, OuterError } from './outer';
import {
  Term,
  Type,
  EngineError,
  boolT,
  funT,
  funTs,
  tvar,
  tcon,
  mkC,
  mkF,
  mkV,
  mkApps,
  mkEq,
  mkMetaImp,
  mkConj,
  conjs,
  stripApp,
  destApp,
  frees,
  termEq,
  typeOf,
  mapTypes,
  tsubst,
  tunify,
  freshTS,
  isConst,
  betaNorm,
  substFrees,
  stripFunT,
  tvarsOf,
  natT,
  mkEx,
  mkNot,
  termKey,
} from './terms';
import { Theory, Thm, generalize, instThm, varsToFrees } from './theory';
import { TermCtx, readTerms, readType, Elab } from './typecheck';
import { parseTerm, parseType } from './syntax';
import { printTerm, printType, setPrintTheory } from './printer';
import { Goal, termToGoal, printGoals, goalToTerm, goalFrees } from './goal';
import {
  Meth,
  parseMethodTop,
  evalMethod,
  MethodEnv,
  ProofState,
  FactRef,
  parseFactRefs,
  parseAttrsOpt,
  MethodFail,
  InductiveInfo,
} from './methods';
import { CaseInfo, instGoal, assumptionTac, closeByFact, decomposeRule } from './tactics';
import { unify, inst, emptySubst, Subst, collectVarNames } from './unify';
import { declareDatatype, completeEquations, registerFun, checkTermination, checkLinearPatterns, RawEq } from './defs';
import { buildSimpset, simpTerm, SimpLimit } from './simp';
import { quickcheck } from './quickcheck';

export type Severity = 'error' | 'warning' | 'info';
export interface Message {
  severity: Severity;
  text: string;
}
export interface CmdResult {
  from: number;
  to: number;
  kw: string;
  messages: Message[];
  state?: string;
  status: 'ok' | 'error' | 'warning';
}
export interface TheoremInfo {
  name: string;
  statement: string;
  sorry: boolean;
  error: boolean;
  from: number;
  to: number;
}
export interface CheckResult {
  commands: CmdResult[];
  theorems: TheoremInfo[];
  errors: number;
  sorries: number;
  ok: boolean;
  theoryName?: string;
  ended: boolean;
}

interface PCtx {
  fixed: Map<string, Type>;
  facts: Map<string, Thm[]>;
  abbrevs: Map<string, Term>;
  dots?: Term;
}
const cloneCtx = (c: PCtx): PCtx => ({ fixed: new Map(c.fixed), facts: new Map(c.facts), abbrevs: new Map(c.abbrevs), dots: c.dots });

interface Attr {
  name: string;
  args: OTok[];
}

type BlockKind = 'lemma' | 'have' | 'show' | 'obtain' | 'subgoal' | 'dummy' | 'brace';

interface Block {
  kind: BlockKind;
  name?: string;
  attrs: Attr[];
  stmts: Term[];
  assms: Term[];
  goals: Goal[];
  mode: 'prove' | 'state' | 'chain';
  ctx: PCtx;
  baseCtx: PCtx | null;
  localFixes: (Term & { k: 'F' })[];
  localAssms: Term[];
  cases: CaseInfo[];
  using: Thm[];
  chained: Thm[];
  thisFacts: Thm[];
  calc: Thm[] | null;
  calcMode?: 'also' | 'moreover';
  error: boolean;
  sorry: boolean;
  from: number;
  obtain?: { vars: (Term & { k: 'F' })[]; props: Term[]; names: (string | undefined)[] };
  subgoalIdx?: number;
  usedFixes?: Map<string, Type>;
  stmtFrees?: Map<string, Type>;
}

class CmdError extends Error {}

let PRELUDE_THY: Theory | null = null;
export function setPrelude(thy: Theory) {
  PRELUDE_THY = thy;
}
export function getPrelude(): Theory | null {
  return PRELUDE_THY;
}

export interface CheckOptions {
  base?: Theory;
  isPrelude?: boolean;
  stepLimit?: number;
}

export class Checker {
  thy: Theory;
  stack: Block[] = [];
  results: CmdResult[] = [];
  theorems: TheoremInfo[] = [];
  inductives = new Map<string, InductiveInfo>();
  cur!: CmdResult;
  ended = false;
  theoryName?: string;
  started = false;
  constructor(public opts: CheckOptions) {
    this.thy = opts.base ? opts.base.clone() : new Theory();
    const ind = (opts.base as unknown as { __inductives?: Map<string, InductiveInfo> })?.__inductives;
    if (ind) this.inductives = new Map(ind);
  }

  msg(severity: Severity, text: string) {
    this.cur.messages.push({ severity, text });
    if (severity === 'error') this.cur.status = 'error';
    else if (severity === 'warning' && this.cur.status === 'ok') this.cur.status = 'warning';
  }

  get top(): Block | undefined {
    return this.stack[this.stack.length - 1];
  }

  run(src: string): CheckResult {
    setPrintTheory(this.thy);
    const { toks, errors } = tokenizeOuter(src);
    const cmds = splitCommands(toks);
    for (const e of errors) {
      this.results.push({ from: e.from, to: e.to, kw: 'error', messages: [{ severity: 'error', text: e.message }], status: 'error' });
    }
    for (const c of cmds) {
      this.cur = { from: c.from, to: c.to, kw: c.kw, messages: [], status: 'ok' };
      this.results.push(this.cur);
      try {
        this.exec(c);
      } catch (e) {
        if (e instanceof OuterError || e instanceof EngineError || e instanceof CmdError || e instanceof MethodFail) this.msg('error', e.message);
        else if (e instanceof RangeError) this.msg('error', 'Internal error: recursion too deep (term too large?)');
        else this.msg('error', 'Internal error: ' + (e instanceof Error ? e.message : String(e)));
        const b = this.top;
        if (b) this.markError();
      }
      this.cur.state = this.stateString();
    }
    if (this.stack.length && this.results.length) {
      const last = this.results[this.results.length - 1];
      last.messages.push({ severity: 'error', text: 'Unfinished proof at end of text' });
      last.status = 'error';
    }
    const errorsN = this.results.filter((r) => r.status === 'error').length;
    const sorries = this.results.filter((r) => r.kw === 'sorry' || r.kw === 'oops').length;
    return {
      commands: this.results,
      theorems: this.theorems,
      errors: errorsN,
      sorries,
      ok: errorsN === 0,
      theoryName: this.theoryName,
      ended: this.ended,
    };
  }

  markError() {
    for (const b of this.stack) b.error = true;
  }

  // ---------------- dispatch ----------------
  exec(c: Command) {
    const r = new TokReader(c.toks, c);
    const kw = c.kw;
    if (kw === '<junk>') throw new CmdError('Outer syntax error: command expected');
    if (this.ended) throw new CmdError('Command after end of theory');
    switch (kw) {
      case 'theory':
        return this.cmdTheory(r);
      case 'begin':
        if (this.started) throw new CmdError('Unexpected "begin"');
        this.started = true;
        return;
      case 'end':
        if (this.stack.length) throw new CmdError('Bad context for command "end": unfinished proof');
        this.ended = true;
        return;
      case 'text':
      case 'txt':
      case 'section':
      case 'subsection':
      case 'subsubsection':
      case 'chapter':
      case 'paragraph':
      case 'header':
      case 'text_raw':
        return;
    }
    const theoryCmds = new Set([
      'datatype',
      'fun',
      'primrec',
      'function',
      'termination',
      'definition',
      'abbreviation',
      'type_synonym',
      'axiomatization',
      'consts',
      'declare',
      'lemmas',
      'inductive',
      'lemma',
      'theorem',
      'corollary',
      'proposition',
      'schematic_goal',
      'export_code',
      'hide_const',
      'notation',
      'no_notation',
      'locale',
      'class',
      'instantiation',
      'instance',
      'interpretation',
    ]);
    const diag = new Set(['value', 'term', 'typ', 'thm', 'find_theorems', 'print_theorems', 'prop', 'print_state']);
    if (diag.has(kw)) return this.cmdDiag(kw, r);
    if (theoryCmds.has(kw)) {
      if (this.stack.length && kw !== 'termination') {
        throw new CmdError(`Illegal application of command "${kw}" in proof mode`);
      }
      return this.cmdTheoryLevel(kw, r, c);
    }
    if (!this.stack.length) throw new CmdError(`Illegal application of proof command "${kw}" in theory mode`);
    return this.cmdProof(kw, r, c);
  }

  cmdTheory(r: TokReader) {
    const name = r.expectIdent();
    this.theoryName = name.v;
    this.thy.name = name.v;
    if (r.isIdent('imports')) {
      r.next();
      while (!r.atEnd()) {
        const t = r.next();
        const nm = t.v.replace(/^"|"$/g, '');
        if (!['Main', 'Complex_Main', 'HOL.Main', 'HOL-Library.Main'].includes(nm) && !nm.startsWith('HOL-'))
          this.msg('warning', `Theory "${nm}" is not available in this web edition; only Main is loaded`);
      }
    }
  }

  // ---------------- theory-level commands ----------------
  cmdTheoryLevel(kw: string, r: TokReader, c: Command) {
    switch (kw) {
      case 'datatype':
        return this.cmdDatatype(r);
      case 'fun':
      case 'primrec':
      case 'function':
        return this.cmdFun(kw, r, c);
      case 'termination':
        this.pushDummy(c);
        return;
      case 'definition':
      case 'abbreviation':
        return this.cmdDefinition(kw, r);
      case 'type_synonym':
        return this.cmdTypeSynonym(r);
      case 'axiomatization':
      case 'consts':
        return this.cmdAxiomatization(kw, r);
      case 'declare':
        return this.cmdDeclare(r);
      case 'lemmas':
        return this.cmdLemmas(r);
      case 'inductive':
        return this.cmdInductive(r);
      case 'lemma':
      case 'theorem':
      case 'corollary':
      case 'proposition':
      case 'schematic_goal':
        return this.cmdLemma(r, c);
      case 'export_code':
      case 'hide_const':
      case 'notation':
      case 'no_notation':
        this.msg('warning', `Command "${kw}" is not supported in this web edition (ignored)`);
        return;
      default:
        throw new CmdError(`Command "${kw}" is not supported in this web edition`);
    }
  }

  pushDummy(c: Command) {
    this.stack.push(this.newBlock('dummy', [], [{ params: [], prems: [], concl: mkC('True', boolT) }], c.from));
  }

  readTyTok(t: OTok, tvEnv?: Map<string, Type>): Type {
    if (t.kind === 'string' || t.kind === 'cartouche' || t.kind === 'ident' || t.kind === 'tvar') {
      const e = new Elab({ thy: this.thy, fixed: new Map(), abbrevs: new Map() });
      return e.ty(parseType(t.v), tvEnv);
    }
    throw new CmdError('type expected');
  }

  cmdDatatype(r: TokReader) {
    const params: string[] = [];
    if (r.isSym('(')) {
      r.next();
      while (!r.isSym(')')) {
        const t = r.next();
        if (t.kind === 'tvar') params.push(t.v);
        else if (!(t.kind === 'sym' && t.v === ',')) r.fail('type variable expected');
      }
      r.next();
    } else if (r.peek()?.kind === 'tvar') params.push(r.next().v);
    const name = r.expectIdent().v;
    if (this.thy.types.has(name) && name !== 'list' && name !== 'option' && name !== 'prod') throw new CmdError(`Duplicate type declaration: "${name}"`);
    r.expectSym('=');
    // pre-register the type so recursive references resolve
    this.thy.types.set(name, params.length);
    const ctors: { name: string; argTys: Type[] }[] = [];
    for (;;) {
      const cn = r.next();
      if (cn.kind !== 'ident' && cn.kind !== 'string') r.fail('constructor name expected');
      const argTys: Type[] = [];
      while (!r.atEnd() && !r.isSym('|')) {
        const a = r.peek()!;
        if (a.kind === 'sym' && a.v === '(') {
          // mixfix annotation or named field: skip parenthesised group
          let depth = 0;
          let inner: OTok[] = [];
          do {
            const t = r.next();
            if (t.kind === 'sym' && t.v === '(') depth++;
            else if (t.kind === 'sym' && t.v === ')') depth--;
            else inner.push(t);
          } while (depth > 0);
          // named field: (sel: "type")
          if (inner.length >= 3 && inner[1].kind === 'sym' && inner[1].v === ':') argTys.push(this.readTyTok(inner[2]));
          inner = [];
          continue;
        }
        if (a.kind === 'ident' && (r.isSym('(', 1) === false) && a.v === 'and') r.fail('mutual datatypes are not supported');
        r.next();
        if (a.kind === 'string' || a.kind === 'ident' || a.kind === 'tvar' || a.kind === 'cartouche') {
          argTys.push(this.readTyTok(a));
        } else r.fail('constructor argument type expected');
      }
      ctors.push({ name: cn.v, argTys });
      if (r.isSym('|')) {
        r.next();
        continue;
      }
      break;
    }
    for (const c of ctors) for (const t of c.argTys) for (const v of tvarsOf(t)) if (!params.includes(v)) throw new CmdError(`Extra type variable on rhs: "${v}"`);
    declareDatatype(this.thy, { name, params, ctors });
  }

  /** Parse `name :: "type"` (optional type) */
  parseConstDecl(r: TokReader): { name: string; ty?: Type } {
    const n = r.next();
    if (n.kind !== 'ident' && n.kind !== 'string') r.fail('name expected');
    let ty: Type | undefined;
    if (r.isSym('::')) {
      r.next();
      ty = this.readTyTok(r.next());
    }
    // mixfix
    if (r.isSym('(')) {
      let depth = 0;
      do {
        const t = r.next();
        if (t.kind === 'sym' && t.v === '(') depth++;
        if (t.kind === 'sym' && t.v === ')') depth--;
      } while (depth > 0);
      this.msg('warning', 'Mixfix annotations are ignored in this web edition');
    }
    return { name: n.v, ty };
  }

  parseEqns(r: TokReader): { name?: string; attrs: Attr[]; src: string; tok: OTok }[] {
    const out: { name?: string; attrs: Attr[]; src: string; tok: OTok }[] = [];
    for (;;) {
      let name: string | undefined;
      let attrs: Attr[] = [];
      if (r.isIdent() && (r.isSym(':', 1) || r.isSym('[', 1))) {
        name = r.next().v;
        attrs = parseAttrsOpt(r);
        r.expectSym(':');
      } else if (r.isSym('[')) {
        attrs = parseAttrsOpt(r);
        r.expectSym(':');
      }
      const t = r.next();
      if (t.kind !== 'string' && t.kind !== 'cartouche') r.fail('equation expected (in quotes)');
      out.push({ name, attrs, src: t.v, tok: t });
      if (r.isSym('|')) {
        r.next();
        continue;
      }
      break;
    }
    return out;
  }

  cmdFun(kw: string, r: TokReader, c: Command) {
    if (r.isSym('(')) {
      // options like (sequential)
      while (!r.isSym(')')) r.next();
      r.next();
    }
    const decl = this.parseConstDecl(r);
    if (r.isIdent('and')) throw new CmdError('Mutual recursion is not supported in this web edition');
    r.expectIdent('where');
    const eqs = this.parseEqns(r);
    if (!r.atEnd()) r.fail('unexpected tokens after equations');
    if (this.thy.consts.has(decl.name)) throw new CmdError(`Duplicate constant declaration: "${decl.name}"`);
    const fty = decl.ty ?? freshTS();
    const ctx: TermCtx = { thy: this.thy, fixed: new Map([[decl.name, fty]]), abbrevs: new Map() };
    const read = readTerms(
      ctx,
      eqs.map((e) => ({ src: e.src, ty: boolT })),
    );
    let ty = read.fixed.get(decl.name)!;
    // generalise remaining schematic types in the function type
    const fC = mkC(decl.name, ty);
    const raw: RawEq[] = [];
    read.terms.forEach((t, i) => {
      const e = destApp(t, 'eq', 2);
      if (!e) throw new CmdError(`Equation ${i + 1}: not an equation "lhs = rhs"`);
      const { head, args } = stripApp(e[0]);
      if (!(head.k === 'F' && head.name === decl.name)) throw new CmdError(`Equation ${i + 1}: left-hand side must be an application of "${decl.name}"`);
      const conv = (u: Term): Term => substFrees(u, new Map([[decl.name, fC]]));
      const req: RawEq = { lhsArgs: args.map(conv), rhs: conv(e[1]) };
      checkLinearPatterns(req);
      const pv = new Set<string>();
      for (const a of req.lhsArgs) for (const k of frees(a).keys()) pv.add(k);
      for (const k of frees(req.rhs).keys()) if (!pv.has(k)) throw new CmdError(`Extra variables on rhs: "${k}" in equation ${i + 1}`);
      raw.push(req);
    });
    const arity = raw[0].lhsArgs.length;
    if (raw.some((x) => x.lhsArgs.length !== arity)) throw new CmdError('Function equations have different numbers of arguments');
    let completed;
    try {
      completed = completeEquations(this.thy, raw);
    } catch (e) {
      throw new CmdError((e as Error).message);
    }
    this.thy.addConst(decl.name, ty);
    if (!checkTermination(this.thy, decl.name, arity, completed)) {
      if (kw === 'function') this.msg('warning', 'Termination not proved automatically');
      else this.msg('warning', `Could not find a termination order for "${decl.name}" automatically; the definition is accepted, but beware of non-terminating rewriting`);
    }
    // missing patterns
    if (kw === 'primrec') {
      /* no extra check */
    }
    registerFun(this.thy, decl.name, ty, completed);
    if (completed.length !== raw.length) this.msg('info', `Patterns were completed into ${completed.length} non-overlapping equations (see ${decl.name}.simps)`);
    if (kw === 'function') this.pushDummy(c);
  }

  cmdDefinition(kw: string, r: TokReader) {
    let decl: { name: string; ty?: Type } | undefined;
    if (r.isIdent() && !r.isIdent('where')) {
      decl = this.parseConstDecl(r);
      r.expectIdent('where');
    }
    let thmName: string | undefined;
    if (r.isIdent() && r.isSym(':', 1)) {
      thmName = r.next().v;
      r.next();
    }
    const t = r.next();
    if (t.kind !== 'string' && t.kind !== 'cartouche') r.fail('definition equation expected');
    // determine name from lhs if not declared
    let name = decl?.name;
    if (!name) {
      const m = /^\s*([A-Za-z][A-Za-z0-9_']*)/.exec(t.v);
      if (!m) throw new CmdError('Bad definition: cannot determine the constant name');
      name = m[1];
    }
    if (this.thy.consts.has(name)) throw new CmdError(`Duplicate constant declaration: "${name}"`);
    const fty = decl?.ty ?? freshTS();
    const ctx: TermCtx = { thy: this.thy, fixed: new Map([[name, fty]]), abbrevs: new Map() };
    const read = readTerms(ctx, [{ src: t.v, ty: boolT }]);
    const ty = read.fixed.get(name)!;
    const prop = read.terms[0];
    const e = destApp(prop, 'eq', 2);
    if (!e) throw new CmdError('Definition must be an equation "c x = t" or "c x ≡ t"');
    const { head, args } = stripApp(e[0]);
    if (!(head.k === 'F' && head.name === name)) throw new CmdError(`Bad head of definition: expected "${name}"`);
    for (const a of args) if (a.k !== 'F') throw new CmdError('Arguments of a definition must be distinct variables');
    const C = mkC(name, ty);
    const conv = (u: Term): Term => substFrees(u, new Map([[name!, C]]));
    const pv = new Set(args.map((a) => (a as { name: string }).name));
    for (const k of frees(e[1]).keys()) if (!pv.has(k) && k !== name) throw new CmdError(`Extra variables on rhs: "${k}"`);
    if (frees(e[1]).has(name)) throw new CmdError('Recursive definitions need "fun"');
    this.thy.addConst(name, ty);
    const eq = generalize(mkEq(mkApps(C, args), conv(e[1])));
    const th: Thm = { name: thmName ?? name + '_def', prop: eq, global: true };
    this.thy.addThms(thmName ?? name + '_def', [th]);
    if (thmName) this.thy.addThms(name + '_def', [th]);
    this.thy.defs.set(name, [th]);
    if (kw === 'abbreviation') this.thy.addSimp(th);
  }

  cmdTypeSynonym(r: TokReader) {
    const params: string[] = [];
    if (r.isSym('(')) {
      r.next();
      while (!r.isSym(')')) {
        const t = r.next();
        if (t.kind === 'tvar') params.push(t.v);
      }
      r.next();
    } else if (r.peek()?.kind === 'tvar') params.push(r.next().v);
    const name = r.expectIdent().v;
    r.expectSym('=');
    const rhs = this.readTyTok(r.next());
    this.thy.typeSyns.set(name, { params, rhs });
  }

  cmdAxiomatization(kw: string, r: TokReader) {
    while (!r.atEnd() && !r.isIdent('where')) {
      const d = this.parseConstDecl(r);
      if (!d.ty) throw new CmdError('Type required for constant declaration');
      this.thy.addConst(d.name, d.ty);
      if (r.isIdent('and')) r.next();
    }
    if (kw === 'consts' || r.atEnd()) return;
    r.expectIdent('where');
    for (;;) {
      let name = 'axiom';
      if (r.isIdent() && r.isSym(':', 1)) {
        name = r.next().v;
        r.next();
      }
      const t = r.next();
      const read = readTerms({ thy: this.thy, fixed: new Map(), abbrevs: new Map() }, [{ src: t.v, ty: boolT }]);
      const th: Thm = { name, prop: generalize(read.terms[0]), global: true };
      this.thy.addThms(name, [th]);
      if (!this.opts.isPrelude) this.msg('warning', `Axiom "${name}" added without proof`);
      if (r.isIdent('and')) {
        r.next();
        continue;
      }
      break;
    }
  }

  cmdDeclare(r: TokReader) {
    const refs = parseFactRefs(r);
    for (const ref of refs) {
      const ths = this.thy.thms.get(ref.name);
      if (!ths) throw new CmdError(`Undefined fact: "${ref.name}"`);
      this.applyDeclAttrs(ref.name, ths, ref.attrs);
    }
  }

  applyDeclAttrs(name: string, ths: Thm[], attrs: Attr[]) {
    for (const a of attrs) {
      const del = a.args.some((t) => t.v === 'del');
      switch (a.name) {
        case 'simp':
          if (del) {
            this.thy.delSimp(name);
            for (const th of ths) this.thy.simpRules = this.thy.simpRules.filter((x) => x.prop !== th.prop);
          } else for (const th of ths) this.thy.addSimp(th);
          break;
        case 'intro':
          for (const th of ths) this.thy.introRules.push(th);
          break;
        case 'elim':
          for (const th of ths) this.thy.elimRules.push(th);
          break;
        case 'dest':
          for (const th of ths) this.thy.destRules.push(th);
          break;
        case 'iff':
          for (const th of ths) {
            this.thy.addSimp(th);
            this.thy.introRules.push(th);
          }
          break;
        case 'split':
          for (const th of ths) {
            const nm = th.name.replace(/\.split(_asm)?$/, '');
            const dt = this.thy.datatypes.get(nm);
            if (dt) {
              if (del) this.thy.splitRules.delete(dt.caseConst);
              else this.thy.splitRules.add(dt.caseConst);
            }
          }
          break;
        case 'code':
        case 'induct':
        case 'cases':
        case 'termination_simp':
          break;
        default:
          this.msg('warning', `Attribute "${a.name}" ignored in declaration`);
      }
    }
  }

  cmdLemmas(r: TokReader) {
    const name = r.expectIdent().v;
    const attrs = parseAttrsOpt(r);
    r.expectSym('=');
    const refs = parseFactRefs(r);
    const ths = this.resolveFacts(refs, null).map((t, i, arr) => ({ ...t, name: arr.length > 1 ? `${name}(${i + 1})` : name }));
    this.thy.addThms(name, ths);
    this.applyDeclAttrs(name, ths, attrs);
  }

  cmdInductive(r: TokReader) {
    const decl = this.parseConstDecl(r);
    if (r.isIdent('for')) throw new CmdError('"for" parameters of inductive definitions are not supported');
    r.expectIdent('where');
    const rules = this.parseEqns(r);
    const fty = decl.ty ?? freshTS();
    const ctx: TermCtx = { thy: this.thy, fixed: new Map([[decl.name, fty]]), abbrevs: new Map() };
    const read = readTerms(
      ctx,
      rules.map((e) => ({ src: e.src, ty: boolT })),
    );
    const ty = read.fixed.get(decl.name)!;
    const { args, res } = stripFunT(ty);
    if (!(res.k === 'T' && res.name === 'bool')) throw new CmdError('Inductive predicate must return bool');
    const C = mkC(decl.name, ty);
    this.thy.addConst(decl.name, ty);
    const intros: Thm[] = [];
    read.terms.forEach((t, i) => {
      const conv = substFrees(t, new Map([[decl.name, C]]));
      const g = termToGoal(conv);
      const h = stripApp(g.concl);
      if (!(h.head.k === 'C' && h.head.name === decl.name && h.args.length === args.length))
        throw new CmdError(`Rule ${i + 1}: conclusion must be of the form "${decl.name} ..."`);
      const nm = rules[i].name ?? `${decl.name}.intros(${i + 1})`;
      const th: Thm = { name: nm, prop: generalize(conv), global: true };
      intros.push(th);
      if (rules[i].name) {
        this.thy.addThms(rules[i].name!, [th]);
        this.thy.addThms(decl.name + '.' + rules[i].name!, [th]);
      }
    });
    this.thy.addThms(decl.name + '.intros', intros);
    const info: InductiveInfo = { name: decl.name, arity: args.length, intros };
    this.inductives.set(decl.name, info);
    this.thy.addThms(decl.name + '.induct', []);
    this.thy.addThms(decl.name + '.cases', []);
    // simp rules for ground evaluation are not added (as in Isabelle)
  }

  // ---------------- lemma ----------------
  newBlock(kind: BlockKind, stmts: Term[], goals: Goal[], from: number, ctx?: PCtx): Block {
    return {
      kind,
      attrs: [],
      stmts,
      assms: [],
      goals,
      mode: 'prove',
      ctx: ctx ?? { fixed: new Map(), facts: new Map(), abbrevs: new Map() },
      baseCtx: null,
      localFixes: [],
      localAssms: [],
      cases: [],
      using: [],
      chained: [],
      thisFacts: [],
      calc: null,
      error: false,
      sorry: false,
      from,
    };
  }

  /** Parse "name[attrs]:" prefix */
  parseThmDecl(r: TokReader): { name?: string; attrs: Attr[] } {
    let name: string | undefined;
    let attrs: Attr[] = [];
    if (r.isIdent() && (r.isSym(':', 1) || (r.isSym('[', 1) && this.attrsFollowedByColon(r, 1)))) {
      const n = r.peek()!.v;
      if (!['fixes', 'assumes', 'shows', 'obtains'].includes(n)) {
        name = r.next().v;
        attrs = parseAttrsOpt(r);
        r.expectSym(':');
      }
    } else if (r.isSym('[') && this.attrsFollowedByColon(r, 0)) {
      attrs = parseAttrsOpt(r);
      r.expectSym(':');
    }
    return { name, attrs };
  }

  attrsFollowedByColon(r: TokReader, o: number): boolean {
    let depth = 0;
    for (let i = o; ; i++) {
      const t = r.peek(i);
      if (!t) return false;
      if (t.kind === 'sym' && t.v === '[') depth++;
      if (t.kind === 'sym' && t.v === ']') {
        depth--;
        if (depth === 0) return r.isSym(':', i + 1);
      }
    }
  }

  termSrc(t: OTok): string {
    if (t.kind === 'var') return '?' + t.v;
    return t.v;
  }

  cmdLemma(r: TokReader, c: Command) {
    const { name, attrs } = this.parseThmDecl(r);
    const fixes: { name: string; ty?: Type }[] = [];
    const assumes: { name?: string; attrs: Attr[]; srcs: string[] }[] = [];
    const shows: string[] = [];
    const parseFixes = () => {
      for (;;) {
        const names: string[] = [];
        while (r.isIdent() && !['and', 'assumes', 'shows', 'fixes', 'obtains'].includes(r.peek()!.v)) names.push(r.next().v);
        let ty: Type | undefined;
        if (r.isSym('::')) {
          r.next();
          ty = this.readTyTok(r.next());
        }
        for (const n of names) fixes.push({ name: n, ty });
        if (r.isIdent('and')) {
          r.next();
          continue;
        }
        break;
      }
    };
    const parseProps = (): { name?: string; attrs: Attr[]; srcs: string[] }[] => {
      const out: { name?: string; attrs: Attr[]; srcs: string[] }[] = [];
      for (;;) {
        const d = this.parseThmDecl(r);
        const srcs: string[] = [];
        while (r.peek() && (r.peek()!.kind === 'string' || r.peek()!.kind === 'cartouche')) srcs.push(r.next().v);
        if (!srcs.length) r.fail('proposition expected');
        out.push({ name: d.name, attrs: d.attrs, srcs });
        if (r.isIdent('and')) {
          r.next();
          continue;
        }
        break;
      }
      return out;
    };
    if (r.isIdent('fixes') || r.isIdent('assumes') || r.isIdent('shows')) {
      while (!r.atEnd()) {
        const k = r.expectIdent().v;
        if (k === 'fixes') parseFixes();
        else if (k === 'assumes') assumes.push(...parseProps());
        else if (k === 'shows') shows.push(...parseProps().flatMap((p) => p.srcs));
        else r.fail(`unexpected "${k}"`);
      }
    } else {
      for (const p of parseProps()) shows.push(...p.srcs);
      if (r.isIdent('for')) {
        r.next();
        parseFixes();
      }
      if (!r.atEnd()) r.fail('unexpected tokens in statement');
    }
    if (!shows.length) throw new CmdError('No statement given');
    const fixed = new Map<string, Type>();
    for (const f of fixes) fixed.set(f.name, f.ty ?? freshTS());
    const ctx: TermCtx = { thy: this.thy, fixed, abbrevs: new Map() };
    const assmSrcs = assumes.flatMap((a) => a.srcs);
    const read = readTerms(ctx, [...assmSrcs, ...shows].map((s) => ({ src: s, ty: boolT })));
    const assmTs = read.terms.slice(0, assmSrcs.length);
    const showTs = read.terms.slice(assmSrcs.length);
    const pctx: PCtx = { fixed: new Map(), facts: new Map(), abbrevs: new Map() };
    for (const [k, v] of read.fixed) pctx.fixed.set(k, v);
    for (const [k, v] of read.newFrees) if (!k.startsWith('?')) pctx.fixed.set(k, v);
    // assumption facts
    let ai = 0;
    const allAssms: Thm[] = [];
    for (const a of assumes) {
      const ths: Thm[] = a.srcs.map(() => ({ name: a.name ?? 'assms', prop: assmTs[ai++] }));
      if (a.name) pctx.facts.set(a.name, ths);
      allAssms.push(...ths);
    }
    if (allAssms.length) pctx.facts.set('assms', allAssms);
    const b = this.newBlock(
      'lemma',
      showTs,
      showTs.map((t) => termToGoal(t)),
      c.from,
      pctx,
    );
    b.name = name;
    b.attrs = attrs;
    b.assms = assmTs;
    if (showTs.length === 1) pctx.abbrevs.set('thesis', showTs[0]);
    else pctx.abbrevs.set('thesis', conjs(showTs));
    this.stack.push(b);
  }

  // ---------------- proof commands ----------------
  requireMode(b: Block, modes: Block['mode'][], kw: string) {
    if (!modes.includes(b.mode)) throw new CmdError(`Illegal application of proof command "${kw}" in "${b.mode}" mode`);
  }

  cmdProof(kw: string, r: TokReader, c: Command) {
    const b = this.top!;
    switch (kw) {
      case 'apply': {
        this.requireMode(b, ['prove'], kw);
        const m = parseMethodTop(r);
        if (!r.atEnd()) r.fail('unexpected tokens after method');
        this.applyMethod(b, m);
        return;
      }
      case 'using':
      case 'unfolding': {
        this.requireMode(b, ['prove'], kw);
        const refs = parseFactRefs(r);
        const ths = this.resolveFacts(refs, b);
        if (kw === 'using') b.using.push(...ths);
        else this.unfoldGoals(b, ths);
        return;
      }
      case 'done': {
        this.requireMode(b, ['prove'], kw);
        if (b.goals.length) {
          this.msg('error', 'Failed to finish proof:\n' + printGoals(b.goals));
          b.error = true;
          this.markError();
        }
        this.finishBlock();
        return;
      }
      case 'by': {
        this.requireMode(b, ['prove'], kw);
        const m1 = parseMethodTop(r);
        const m2 = r.atEnd() ? null : parseMethodTop(r);
        if (!r.atEnd()) r.fail('unexpected tokens after method');
        this.terminalProof(b, m1, m2);
        return;
      }
      case '.':
      case '..': {
        this.requireMode(b, ['prove'], kw);
        const m: Meth = { m: 'name', name: kw === '.' ? 'this' : 'standard', args: [], from: c.from, to: c.to };
        this.terminalProof(b, m, null);
        return;
      }
      case 'sorry': {
        this.requireMode(b, ['prove', 'state'], kw);
        this.msg('warning', 'Proof skipped with "sorry"');
        b.sorry = true;
        b.goals = [];
        this.finishBlock();
        return;
      }
      case 'oops': {
        // abandon the whole top-level proof
        this.msg('warning', 'Proof abandoned with "oops"');
        this.stack = [];
        return;
      }
      case 'proof': {
        this.requireMode(b, ['prove'], kw);
        let m: Meth | null = null;
        if (!r.atEnd()) m = parseMethodTop(r);
        if (!r.atEnd()) r.fail('unexpected tokens after method');
        const mm: Meth = m ?? { m: 'name', name: 'standard', args: [], from: c.from, to: c.to };
        try {
          const st = evalMethod(this.methodEnv(b), mm, { goals: b.goals, facts: b.using });
          b.goals = st.goals;
          b.cases = st.cases ?? [];
        } catch (e) {
          this.reportMethodError(e);
        }
        b.using = [];
        b.mode = 'state';
        b.baseCtx = cloneCtx(b.ctx);
        b.localFixes = [];
        b.localAssms = [];
        b.thisFacts = [];
        return;
      }
      case 'qed': {
        this.requireMode(b, ['state'], kw);
        if (!r.atEnd()) {
          const m = parseMethodTop(r);
          try {
            const st = evalMethod(this.methodEnv(b), m, { goals: b.goals, facts: [] });
            b.goals = st.goals;
          } catch (e) {
            this.reportMethodError(e);
          }
        }
        if (b.goals.length) {
          this.msg('error', 'Failed to finish proof:\n' + printGoals(b.goals));
          this.markError();
        }
        this.finishBlock();
        return;
      }
      case 'next': {
        this.requireMode(b, ['state'], kw);
        if (!b.baseCtx) throw new CmdError('"next" outside of a proof block');
        b.ctx = cloneCtx(b.baseCtx);
        b.localFixes = [];
        b.localAssms = [];
        b.thisFacts = [];
        b.calc = null;
        return;
      }
      case 'fix': {
        this.requireMode(b, ['state'], kw);
        for (;;) {
          const names: string[] = [];
          while (r.isIdent() && !r.isIdent('and')) names.push(r.next().v);
          let ty: Type | undefined;
          if (r.isSym('::')) {
            r.next();
            ty = this.readTyTok(r.next());
          }
          for (const n of names) {
            const t = ty ?? freshTS();
            b.ctx.fixed.set(n, t);
            b.localFixes.push(mkF(n, t) as Term & { k: 'F' });
          }
          if (r.isIdent('and')) {
            r.next();
            continue;
          }
          break;
        }
        if (!r.atEnd()) r.fail('unexpected tokens');
        return;
      }
      case 'assume':
      case 'presume': {
        this.requireMode(b, ['state', 'chain'], kw);
        const props = this.parseStatements(r, b);
        const ths: Thm[] = [];
        for (const p of props) {
          const pts: Thm[] = p.terms.map((t) => ({ name: p.name ?? 'this', prop: t }));
          if (p.name) b.ctx.facts.set(p.name, pts);
          ths.push(...pts);
          b.localAssms.push(...p.terms);
        }
        b.thisFacts = ths;
        b.mode = 'state';
        return;
      }
      case 'have':
      case 'show':
      case 'hence':
      case 'thus': {
        const chained = kw === 'hence' || kw === 'thus' ? (this.requireMode(b, ['state'], kw), b.thisFacts) : b.mode === 'chain' ? b.chained : [];
        this.requireMode(b, kw === 'hence' || kw === 'thus' ? ['state'] : ['state', 'chain'], kw);
        const props = this.parseStatements(r, b);
        const stmts = props.flatMap((p) => p.terms);
        const blk = this.newBlock(kw === 'show' || kw === 'thus' ? 'show' : 'have', stmts, stmts.map((t) => termToGoal(t, new Set(b.ctx.fixed.keys()))), c.from, cloneCtx(b.ctx));
        blk.name = props.length === 1 ? props[0].name : undefined;
        blk.attrs = props.length === 1 ? props[0].attrs : [];
        blk.using = [...chained];
        blk.ctx.abbrevs.set('thesis', stmts.length === 1 ? stmts[0] : conjs(stmts));
        b.mode = 'state';
        b.chained = [];
        this.stack.push(blk);
        return;
      }
      case 'then': {
        this.requireMode(b, ['state'], kw);
        b.chained = b.thisFacts;
        b.mode = 'chain';
        return;
      }
      case 'from':
      case 'with': {
        this.requireMode(b, ['state'], kw);
        const ths = this.resolveFacts(parseFactRefs(r), b);
        b.chained = kw === 'with' ? [...ths, ...b.thisFacts] : ths;
        b.thisFacts = b.chained;
        b.mode = 'chain';
        return;
      }
      case 'note': {
        this.requireMode(b, ['state'], kw);
        let name: string | undefined;
        if (r.isIdent() && r.isSym('=', 1)) {
          name = r.next().v;
          r.next();
        } else if (r.isIdent() && r.isSym('[', 1) && this.hasEqAfterAttrs(r)) {
          name = r.next().v;
          parseAttrsOpt(r);
          r.expectSym('=');
        }
        const ths = this.resolveFacts(parseFactRefs(r), b);
        if (name) b.ctx.facts.set(name, ths);
        b.thisFacts = ths;
        return;
      }
      case 'case':
        return this.cmdCase(r, b);
      case 'let': {
        this.requireMode(b, ['state'], kw);
        for (;;) {
          const v = r.next();
          if (v.kind !== 'var') r.fail('?variable expected');
          r.expectSym('=');
          const t = r.termArg();
          const read = readTerms(this.termCtx(b), [{ src: this.termSrc(t) }]);
          b.ctx.abbrevs.set(v.v, read.terms[0]);
          if (r.isIdent('and')) {
            r.next();
            continue;
          }
          break;
        }
        return;
      }
      case 'obtain':
        return this.cmdObtain(r, b, c);
      case 'moreover': {
        this.requireMode(b, ['state'], kw);
        b.calc = [...(b.calc ?? []), ...b.thisFacts];
        b.calcMode = 'moreover';
        return;
      }
      case 'ultimately': {
        this.requireMode(b, ['state'], kw);
        b.chained = [...(b.calc ?? []), ...b.thisFacts];
        b.calc = null;
        b.mode = 'chain';
        return;
      }
      case 'also':
      case 'finally': {
        this.requireMode(b, ['state'], kw);
        if (!b.thisFacts.length) throw new CmdError(`No facts for "${kw}"`);
        const cur = b.thisFacts[0];
        let calc: Thm;
        if (!b.calc || b.calcMode !== 'also') calc = cur;
        else calc = this.transitive(b.calc[0], cur);
        b.calcMode = 'also';
        const rel = stripApp(calc.prop);
        if (rel.args.length === 2) b.ctx.dots = rel.args[1];
        if (kw === 'also') {
          b.calc = [calc];
          this.cur.messages.push({ severity: 'info', text: 'calculation:\n  ' + printTerm(calc.prop) });
        } else {
          b.calc = null;
          b.chained = [calc];
          b.thisFacts = [calc];
          b.mode = 'chain';
          this.cur.messages.push({ severity: 'info', text: 'calculation:\n  ' + printTerm(calc.prop) });
        }
        return;
      }
      case 'defer':
      case 'prefer': {
        this.requireMode(b, ['prove'], kw);
        const n = r.peek()?.kind === 'nat' ? Number(r.next().v) : 1;
        if (n < 1 || n > b.goals.length) throw new CmdError(`No such subgoal: ${n}`);
        const g = b.goals[n - 1];
        const rest = b.goals.filter((_, i) => i !== n - 1);
        b.goals = kw === 'defer' ? [...rest, g] : [g, ...rest];
        return;
      }
      case 'back':
        this.msg('warning', '"back" has no effect in this web edition');
        return;
      case 'subgoal': {
        this.requireMode(b, ['prove'], kw);
        if (!b.goals.length) throw new CmdError('No subgoals!');
        const g = b.goals[0];
        const blk = this.newBlock('subgoal', [], [g], c.from, cloneCtx(b.ctx));
        for (const p of g.params) blk.ctx.fixed.set(p.name, p.ty);
        blk.using = b.using;
        b.using = [];
        // premises available as facts
        blk.ctx.facts.set('prems', g.prems.map((p) => ({ name: 'prems', prop: p })));
        this.stack.push(blk);
        return;
      }
      case '{': {
        this.requireMode(b, ['state'], kw);
        const blk = this.newBlock('brace', [], [], c.from, cloneCtx(b.ctx));
        blk.mode = 'state';
        blk.baseCtx = cloneCtx(blk.ctx);
        this.stack.push(blk);
        return;
      }
      case '}': {
        if (b.kind !== 'brace') throw new CmdError('Unmatched "}"');
        this.stack.pop();
        const parent = this.top!;
        // export last fact, discharging local assumptions
        const last = b.thisFacts[0];
        if (last) {
          let prop = last.prop;
          for (let i = b.localAssms.length - 1; i >= 0; i--) prop = mkMetaImp(b.localAssms[i], prop);
          parent.thisFacts = [{ name: 'this', prop: generalize(prop, new Set(parent.ctx.fixed.keys())) }];
        }
        return;
      }
      case 'quickcheck':
      case 'nitpick': {
        const g = b.goals[0];
        if (!g) throw new CmdError('No subgoal to check');
        const res = quickcheck(this.thy, g);
        this.cur.messages.push({ severity: res.found ? 'warning' : 'info', text: res.text });
        return;
      }
      case 'sledgehammer':
      case 'try':
      case 'try0': {
        this.requireMode(b, ['prove'], kw);
        this.cmdTry(b);
        return;
      }
      case 'supply':
        this.msg('warning', '"supply" is ignored in this web edition');
        return;
      case 'termination':
        throw new CmdError('Illegal "termination" inside proof');
    }
    throw new CmdError(`Unsupported command "${kw}"`);
  }

  hasEqAfterAttrs(r: TokReader): boolean {
    let depth = 0;
    for (let i = 1; ; i++) {
      const t = r.peek(i);
      if (!t) return false;
      if (t.kind === 'sym' && t.v === '[') depth++;
      if (t.kind === 'sym' && t.v === ']') {
        depth--;
        if (depth === 0) return r.isSym('=', i + 1);
      }
    }
  }

  termCtx(b: Block, extraFixed?: Map<string, Type>): TermCtx {
    const fixed = new Map(b.ctx.fixed);
    if (extraFixed) for (const [k, v] of extraFixed) fixed.set(k, v);
    return { thy: this.thy, fixed, abbrevs: b.ctx.abbrevs, dots: b.ctx.dots };
  }

  /** statements: [name[attrs]:] "p" "q" and ... */
  parseStatements(r: TokReader, b: Block): { name?: string; attrs: Attr[]; terms: Term[] }[] {
    const groups: { name?: string; attrs: Attr[]; srcs: string[] }[] = [];
    for (;;) {
      const d = this.parseThmDecl(r);
      const srcs: string[] = [];
      while (r.peek() && (['string', 'cartouche', 'var', 'nat'].includes(r.peek()!.kind) || (r.peek()!.kind === 'ident' && !['and', 'if', 'for', 'when'].includes(r.peek()!.v))))
        srcs.push(this.termSrc(r.next()));
      if (!srcs.length) r.fail('proposition expected');
      groups.push({ name: d.name, attrs: d.attrs, srcs });
      if (r.isIdent('and')) {
        r.next();
        continue;
      }
      break;
    }
    if (r.isIdent('if') || r.isIdent('for')) throw new CmdError('"if"/"for" clauses in statements are not supported in this web edition; use fix/assume');
    if (!r.atEnd()) r.fail('unexpected tokens in statement');
    const ctx = this.termCtx(b);
    const read = readTerms(
      ctx,
      groups.flatMap((g) => g.srcs).map((s) => ({ src: s, ty: boolT })),
    );
    // update fixed types that got resolved
    for (const [k, v] of read.fixed) if (b.ctx.fixed.has(k)) b.ctx.fixed.set(k, v);
    for (const blk of this.stack) for (const [k, v] of read.fixed) if (blk.ctx.fixed.has(k)) blk.ctx.fixed.set(k, v);
    let i = 0;
    return groups.map((g) => ({ name: g.name, attrs: g.attrs, terms: g.srcs.map(() => read.terms[i++]) }));
  }

  cmdCase(r: TokReader, b: Block) {
    this.requireMode(b, ['state'], 'case');
    let cname: string;
    const names: string[] = [];
    if (r.isSym('(')) {
      r.next();
      const t = r.next();
      cname = t.v;
      while (!r.isSym(')')) {
        const n = r.next();
        names.push(n.v);
      }
      r.next();
    } else {
      const t = r.next();
      cname = t.v;
    }
    const ci = b.cases.find((c) => c.name === cname);
    if (!ci) {
      const avail = b.cases.map((c) => c.name).join(', ');
      throw new CmdError(`Undefined case: "${cname}"${avail ? ` (available: ${avail})` : ''}`);
    }
    // rename fixes
    const ren = new Map<string, Term>();
    const fixes: (Term & { k: 'F' })[] = [];
    ci.fixes.forEach((f, i) => {
      const nm = names[i] && names[i] !== '_' ? names[i] : f.name;
      const nf = mkF(nm, f.ty) as Term & { k: 'F' };
      ren.set(f.name, nf);
      fixes.push(nf);
    });
    if (names.length > ci.fixes.length) throw new CmdError(`Too many parameters for case "${cname}"`);
    const sub = (t: Term) => substFrees(t, ren);
    for (const f of fixes) b.ctx.fixed.set(f.name, f.ty);
    b.localFixes.push(...fixes);
    const assumes = ci.assumes.map(sub);
    b.localAssms.push(...assumes);
    const mk = (ts: Term[], n: string): Thm[] => ts.map((t) => ({ name: n, prop: sub(t) }));
    if (ci.assumes.length) b.ctx.facts.set(cname, mk(ci.assumes, cname));
    b.ctx.facts.set(cname + '.IH', mk(ci.ih, cname + '.IH'));
    b.ctx.facts.set(cname + '.hyps', mk(ci.ih.length ? ci.ih : ci.assumes.filter((a) => !ci.prems.includes(a)), cname + '.hyps'));
    b.ctx.facts.set(cname + '.prems', mk(ci.prems, cname + '.prems'));
    b.ctx.facts.set('IH', mk(ci.ih, 'IH'));
    b.ctx.facts.set('prems', mk(ci.prems, 'prems'));
    b.ctx.abbrevs.set('case', sub(ci.concl));
    b.thisFacts = mk(ci.assumes, cname);
  }

  cmdObtain(r: TokReader, b: Block, c: Command) {
    this.requireMode(b, ['state', 'chain'], 'obtain');
    const vars: { name: string; ty?: Type }[] = [];
    for (;;) {
      while (r.isIdent() && !r.isIdent('where') && !r.isIdent('and')) vars.push({ name: r.next().v });
      if (r.isSym('::')) {
        r.next();
        const ty = this.readTyTok(r.next());
        for (const v of vars) if (!v.ty) v.ty = ty;
      }
      if (r.isIdent('and')) {
        r.next();
        continue;
      }
      break;
    }
    r.expectIdent('where');
    const extra = new Map<string, Type>();
    for (const v of vars) extra.set(v.name, v.ty ?? freshTS());
    const groups: { name?: string; srcs: string[] }[] = [];
    for (;;) {
      const d = this.parseThmDecl(r);
      const srcs: string[] = [];
      while (r.peek() && ['string', 'cartouche'].includes(r.peek()!.kind)) srcs.push(r.next().v);
      groups.push({ name: d.name, srcs });
      if (r.isIdent('and')) {
        r.next();
        continue;
      }
      break;
    }
    if (!r.atEnd()) r.fail('unexpected tokens');
    const ctx = this.termCtx(b, extra);
    const read = readTerms(
      ctx,
      groups.flatMap((g) => g.srcs).map((s) => ({ src: s, ty: boolT })),
    );
    const vs = vars.map((v) => mkF(v.name, read.fixed.get(v.name)!) as Term & { k: 'F' });
    let stmt = conjs(read.terms);
    for (let i = vs.length - 1; i >= 0; i--) stmt = mkEx(vs[i], stmt);
    const chained = b.mode === 'chain' ? b.chained : [];
    const blk = this.newBlock('obtain', [stmt], [termToGoal(stmt)], c.from, cloneCtx(b.ctx));
    blk.using = [...chained];
    let i = 0;
    blk.obtain = { vars: vs, props: read.terms, names: groups.flatMap((g) => g.srcs.map(() => (i++, g.name))) };
    b.mode = 'state';
    b.chained = [];
    this.stack.push(blk);
  }

  transitive(a: Thm, bth: Thm): Thm {
    const ra = stripApp(a.prop);
    const rb = stripApp(bth.prop);
    if (ra.head.k !== 'C' || rb.head.k !== 'C' || ra.args.length !== 2 || rb.args.length !== 2) throw new CmdError('No transitivity rule for these facts');
    const [x, y] = ra.args;
    const [y2, z] = rb.args;
    if (!termEq(betaNorm(y), betaNorm(y2))) throw new CmdError(`Calculation mismatch: "${printTerm(y)}" vs "${printTerm(y2)}"`);
    const ra1 = ra.head.name;
    const rb1 = rb.head.name;
    let rel: string;
    if (ra1 === 'eq' && rb1 === 'eq') rel = 'eq';
    else if (ra1 === 'eq') rel = rb1;
    else if (rb1 === 'eq') rel = ra1;
    else if ((ra1 === 'less' || ra1 === 'less_eq') && (rb1 === 'less' || rb1 === 'less_eq')) rel = ra1 === 'less' || rb1 === 'less' ? 'less' : 'less_eq';
    else if (ra1 === rb1 && (ra1 === 'subset_eq' || ra1 === 'imp' || ra1 === 'dvd')) rel = ra1;
    else throw new CmdError('No transitivity rule for these facts');
    const ty = typeOf(x);
    return { name: 'calculation', prop: mkApps(mkC(rel, funT(ty, funT(ty, boolT))), [x, z]) };
  }

  unfoldGoals(b: Block, ths: Thm[]) {
    const m: Meth = { m: 'name', name: 'unfold', args: [], from: 0, to: 0 };
    const env = this.methodEnv(b);
    const env2: MethodEnv = { ...env, resolveFacts: () => ths };
    try {
      const st = evalMethod(env2, m, { goals: b.goals, facts: [] });
      b.goals = st.goals;
    } catch (e) {
      this.reportMethodError(e);
    }
    // also unfold chained facts
    const ss = buildSimpset(this.thy, ths, [], true);
    b.using = b.using.map((f) => ({ ...f, prop: simpTerm(this.thy, ss, instThm(f), 2000) }));
  }

  reportMethodError(e: unknown) {
    if (e instanceof MethodFail || e instanceof EngineError || e instanceof OuterError || e instanceof CmdError) {
      this.msg('error', e.message);
      this.markError();
      return;
    }
    throw e;
  }

  applyMethod(b: Block, m: Meth) {
    try {
      const st = evalMethod(this.methodEnv(b), m, { goals: b.goals, facts: b.using });
      b.goals = st.goals;
      if (st.cases) b.cases = st.cases;
      b.using = [];
      if (b.goals.length === 0) this.cur.messages.push({ severity: 'info', text: 'No subgoals!' });
    } catch (e) {
      b.using = [];
      this.reportMethodError(e);
    }
  }

  terminalProof(b: Block, m1: Meth, m2: Meth | null) {
    let ok = true;
    try {
      const env = this.methodEnv(b);
      let st: ProofState = evalMethod(env, m1, { goals: b.goals, facts: b.using });
      if (m2) st = evalMethod(env, m2, st);
      // finish remaining goals by assumption
      const rest: Goal[] = [];
      for (const g of st.goals) {
        const r = assumptionTac(g);
        if (!r) rest.push(g);
      }
      b.goals = rest;
      if (rest.length) {
        ok = false;
        this.msg('error', 'Failed to finish proof:\n' + printGoals(rest));
        this.markError();
      }
    } catch (e) {
      ok = false;
      this.reportMethodError(e);
    }
    void ok;
    b.goals = [];
    b.using = [];
    this.finishBlock();
  }

  methodEnv(b: Block): MethodEnv {
    return {
      thy: this.thy,
      resolveFacts: (refs: FactRef[]) => this.resolveFacts(refs, b),
      readTerm: (src: string, g?: Goal) => {
        const extra = new Map<string, Type>();
        if (g) for (const p of g.params) extra.set(p.name, p.ty);
        if (g) for (const t of [...g.prems, g.concl]) for (const [k, v] of frees(t)) if (!extra.has(k)) extra.set(k, (v as { ty: Type }).ty);
        return readTerms(this.termCtx(b, extra), [{ src }]).terms[0];
      },
      getFun: (n: string) => this.thy.funs.get(n),
      getInductive: (n: string) => this.inductives.get(n),
      stepLimit: this.opts.stepLimit,
    };
  }

  // ---------------- facts ----------------
  resolveFacts(refs: FactRef[], b: Block | null): Thm[] {
    const out: Thm[] = [];
    for (const ref of refs) {
      let ths: Thm[] | undefined;
      if (ref.literal !== undefined) {
        const prop = b ? readTerms(this.termCtx(b), [{ src: ref.literal, ty: boolT }]).terms[0] : null;
        if (!prop) throw new CmdError('Fact literal outside proof');
        const cands: Thm[] = [];
        for (const blk of [...this.stack].reverse()) {
          for (const fs of blk.ctx.facts.values()) cands.push(...fs);
          cands.push(...blk.thisFacts);
          for (const a of blk.localAssms) cands.push({ name: 'assm', prop: a });
          if (blk.calc) cands.push(...blk.calc);
        }
        const f = cands.find((c) => termEq(betaNorm(c.prop), betaNorm(prop)));
        if (!f) throw new CmdError(`Failed to retrieve literal fact: ‹${ref.literal}›`);
        ths = [f];
      } else {
        const name = ref.name;
        if (b) {
          if (name === 'this') ths = this.top?.thisFacts ?? [];
          else if (name === 'calculation') ths = this.top?.calc ?? [];
          else ths = b.ctx.facts.get(name);
        }
        if (!ths) ths = this.thy.thms.get(name);
        if (!ths) {
          // f.simps(2) style handled via selection; also allow "name(i)" key directly
          const fn = this.thy.funs.get(name.replace(/\.(simps|induct)$/, ''));
          if (fn && name.endsWith('.induct')) ths = [];
        }
        if (!ths) throw new CmdError(`Undefined fact: "${name}"`);
      }
      if (ref.sel) {
        const sel: Thm[] = [];
        for (const i of ref.sel) {
          if (i < 0) {
            for (let k = -i; k <= ths.length; k++) sel.push(ths[k - 1]);
            continue;
          }
          if (i < 1 || i > ths.length) throw new CmdError(`Bad fact selection "${ref.name}(${i})": only ${ths.length} fact(s)`);
          sel.push(ths[i - 1]);
        }
        ths = sel;
      }
      for (const a of ref.attrs) ths = ths.map((t) => this.applyAttr(t, a, b));
      out.push(...ths);
    }
    return out;
  }

  applyAttr(th: Thm, a: Attr, b: Block | null): Thm {
    switch (a.name) {
      case 'simp':
      case 'intro':
      case 'elim':
      case 'dest':
      case 'iff':
      case 'induct':
        return th;
      case 'symmetric': {
        const p = instThm(th);
        const r = decomposeRule(p);
        const e = destApp(r.concl, 'eq', 2);
        if (!e) throw new CmdError('symmetric: not an equation');
        let res: Term = mkEq(e[1], e[0]);
        for (let i = r.prems.length - 1; i >= 0; i--) res = mkMetaImp(r.prems[i], res);
        return { name: th.name, prop: res };
      }
      case 'of':
      case 'where': {
        const p = instThm(th);
        const vs: (Term & { k: 'V' })[] = [];
        const collect = (t: Term) => {
          if (t.k === 'V' && !vs.some((v) => v.name === t.name)) vs.push(t);
          if (t.k === 'A') {
            collect(t.f);
            collect(t.a);
          }
          if (t.k === 'L') collect(t.body);
        };
        collect(p);
        let s: Subst = emptySubst();
        const ctx = b ? this.termCtx(b) : { thy: this.thy, fixed: new Map(), abbrevs: new Map() };
        if (a.name === 'of') {
          let i = 0;
          for (const t of a.args) {
            if (t.kind === 'sym' && t.v === '_') {
              i++;
              continue;
            }
            if (i >= vs.length) throw new CmdError(`More instantiations than variables in theorem`);
            const term = readTerms(ctx, [{ src: this.termSrc(t) }]).terms[0];
            const s2 = unify(vs[i], term, s);
            if (!s2) throw new CmdError(`Type mismatch instantiating variable ?${vs[i].name.replace(/__\d+$/, '')}`);
            s = s2;
            i++;
          }
        } else {
          const toks = a.args;
          for (let i = 0; i < toks.length; ) {
            const v = toks[i];
            if (toks[i + 1]?.v !== '=') throw new CmdError('where: expected "x = t"');
            const t = toks[i + 2];
            const target = vs.find((x) => x.name.replace(/__\d+$/, '') === v.v.replace(/^\?/, ''));
            if (!target) throw new CmdError(`No such variable ?${v.v}`);
            const term = readTerms(ctx, [{ src: this.termSrc(t) }]).terms[0];
            const s2 = unify(target, term, s);
            if (!s2) throw new CmdError(`Type mismatch instantiating ?${v.v}`);
            s = s2;
            i += 3;
            if (toks[i]?.v === 'and') i++;
          }
        }
        return { name: th.name, prop: inst(p, s) };
      }
      case 'OF': {
        const rr = new TokReader(a.args, this.cmdOf(a.args));
        const facts = this.resolveFacts(parseFactRefs(rr), b);
        const p = instThm(th);
        const r = decomposeRule(p);
        let s: Subst = emptySubst();
        const prems = [...r.prems];
        let idx = 0;
        for (const f of facts) {
          if (idx >= prems.length) throw new CmdError('OF: too many facts');
          const s2 = unify(prems[idx], instThm(f), s);
          if (!s2) throw new CmdError(`OF: fact ${printTerm(instThm(f))} does not match premise ${printTerm(inst(prems[idx], s))}`);
          s = s2;
          prems.splice(idx, 1);
        }
        let res: Term = r.concl;
        for (let i = prems.length - 1; i >= 0; i--) res = mkMetaImp(prems[i], res);
        return { name: th.name, prop: inst(res, s) };
      }
      case 'THEN': {
        const rr = new TokReader(a.args, this.cmdOf(a.args));
        const rules = this.resolveFacts(parseFactRefs(rr), b);
        const rule = decomposeRule(instThm(rules[0]));
        const s = unify(rule.prems[0], instThm(th));
        if (!s) throw new CmdError('THEN: fact does not match first premise of rule');
        let res: Term = rule.concl;
        for (let i = rule.prems.length - 1; i >= 1; i--) res = mkMetaImp(rule.prems[i], res);
        return { name: th.name, prop: inst(res, s) };
      }
      case 'rule_format': {
        // ∀x. A ⟶ B  into  A ⟹ B with schematic x
        let p = instThm(th);
        const conv = (t: Term): Term => {
          const s = stripApp(t);
          if (s.head.k === 'C' && s.head.name === 'All' && s.args[0]?.k === 'L') {
            const lam = s.args[0];
            return conv(betaNorm({ k: 'A', f: lam, a: mkV(lam.x + '_rf' + Math.random().toString(36).slice(2, 6), lam.ty) }));
          }
          const im = destApp(t, 'imp', 2);
          if (im) return mkMetaImp(im[0], conv(im[1]));
          const mi = destApp(t, '==>', 2);
          if (mi) return mkMetaImp(mi[0], conv(mi[1]));
          return t;
        };
        p = conv(p);
        return { name: th.name, prop: p };
      }
      default:
        this.msg('warning', `Attribute "${a.name}" ignored`);
        return th;
    }
  }

  cmdOf(toks: OTok[]): Command {
    return { kw: 'attr', toks, from: toks[0]?.from ?? 0, to: toks[toks.length - 1]?.to ?? 0 };
  }

  // ---------------- finishing blocks ----------------
  finishBlock() {
    const b = this.stack.pop()!;
    const parent = this.top;
    if (b.kind === 'dummy') return;
    if (b.kind === 'lemma') {
      let prop: Term;
      const props = b.stmts.map((s) => {
        let p = s;
        for (let i = b.assms.length - 1; i >= 0; i--) p = mkMetaImp(b.assms[i], p);
        return generalize(p);
      });
      const ths: Thm[] = props.map((p, i) => ({ name: b.name ? (props.length > 1 ? `${b.name}(${i + 1})` : b.name) : 'unnamed', prop: p, global: true }));
      if (b.name) {
        this.thy.addThms(b.name, ths);
        this.applyDeclAttrs(b.name, ths, b.attrs);
      } else if (b.attrs.length) this.applyDeclAttrs('unnamed', ths, b.attrs);
      prop = props[0];
      const statement = props.map((p) => printTerm(p)).join('\n');
      this.theorems.push({ name: b.name ?? '', statement, sorry: b.sorry, error: b.error, from: b.from, to: this.cur.to });
      if (!b.error) this.cur.messages.push({ severity: 'info', text: `theorem ${b.name ? b.name + ': ' : ''}${statement}` });
      void prop;
      // propagate sorry flags
      return;
    }
    if (!parent) return;
    if (b.sorry) parent.sorry = true;
    if (b.error) parent.error = true;
    if (b.kind === 'subgoal') {
      parent.goals = parent.goals.slice(1);
      return;
    }
    if (b.kind === 'obtain') {
      const ob = b.obtain!;
      for (const v of ob.vars) parent.ctx.fixed.set(v.name, v.ty);
      const ths: Thm[] = ob.props.map((p, i) => ({ name: ob.names[i] ?? 'this', prop: p }));
      const named = new Map<string, Thm[]>();
      ob.props.forEach((p, i) => {
        const n = ob.names[i];
        if (n) named.set(n, [...(named.get(n) ?? []), ths[i]]);
      });
      for (const [k, v] of named) parent.ctx.facts.set(k, v);
      parent.thisFacts = ths;
      parent.mode = 'state';
      return;
    }
    if (b.kind === 'have' || b.kind === 'show') {
      const ths: Thm[] = b.stmts.map((s, i) => ({ name: b.name ? (b.stmts.length > 1 ? `${b.name}(${i + 1})` : b.name) : 'this', prop: s }));
      if (b.name) parent.ctx.facts.set(b.name, ths);
      parent.ctx.facts.set('__anon', [...(parent.ctx.facts.get('__anon') ?? []), ...ths]);
      parent.thisFacts = ths;
      parent.mode = 'state';
      if (b.kind === 'show') {
        for (const s of b.stmts) {
          if (!this.discharge(parent, s)) {
            this.msg('error', `Failed to refine any pending goal\nLocal statement fails to refine any pending goal\nFailed attempt to solve goal by exported rule:\n  ${printTerm(this.exportShow(parent, s))}`);
            this.markError();
          }
        }
      }
    }
  }

  exportShow(parent: Block, s: Term): Term {
    let t = s;
    for (let i = parent.localAssms.length - 1; i >= 0; i--) t = mkMetaImp(parent.localAssms[i], t);
    return t;
  }

  /** Discharge a pending goal of the parent block by the shown statement. */
  discharge(parent: Block, s: Term): boolean {
    const fixNames = new Set(parent.localFixes.map((f) => f.name));
    const toV = new Map<string, Term>();
    for (const f of parent.localFixes) toV.set(f.name, mkV('_fx_' + f.name, f.ty));
    const sg = termToGoal(s, new Set(parent.ctx.fixed.keys()));
    const conclP = substFrees(sg.concl, toV);
    const assmsP = [...parent.localAssms, ...sg.prems].map((a) => substFrees(a, toV));
    for (let gi = 0; gi < parent.goals.length; gi++) {
      const g = parent.goals[gi];
      let sub = unify(conclP, g.concl);
      if (!sub) continue;
      let ok = true;
      for (const a of assmsP) {
        let found = false;
        for (const p of g.prems) {
          const s2 = unify(a, p, sub!);
          if (s2) {
            sub = s2;
            found = true;
            break;
          }
        }
        if (!found) {
          // allow assumptions that are trivially true
          const ai = inst(a, sub!);
          if (isConst(ai, 'True')) continue;
          ok = false;
          break;
        }
      }
      if (!ok) continue;
      void fixNames;
      parent.goals = parent.goals.filter((_, i) => i !== gi).map((x) => instGoal(x, sub!));
      return true;
    }
    return false;
  }

  // ---------------- diagnostics ----------------
  cmdDiag(kw: string, r: TokReader) {
    const b = this.top;
    const ctx: TermCtx = b ? this.termCtx(b) : { thy: this.thy, fixed: new Map(), abbrevs: new Map() };
    switch (kw) {
      case 'value': {
        if (r.isSym('[')) parseAttrsOpt(r);
        const t = r.termArg();
        const read = readTerms(ctx, [{ src: this.termSrc(t) }]);
        const term = read.terms[0];
        const ss = buildSimpset(this.thy);
        let v: Term;
        try {
          v = simpTerm(this.thy, ss, term, 50000);
        } catch (e) {
          if (e instanceof SimpLimit) throw new CmdError('Evaluation did not terminate within the step limit');
          throw e;
        }
        this.cur.messages.push({ severity: 'info', text: `"${printTerm(v)}"\n  :: "${printType(typeOf(v))}"` });
        return;
      }
      case 'term':
      case 'prop': {
        const t = r.termArg();
        const read = readTerms(ctx, [{ src: this.termSrc(t), ty: kw === 'prop' ? boolT : undefined }]);
        const term = read.terms[0];
        this.cur.messages.push({ severity: 'info', text: `"${printTerm(term)}"\n  :: "${printType(typeOf(term))}"` });
        return;
      }
      case 'typ': {
        const t = r.next();
        this.cur.messages.push({ severity: 'info', text: `"${printType(this.readTyTok(t))}"` });
        return;
      }
      case 'thm': {
        const refs = parseFactRefs(r);
        const ths = this.resolveFacts(refs, b ?? null);
        this.cur.messages.push({ severity: 'info', text: ths.map((t) => printTerm(t.prop)).join('\n') || '(no facts)' });
        return;
      }
      case 'print_theorems':
        return;
      case 'print_state':
        return;
      case 'find_theorems': {
        const crit: { name?: string; pattern?: Term }[] = [];
        while (!r.atEnd()) {
          const t = r.next();
          if (t.kind === 'ident' && t.v === 'name' && r.isSym(':')) {
            r.next();
            crit.push({ name: r.next().v });
          } else if (t.kind === 'string' || t.kind === 'cartouche') {
            crit.push({ pattern: readTerms(ctx, [{ src: t.v }]).terms[0] });
          } else if (t.kind === 'ident' && (t.v === 'simp' || t.v === 'intro' || t.v === 'elim')) {
            if (r.isSym(':')) {
              r.next();
              const tt = r.next();
              crit.push({ pattern: readTerms(ctx, [{ src: tt.v }]).terms[0] });
            }
          }
        }
        const found: string[] = [];
        for (const [name, ths] of this.thy.thms) {
          for (const th of ths) {
            if (found.length >= 60) break;
            const ok = crit.every((cr) => {
              if (cr.name) return name.includes(cr.name);
              if (cr.pattern) return containsPattern(instThm(th), varsToSchematic(cr.pattern));
              return true;
            });
            if (ok) found.push(`${th.name}: ${printTerm(th.prop)}`);
          }
        }
        this.cur.messages.push({ severity: 'info', text: found.length ? `found ${found.length} theorem(s):\n` + found.join('\n') : 'found nothing' });
        return;
      }
    }
  }

  cmdTry(b: Block) {
    if (!b.goals.length) throw new CmdError('No subgoals!');
    const g = b.goals[0];
    const cands: string[] = ['simp', 'auto', 'blast', 'arith', 'force', 'fastforce', 'metis'];
    // induction candidates on free variables of datatype type
    const fv = [...frees(goalToTerm(g)).values()].filter((f) => this.thy.datatypeOf((f as { ty: Type }).ty));
    for (const f of fv) {
      const n = (f as { name: string }).name;
      const others = fv.filter((x) => (x as { name: string }).name !== n).map((x) => (x as { name: string }).name);
      cands.push(`(induction ${n}) auto`);
      if (others.length) cands.push(`(induction ${n} arbitrary: ${others.join(' ')}) auto`);
    }
    for (const c of cands) {
      const { toks } = tokenizeOuter(c);
      const cmd: Command = { kw: 'by', toks, from: 0, to: c.length };
      const rr = new TokReader(toks, cmd);
      try {
        const m1 = parseMethodTop(rr);
        const m2 = rr.atEnd() ? null : parseMethodTop(rr);
        const env = this.methodEnv(b);
        let st = evalMethod(env, m1, { goals: [g], facts: b.using });
        if (m2) st = evalMethod(env, m2, st);
        const rest = st.goals.filter((x) => !assumptionTac(x));
        if (rest.length === 0) {
          this.cur.messages.push({ severity: 'info', text: `Try this: by ${c.includes(' ') && !c.startsWith('(') ? '(' + c + ')' : c}` });
          return;
        }
      } catch {
        /* try next */
      }
    }
    this.cur.messages.push({ severity: 'warning', text: 'No proof found (tried simp, auto, blast, arith, force, fastforce, metis and induction)' });
  }

  stateString(): string | undefined {
    const b = this.top;
    if (!b) return undefined;
    const lines: string[] = [];
    if (b.mode === 'prove') {
      lines.push('proof (prove)');
      if (b.using.length) lines.push('using this:\n' + b.using.map((f) => '  ' + printTerm(f.prop)).join('\n') + '\n');
      lines.push(printGoals(b.goals));
    } else if (b.mode === 'state') {
      lines.push('proof (state)');
      if (b.thisFacts.length) lines.push('this:\n' + b.thisFacts.map((f) => '  ' + printTerm(f.prop)).join('\n') + '\n');
      lines.push(printGoals(b.goals));
    } else {
      lines.push('proof (chain)');
      lines.push('picking this:\n' + b.chained.map((f) => '  ' + printTerm(f.prop)).join('\n'));
    }
    return lines.join('\n');
  }
}

function varsToSchematic(t: Term): Term {
  // free variables in a find_theorems pattern act as wildcards
  switch (t.k) {
    case 'F':
      return mkV('_fp_' + t.name, t.ty);
    case 'A':
      return { k: 'A', f: varsToSchematic(t.f), a: varsToSchematic(t.a) };
    case 'L':
      return { k: 'L', x: t.x, ty: t.ty, body: varsToSchematic(t.body) };
    default:
      return t;
  }
}

function containsPattern(t: Term, pat: Term): boolean {
  if (unify(pat, t)) return true;
  if (t.k === 'A') return containsPattern(t.f, pat) || containsPattern(t.a, pat);
  if (t.k === 'L') return containsPattern(t.body, pat);
  return false;
}

export function checkTheory(src: string, opts: CheckOptions = {}): CheckResult {
  const base = opts.base ?? PRELUDE_THY ?? undefined;
  const ch = new Checker({ ...opts, base });
  const res = ch.run(src);
  if (opts.isPrelude) {
    (ch.thy as unknown as { __inductives?: Map<string, InductiveInfo> }).__inductives = ch.inductives;
    lastTheory = ch.thy;
  }
  return res;
}

export let lastTheory: Theory | null = null;

export { tvar, tcon, funTs, natT, mkNot, termKey, tunify, tsubst, mapTypes, readType, parseTerm, emptySubst, collectVarNames, closeByFact, goalFrees, mkConj };
