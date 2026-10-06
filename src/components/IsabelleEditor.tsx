'use client';
import { forwardRef, useEffect, useImperativeHandle, useRef } from 'react';
import { EditorState, Compartment, StateEffect, StateField, RangeSetBuilder, Extension } from '@codemirror/state';
import {
  EditorView,
  keymap,
  lineNumbers,
  highlightActiveLine,
  highlightActiveLineGutter,
  Decoration,
  DecorationSet,
  gutter,
  GutterMarker,
  drawSelection,
} from '@codemirror/view';
import { defaultKeymap, history, historyKeymap, indentWithTab } from '@codemirror/commands';
import { StreamLanguage, syntaxHighlighting, HighlightStyle, bracketMatching, indentUnit } from '@codemirror/language';
import { autocompletion, CompletionContext, completionKeymap } from '@codemirror/autocomplete';
import { searchKeymap, highlightSelectionMatches } from '@codemirror/search';
import { tags as t } from '@lezer/highlight';
import { COMPLETIONS } from '@/engine/symbols';
import type { CmdResult } from '@/engine/check';

// ---------------- language ----------------
const COMMAND_KW = new Set([
  'theory', 'imports', 'begin', 'end', 'datatype', 'fun', 'primrec', 'function', 'termination', 'definition', 'abbreviation',
  'type_synonym', 'axiomatization', 'consts', 'declare', 'lemmas', 'inductive', 'lemma', 'theorem', 'corollary', 'proposition',
  'apply', 'done', 'by', 'sorry', 'oops', 'proof', 'qed', 'next', 'fix', 'assume', 'presume', 'have', 'show', 'hence', 'thus',
  'then', 'from', 'with', 'using', 'unfolding', 'note', 'case', 'obtain', 'let', 'moreover', 'ultimately', 'also', 'finally',
  'defer', 'prefer', 'back', 'subgoal', 'value', 'term', 'typ', 'thm', 'find_theorems', 'quickcheck', 'nitpick', 'sledgehammer',
  'try', 'try0', 'text', 'txt', 'section', 'subsection', 'subsubsection', 'chapter', 'paragraph', 'prop',
]);
const MINOR_KW = new Set(['where', 'and', 'assumes', 'shows', 'fixes', 'for', 'if', 'obtains', 'is', 'in', 'arbitrary', 'rule', 'add', 'del', 'only', 'intro', 'elim', 'dest', 'split', 'simp', 'of', 'OF', 'THEN', 'symmetric']);
const METHODS = new Set([
  'auto', 'blast', 'force', 'fastforce', 'simp_all', 'induction', 'induct', 'cases', 'arith', 'linarith', 'presburger', 'metis',
  'assumption', 'rule', 'erule', 'drule', 'frule', 'intro', 'elim', 'clarify', 'clarsimp', 'safe', 'fast', 'best', 'iprover',
  'meson', 'smt', 'subst', 'unfold', 'insert', 'standard', 'contradiction', 'induct_tac', 'case_tac', 'rule_tac', 'eval', 'algebra',
]);

interface LState {
  comment: number;
  inString: '"' | null;
  cart: number;
}

const isabelleLang = StreamLanguage.define<LState>({
  startState: () => ({ comment: 0, inString: null, cart: 0 }),
  token(stream, st) {
    if (st.comment > 0) {
      while (!stream.eol()) {
        if (stream.match('(*')) st.comment++;
        else if (stream.match('*)')) {
          st.comment--;
          if (st.comment === 0) break;
        } else stream.next();
      }
      return 'comment';
    }
    if (st.inString) {
      while (!stream.eol()) {
        const ch = stream.next();
        if (ch === '\\') stream.next();
        else if (ch === '"') {
          st.inString = null;
          break;
        }
      }
      return 'string';
    }
    if (st.cart > 0) {
      while (!stream.eol()) {
        const ch = stream.next();
        if (ch === '‹') st.cart++;
        else if (ch === '›') {
          st.cart--;
          if (st.cart === 0) break;
        }
      }
      return 'string';
    }
    if (stream.eatSpace()) return null;
    if (stream.match('(*')) {
      st.comment = 1;
      return 'comment';
    }
    const ch = stream.peek();
    if (ch === '"') {
      stream.next();
      st.inString = '"';
      return 'string';
    }
    if (ch === '‹') {
      stream.next();
      st.cart = 1;
      return 'string';
    }
    if (stream.match(/^[0-9]+/)) return 'number';
    if (stream.match(/^'[A-Za-z][A-Za-z0-9_']*/)) return 'typeName';
    if (stream.match(/^\?[A-Za-z][A-Za-z0-9_']*/)) return 'variableName.special';
    const m = stream.match(/^[A-Za-z][A-Za-z0-9_'.]*/) as RegExpMatchArray | null;
    if (m) {
      const w = m[0];
      if (COMMAND_KW.has(w)) return 'keyword';
      if (MINOR_KW.has(w)) return 'modifier';
      if (METHODS.has(w)) return 'atom';
      return 'variableName';
    }
    stream.next();
    return 'operator';
  },
  languageData: { commentTokens: { block: { open: '(*', close: '*)' } } },
});

const lightHL = HighlightStyle.define([
  { tag: t.keyword, color: '#0b5394', fontWeight: '600' },
  { tag: t.modifier, color: '#7c3aed' },
  { tag: t.string, color: '#166534' },
  { tag: t.comment, color: '#94a3b8', fontStyle: 'italic' },
  { tag: t.number, color: '#b45309' },
  { tag: t.typeName, color: '#a21caf' },
  { tag: t.special(t.variableName), color: '#a21caf' },
  { tag: t.atom, color: '#0369a1' },
  { tag: t.function(t.variableName), color: '#0369a1' },
  { tag: t.operator, color: '#475569' },
]);
const darkHL = HighlightStyle.define([
  { tag: t.keyword, color: '#7cb7ff', fontWeight: '600' },
  { tag: t.modifier, color: '#c4b5fd' },
  { tag: t.string, color: '#86efac' },
  { tag: t.comment, color: '#64748b', fontStyle: 'italic' },
  { tag: t.number, color: '#fbbf24' },
  { tag: t.typeName, color: '#f0abfc' },
  { tag: t.special(t.variableName), color: '#f0abfc' },
  { tag: t.atom, color: '#7dd3fc' },
  { tag: t.function(t.variableName), color: '#7dd3fc' },
  { tag: t.operator, color: '#cbd5e1' },
]);

const lightTheme = EditorView.theme(
  {
    '&': { backgroundColor: '#ffffff', color: '#0f172a' },
    '.cm-gutters': { backgroundColor: '#f8fafc', color: '#94a3b8', border: 'none' },
    '.cm-activeLine': { backgroundColor: 'rgba(52,121,252,0.05)' },
    '.cm-activeLineGutter': { backgroundColor: 'rgba(52,121,252,0.08)' },
    '.cm-cursor': { borderLeftColor: '#1e5af1', borderLeftWidth: '2px' },
    '&.cm-focused .cm-selectionBackground, .cm-selectionBackground': { backgroundColor: 'rgba(52,121,252,0.2) !important' },
  },
  { dark: false },
);
const darkTheme = EditorView.theme(
  {
    '&': { backgroundColor: '#0b1220', color: '#e2e8f0' },
    '.cm-gutters': { backgroundColor: '#0b1220', color: '#475569', border: 'none' },
    '.cm-activeLine': { backgroundColor: 'rgba(148,163,184,0.06)' },
    '.cm-activeLineGutter': { backgroundColor: 'rgba(148,163,184,0.1)' },
    '.cm-cursor': { borderLeftColor: '#7cb7ff', borderLeftWidth: '2px' },
    '&.cm-focused .cm-selectionBackground, .cm-selectionBackground': { backgroundColor: 'rgba(89,159,255,0.3) !important' },
    '.cm-tooltip': { backgroundColor: '#0f172a', color: '#e2e8f0', border: '1px solid #334155' },
    '.cm-tooltip-autocomplete > ul > li[aria-selected]': { backgroundColor: '#1e3a8a', color: '#fff' },
  },
  { dark: true },
);

// ---------------- abbreviations ----------------
const ABBREVS: [string, string][] = [
  ['==>', '⟹'],
  ['-->', '⟶'],
  ['<-->', '⟷'],
  ['<->', '⟷'],
  ['=>', '⇒'],
  ['!!', '⋀'],
  ['/\\', '∧'],
  ['\\/', '∨'],
  ['~=', '≠'],
  ['<=', '≤'],
  ['>=', '≥'],
  ['[|', '⟦'],
  ['|]', '⟧'],
  ['<<', '‹'],
  ['>>', '›'],
  ['%', 'λ'],
];

function abbrevHandler(enabled: () => boolean) {
  return EditorView.inputHandler.of((view, from, to, text) => {
    if (!enabled() || text.length !== 1 || from !== to) return false;
    const before = view.state.doc.sliceString(Math.max(0, from - 4), from) + text;
    let best: [string, string] | null = null;
    for (const a of ABBREVS) if (before.endsWith(a[0]) && (!best || a[0].length > best[0].length)) best = a;
    if (!best) return false;
    // do not convert "<-" prefixes, "=" inside "==>" in progress etc. (handled by longest match)
    const start = from - (best[0].length - 1);
    if (start < 0) return false;
    view.dispatch({ changes: { from: start, to, insert: best[1] }, selection: { anchor: start + best[1].length }, userEvent: 'input.type' });
    return true;
  });
}

function symbolCompletions(ctx: CompletionContext) {
  const word = ctx.matchBefore(/\\[A-Za-z<]*/);
  if (!word || (word.from === word.to && !ctx.explicit)) return null;
  return {
    from: word.from,
    options: COMPLETIONS.map((c) => ({ label: c.label, detail: c.sym, apply: c.sym, type: 'text' })),
    validFor: /^\\[A-Za-z<]*$/,
  };
}

// ---------------- diagnostics ----------------
export interface Diag {
  from: number;
  to: number;
  severity: 'error' | 'warning';
}
const setDiags = StateEffect.define<Diag[]>();

class GMarker extends GutterMarker {
  constructor(public cls: string) {
    super();
  }
  toDOM() {
    const d = document.createElement('div');
    d.className = this.cls;
    return d;
  }
  eq(o: GMarker) {
    return o.cls === this.cls;
  }
}
const errMarker = new GMarker('isa-gutter-error');
const warnMarker = new GMarker('isa-gutter-warning');

const diagField = StateField.define<{ deco: DecorationSet; diags: Diag[] }>({
  create: () => ({ deco: Decoration.none, diags: [] }),
  update(value, tr) {
    let { deco, diags } = value;
    if (tr.docChanged) {
      deco = deco.map(tr.changes);
      diags = diags
        .map((d) => ({ ...d, from: tr.changes.mapPos(d.from), to: tr.changes.mapPos(d.to) }))
        .filter((d) => d.to > d.from);
    }
    for (const e of tr.effects) {
      if (e.is(setDiags)) {
        diags = e.value;
        const len = tr.state.doc.length;
        const sorted = [...diags].filter((d) => d.from < len).sort((a, b) => a.from - b.from || a.to - b.to);
        const b = new RangeSetBuilder<Decoration>();
        for (const d of sorted) {
          const to = Math.min(d.to, len);
          if (to <= d.from) continue;
          b.add(d.from, to, Decoration.mark({ class: d.severity === 'error' ? 'cm-isa-error' : 'cm-isa-warning' }));
        }
        deco = b.finish();
      }
    }
    return { deco, diags };
  },
  provide: (f) => EditorView.decorations.from(f, (v) => v.deco),
});

const diagGutter = gutter({
  class: 'cm-gutter-isa',
  lineMarker(view, line) {
    const { diags } = view.state.field(diagField);
    let sev: 'error' | 'warning' | null = null;
    for (const d of diags) {
      if (d.from <= line.to && d.to >= line.from) {
        const first = view.state.doc.lineAt(Math.min(d.from, view.state.doc.length));
        if (first.from !== line.from) continue;
        if (d.severity === 'error') sev = 'error';
        else if (!sev) sev = 'warning';
      }
    }
    return sev === 'error' ? errMarker : sev === 'warning' ? warnMarker : null;
  },
  lineMarkerChange: (u) => u.transactions.some((tr) => tr.effects.some((e) => e.is(setDiags))),
});

export function diagsFromCommands(cmds: CmdResult[]): Diag[] {
  const out: Diag[] = [];
  for (const c of cmds) {
    if (c.status === 'error') out.push({ from: c.from, to: c.to, severity: 'error' });
    else if (c.status === 'warning') out.push({ from: c.from, to: c.to, severity: 'warning' });
  }
  return out;
}

// ---------------- component ----------------
export interface EditorHandle {
  insert(text: string): void;
  setText(text: string): void;
  getText(): string;
  focus(): void;
  setDiagnostics(d: Diag[]): void;
  jumpTo(pos: number): void;
}

interface Props {
  value: string;
  onChange?: (text: string) => void;
  onCursor?: (pos: number) => void;
  readOnly?: boolean;
  minHeight?: string;
  autoFocus?: boolean;
  className?: string;
}

function isDark() {
  return typeof document !== 'undefined' && document.documentElement.classList.contains('dark');
}

export const IsabelleEditor = forwardRef<EditorHandle, Props>(function IsabelleEditor(props, ref) {
  const host = useRef<HTMLDivElement>(null);
  const view = useRef<EditorView | null>(null);
  const themeComp = useRef(new Compartment());
  const cbs = useRef(props);
  cbs.current = props;

  useEffect(() => {
    if (!host.current) return;
    const themeExt = (): Extension => (isDark() ? [darkTheme, syntaxHighlighting(darkHL)] : [lightTheme, syntaxHighlighting(lightHL)]);
    const state = EditorState.create({
      doc: props.value,
      extensions: [
        lineNumbers(),
        highlightActiveLineGutter(),
        diagGutter,
        history(),
        drawSelection(),
        highlightActiveLine(),
        highlightSelectionMatches(),
        bracketMatching(),
        indentUnit.of('  '),
        EditorView.lineWrapping,
        isabelleLang,
        themeComp.current.of(themeExt()),
        diagField,
        autocompletion({ override: [symbolCompletions], icons: false }),
        abbrevHandler(() => !cbs.current.readOnly),
        keymap.of([...completionKeymap, ...defaultKeymap, ...historyKeymap, ...searchKeymap, indentWithTab]),
        EditorState.readOnly.of(!!props.readOnly),
        EditorView.contentAttributes.of({ autocapitalize: 'off', autocorrect: 'off', spellcheck: 'false', 'aria-label': 'Isabelle theory editor' }),
        EditorView.updateListener.of((u) => {
          if (u.docChanged) cbs.current.onChange?.(u.state.doc.toString());
          if (u.selectionSet || u.docChanged) cbs.current.onCursor?.(u.state.selection.main.head);
        }),
        EditorView.theme({ '&': { minHeight: props.minHeight ?? '100%' }, '.cm-scroller': { minHeight: props.minHeight ?? '100%' } }),
      ],
    });
    const v = new EditorView({ state, parent: host.current });
    view.current = v;
    if (props.autoFocus) v.focus();
    const onTheme = () => v.dispatch({ effects: themeComp.current.reconfigure(themeExt()) });
    window.addEventListener('isa-theme', onTheme);
    return () => {
      window.removeEventListener('isa-theme', onTheme);
      v.destroy();
      view.current = null;
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  useImperativeHandle(ref, () => ({
    insert(text: string) {
      const v = view.current;
      if (!v) return;
      const { from, to } = v.state.selection.main;
      v.dispatch({ changes: { from, to, insert: text }, selection: { anchor: from + text.length }, userEvent: 'input' });
      v.focus();
    },
    setText(text: string) {
      const v = view.current;
      if (!v) return;
      v.dispatch({ changes: { from: 0, to: v.state.doc.length, insert: text } });
    },
    getText() {
      return view.current?.state.doc.toString() ?? '';
    },
    focus() {
      view.current?.focus();
    },
    setDiagnostics(d: Diag[]) {
      view.current?.dispatch({ effects: setDiags.of(d) });
    },
    jumpTo(pos: number) {
      const v = view.current;
      if (!v) return;
      const p = Math.min(pos, v.state.doc.length);
      v.dispatch({ selection: { anchor: p }, scrollIntoView: true });
      v.focus();
    },
  }));

  return <div ref={host} className={props.className ?? 'h-full'} />;
});
