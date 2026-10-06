import { describe, it, expect } from 'vitest';
import { readFileSync, readdirSync } from 'node:fs';
import path from 'node:path';
import { check, initPrelude } from '../src/engine/index';

const dir = path.join(__dirname, 'thy');

describe('prelude', () => {
  it('loads without errors', () => {
    const r = initPrelude();
    const errs = r ? r.commands.filter((c) => c.status === 'error') : [];
    expect(errs.map((e) => e.messages.map((m) => m.text).join(' '))).toEqual([]);
  });
});

function fmtErrors(src: string, r: ReturnType<typeof check>) {
  return r.commands
    .filter((c) => c.status === 'error')
    .map((c) => `L${src.slice(0, c.from).split('\n').length}: ${src.slice(c.from, c.to).split('\n')[0]} -- ${c.messages.map((m) => m.text).join(' | ')}`);
}

describe('positive theories check without errors', () => {
  for (const f of readdirSync(dir).filter((f) => f.endsWith('.thy') && !f.startsWith('negative'))) {
    it(f, () => {
      const src = readFileSync(path.join(dir, f), 'utf8');
      const r = check(src);
      expect(fmtErrors(src, r)).toEqual([]);
    });
  }
});

describe('soundness: false claims are rejected', () => {
  const src = readFileSync(path.join(dir, 'negative.thy'), 'utf8');
  const r = check(src);
  const lemmas = src.split('\n').filter((l) => l.startsWith('lemma'));
  it('every lemma fails', () => {
    const errLines = new Set(r.commands.filter((c) => c.status === 'error').map((c) => src.slice(0, c.from).split('\n').length));
    const lines = src.split('\n');
    const missing: string[] = [];
    lines.forEach((l, i) => {
      if (l.startsWith('lemma') && !errLines.has(i + 1)) missing.push(l);
    });
    expect(missing).toEqual([]);
    expect(lemmas.length).toBeGreaterThan(10);
  });
});
