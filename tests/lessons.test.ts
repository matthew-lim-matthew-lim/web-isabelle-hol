import { describe, it, expect } from 'vitest';
import { check } from '../src/engine/index';
import { LESSONS } from '../src/content/lessons';
import { grade } from '../src/content/grade';

function errs(src: string, r: ReturnType<typeof check>) {
  return r.commands
    .filter((c) => c.status === 'error')
    .map((c) => `L${src.slice(0, c.from).split('\n').length}: ${src.slice(c.from, c.to).split('\n')[0]} -- ${c.messages.map((m) => m.text).join(' | ')}`);
}

describe('lessons', () => {
  for (const l of LESSONS) {
    l.blocks.forEach((b, i) => {
      if (b.t === 'code')
        it(`${l.slug} code #${i}`, () => {
          expect(errs(b.code, check(b.code))).toEqual([]);
        });
      if (b.t === 'task') {
        it(`${l.slug} task #${i} solution`, () => {
          const r = check(b.solution);
          expect(errs(b.solution, r)).toEqual([]);
          expect(grade(r, b.required, { requireEnd: false }).problems).toEqual([]);
        });
        it(`${l.slug} task #${i} starter unsolved`, () => {
          const r = check(b.starter);
          expect(grade(r, b.required, { requireEnd: false }).passed).toBe(false);
        });
      }
    });
  }
});
