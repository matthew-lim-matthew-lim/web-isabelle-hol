import { describe, it, expect } from 'vitest';
import { check } from '../src/engine/index';
import { EXERCISES } from '../src/content/exercises';
import { grade } from '../src/content/grade';

function errs(src: string, r: ReturnType<typeof check>) {
  return r.commands
    .filter((c) => c.status === 'error')
    .map((c) => `L${src.slice(0, c.from).split('\n').length}: ${src.slice(c.from, c.to).split('\n')[0]} -- ${c.messages.map((m) => m.text).join(' | ')}`);
}

describe('exercises', () => {
  const ids = new Set<string>();
  for (const ex of EXERCISES) {
    it(`${ex.id}: unique id`, () => {
      expect(ids.has(ex.id)).toBe(false);
      ids.add(ex.id);
    });
    it(`${ex.id}: solution passes`, () => {
      const r = check(ex.solution);
      expect(errs(ex.solution, r)).toEqual([]);
      expect(grade(r, ex.required).problems).toEqual([]);
    });
    it(`${ex.id}: starter is well-formed but unsolved`, () => {
      const r = check(ex.starter);
      expect(errs(ex.starter, r)).toEqual([]);
      expect(grade(r, ex.required).passed).toBe(false);
    });
  }
});
