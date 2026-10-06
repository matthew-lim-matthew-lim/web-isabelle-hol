import { describe, it, expect } from 'vitest';
import { check } from '../src/engine/index';
import { EXERCISES } from '../src/content/exercises';
import { LESSONS } from '../src/content/lessons';

// Simulate typing: every prefix of the solutions (at many cut points) must check without internal errors.
const sources = [...EXERCISES.map((e) => e.solution), ...LESSONS.flatMap((l) => l.blocks.flatMap((b) => (b.t === 'code' ? [b.code] : b.t === 'task' ? [b.solution] : [])))];

describe('robustness while typing', () => {
  it('no internal errors on prefixes / mutations', () => {
    const problems: string[] = [];
    let n = 0;
    for (const src of sources) {
      const cuts = 25;
      for (let k = 1; k <= cuts; k++) {
        const pos = Math.floor((src.length * k) / cuts);
        const variants = [src.slice(0, pos), src.slice(0, pos) + src.slice(pos + 3), src.slice(0, pos) + '"' + src.slice(pos)];
        for (const v of variants) {
          n++;
          const t0 = Date.now();
          const r = check(v);
          const ms = Date.now() - t0;
          for (const c of r.commands) for (const m of c.messages) if (m.text.startsWith('Internal error')) problems.push(`${m.text} :: ${v.slice(Math.max(0, c.from - 40), c.to + 20)}`);
          if (ms > 3000) problems.push(`slow (${ms}ms): ${v.slice(-80)}`);
        }
      }
    }
    expect(problems.slice(0, 10)).toEqual([]);
    expect(n).toBeGreaterThan(1000);
  }, 600000);
});
