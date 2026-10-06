// Dev helper: check a .thy file (or stdin text) and print results.
import { readFileSync } from 'node:fs';
import { check, initPrelude } from '../src/engine/index';

const t0 = Date.now();
const pre = initPrelude();
const t1 = Date.now();
if (pre) {
  const errs = pre.commands.filter((c) => c.status === 'error');
  console.log(`prelude: ${t1 - t0}ms, ${errs.length} errors`);
  for (const e of errs.slice(0, 20)) console.log('  PRELUDE ERROR', e.from, e.kw, e.messages.map((m) => m.text).join(' | '));
}
const src = readFileSync(process.argv[2], 'utf8');
const r = check(src);
const verbose = process.argv.includes('-v');
for (const c of r.commands) {
  const line = src.slice(0, c.from).split('\n').length;
  const text = src.slice(c.from, c.to).split('\n')[0].slice(0, 70);
  if (c.status !== 'ok' || verbose) {
    console.log(`L${line} [${c.status}] ${text}`);
    for (const m of c.messages) console.log(`   ${m.severity}: ${m.text.replace(/\n/g, '\n      ')}`);
    if (verbose && c.state) console.log('   STATE: ' + c.state.replace(/\n/g, '\n      '));
  }
}
console.log(`errors=${r.errors} sorries=${r.sorries} time=${Date.now() - t1}ms`);
