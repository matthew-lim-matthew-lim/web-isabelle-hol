import { EXERCISES } from '../src/content/exercises';
import { writeFileSync } from 'node:fs';
const ex = EXERCISES.find((e) => e.id === process.argv[2])!;
writeFileSync(process.argv[3], process.argv[4] === 'starter' ? ex.starter : ex.solution);
