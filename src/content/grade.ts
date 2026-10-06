import type { CheckResult } from '../engine/check';

export interface Grade {
  passed: boolean;
  problems: string[];
}

/** An exercise is solved when the theory has no errors, no sorry/oops, and all required lemmas are proved. */
export function grade(r: CheckResult, required: string[]): Grade {
  const problems: string[] = [];
  if (r.errors > 0) problems.push(`${r.errors} error${r.errors === 1 ? '' : 's'} in the theory`);
  const sorries = r.commands.filter((c) => c.kw === 'sorry' || c.kw === 'oops').length;
  if (sorries > 0) problems.push(`${sorries} proof${sorries === 1 ? '' : 's'} still use${sorries === 1 ? 's' : ''} sorry/oops`);
  for (const name of required) {
    const th = r.theorems.find((t) => t.name === name);
    if (!th) problems.push(`lemma "${name}" is missing`);
    else if (th.error) problems.push(`lemma "${name}" has a failing proof`);
    else if (th.sorry) problems.push(`lemma "${name}" is not proved yet (sorry)`);
  }
  if (!r.ended) problems.push('the theory is not closed with "end"');
  return { passed: problems.length === 0, problems };
}
