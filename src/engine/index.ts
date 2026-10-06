// Public API of the proof engine.
import { PRELUDE } from './prelude';
import { checkTheory, setPrelude, getPrelude, lastTheory, CheckResult, CheckOptions } from './check';
import { baseTheory } from './theory';

export type { CheckResult, CmdResult, Message, TheoremInfo } from './check';

let preludeErrors: CheckResult | null = null;

export function initPrelude(): CheckResult | null {
  if (!getPrelude()) {
    preludeErrors = checkTheory(PRELUDE, { isPrelude: true, base: baseTheory() });
    setPrelude(lastTheory!);
  }
  return preludeErrors;
}

export function check(src: string, opts: CheckOptions = {}): CheckResult {
  initPrelude();
  return checkTheory(src, opts);
}

export { PRELUDE };
