'use client';
import type { CheckResult, CmdResult } from '@/engine/check';

export function commandAt(result: CheckResult | null, pos: number): CmdResult | null {
  if (!result) return null;
  let best: CmdResult | null = null;
  for (const c of result.commands) {
    if (c.kw === 'error' && !(c.from <= pos && pos <= c.to)) continue;
    if (c.from <= pos) {
      if (!best || c.from >= best.from) best = c;
    }
  }
  return best;
}

export function StatusChip({ result, checking, error }: { result: CheckResult | null; checking: boolean; error: string | null }) {
  let cls = 'bg-slate-100 text-slate-700 dark:bg-slate-800 dark:text-slate-200';
  let text = 'Checking…';
  if (error) {
    cls = 'bg-red-100 text-red-800 dark:bg-red-900/50 dark:text-red-200';
    text = 'Checker error';
  } else if (result && !checking) {
    const sorries = result.commands.filter((c) => c.kw === 'sorry' || c.kw === 'oops').length;
    if (result.errors > 0) {
      cls = 'bg-red-100 text-red-800 dark:bg-red-900/50 dark:text-red-200';
      text = `${result.errors} error${result.errors > 1 ? 's' : ''}`;
    } else if (sorries > 0) {
      cls = 'bg-amber-100 text-amber-800 dark:bg-amber-900/40 dark:text-amber-200';
      text = `OK · ${sorries} sorry`;
    } else {
      cls = 'bg-emerald-100 text-emerald-800 dark:bg-emerald-900/40 dark:text-emerald-200';
      text = 'All checked ✓';
    }
  }
  return (
    <span className={`inline-flex items-center gap-1.5 rounded-full px-2.5 py-0.5 text-xs font-medium ${cls}`} aria-live="polite">
      {checking && <span className="h-2 w-2 animate-pulse rounded-full bg-current" />}
      {text}
    </span>
  );
}

const sevCls: Record<string, string> = {
  error: 'border-red-300 bg-red-50 text-red-900 dark:border-red-800 dark:bg-red-950/50 dark:text-red-100',
  warning: 'border-amber-300 bg-amber-50 text-amber-900 dark:border-amber-800 dark:bg-amber-950/40 dark:text-amber-100',
  info: 'border-slate-200 bg-slate-50 text-slate-800 dark:border-slate-700 dark:bg-slate-900 dark:text-slate-100',
};

interface Props {
  result: CheckResult | null;
  checking: boolean;
  error: string | null;
  cursor: number;
  source: string;
  onJump?: (pos: number) => void;
  className?: string;
  headerExtra?: React.ReactNode;
}

export function OutputPanel({ result, checking, error, cursor, source, onJump, className = '', headerExtra }: Props) {
  const cmd = commandAt(result, cursor);
  const problems = result ? result.commands.filter((c) => c.status === 'error') : [];
  const lineOf = (pos: number) => source.slice(0, pos).split('\n').length;
  return (
    <div className={`flex min-h-0 flex-col ${className}`}>
      <div className="flex items-center gap-2 border-b border-slate-200 px-3 py-2 dark:border-slate-800">
        <span className="text-sm font-semibold">Output</span>
        <StatusChip result={result} checking={checking} error={error} />
        {cmd && (
          <span className="ml-auto truncate text-xs text-slate-500 dark:text-slate-400">
            line {lineOf(cmd.from)} · <code className="font-mono">{cmd.kw}</code>
          </span>
        )}
        {headerExtra}
      </div>
      <div className="min-h-0 flex-1 overflow-auto p-3 text-sm">
        {error && <div className={`mb-2 rounded-md border p-2 ${sevCls.error}`}>{error}</div>}
        {!cmd && !error && <p className="text-slate-500 dark:text-slate-400">Place the cursor on a command to see its output and the proof state.</p>}
        {cmd &&
          cmd.messages.map((m, i) => (
            <pre key={i} className={`mb-2 whitespace-pre-wrap break-words rounded-md border p-2 font-mono text-[13px] ${sevCls[m.severity]}`}>
              {m.text}
            </pre>
          ))}
        {cmd?.state && (
          <pre className="whitespace-pre-wrap break-words font-mono text-[13px] leading-relaxed text-slate-800 dark:text-slate-100">{cmd.state}</pre>
        )}
        {problems.length > 0 && cmd?.status !== 'error' && (
          <div className="mt-4 border-t border-slate-200 pt-3 dark:border-slate-800">
            <div className="mb-1 text-xs font-semibold uppercase tracking-wide text-slate-500">Errors in theory</div>
            <ul className="space-y-1">
              {problems.slice(0, 20).map((p, i) => (
                <li key={i}>
                  <button className="text-left text-xs text-red-700 hover:underline dark:text-red-300" onClick={() => onJump?.(p.from)}>
                    line {lineOf(p.from)}: {p.messages.find((m) => m.severity === 'error')?.text.split('\n')[0] ?? 'error'}
                  </button>
                </li>
              ))}
            </ul>
          </div>
        )}
      </div>
    </div>
  );
}
