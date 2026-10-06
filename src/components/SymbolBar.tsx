'use client';
import { SYMBOL_BAR } from '@/engine/symbols';

export function SymbolBar({ onInsert, className = '' }: { onInsert: (s: string) => void; className?: string }) {
  return (
    <div
      className={`no-scrollbar flex gap-1 overflow-x-auto border-slate-200 bg-slate-50 px-2 py-1.5 dark:border-slate-800 dark:bg-slate-900 ${className}`}
      role="toolbar"
      aria-label="Insert symbol"
    >
      {SYMBOL_BAR.map((s) => (
        <button
          key={s.sym}
          type="button"
          title={s.title}
          aria-label={`Insert ${s.title}`}
          onPointerDown={(e) => e.preventDefault()}
          onMouseDown={(e) => e.preventDefault()}
          onClick={() => onInsert(s.sym === '[]' ? '[]' : s.sym)}
          className="min-w-[2.25rem] shrink-0 rounded-md border border-slate-200 bg-white px-2 py-1 font-mono text-base leading-6 text-slate-800 shadow-sm active:bg-brand-100 dark:border-slate-700 dark:bg-slate-800 dark:text-slate-100 dark:active:bg-brand-900"
        >
          {s.sym}
        </button>
      ))}
    </div>
  );
}
