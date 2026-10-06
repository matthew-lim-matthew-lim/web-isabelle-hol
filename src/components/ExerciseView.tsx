'use client';
import Link from 'next/link';
import { useRef, useState } from 'react';
import type { Exercise } from '@/content/exercises';
import { grade, Grade } from '@/content/grade';
import { Markdown } from './Markdown';
import { ProofWorkspace, WorkspaceHandle } from './ProofWorkspace';
import { DifficultyBadge } from './ExerciseList';
import { load, save, markSolved } from '@/lib/storage';
import type { CheckerState } from '@/lib/useChecker';

export function ExerciseView({ ex, next, prev }: { ex: Exercise; next: { id: string; title: string } | null; prev: { id: string; title: string } | null }) {
  const key = `isa-exercise-${ex.id}`;
  const [initial] = useState(() => load<string>(key, ex.starter));
  const [g, setG] = useState<Grade | null>(null);
  const [hints, setHints] = useState(0);
  const [confirmSol, setConfirmSol] = useState(false);
  const ws = useRef<WorkspaceHandle>(null);

  const onChecked = (s: CheckerState) => {
    if (!s.result) return;
    const r = grade(s.result, ex.required);
    setG(r);
    if (r.passed) markSolved('exercise', ex.id);
  };

  return (
    <main className="mx-auto max-w-7xl px-4 py-5">
      <div className="mb-3 flex items-center gap-3 text-sm">
        <Link href="/practice/" className="text-brand-700 hover:underline dark:text-brand-300">
          ← Exercises
        </Link>
        <span className="flex-1" />
        {prev && (
          <Link href={`/practice/${prev.id}/`} className="text-slate-500 hover:underline" title={prev.title}>
            ‹ Prev
          </Link>
        )}
        {next && (
          <Link href={`/practice/${next.id}/`} className="text-slate-500 hover:underline" title={next.title}>
            Next ›
          </Link>
        )}
      </div>
      <div className="grid gap-5 lg:grid-cols-[minmax(0,2fr)_minmax(0,3fr)]">
        <section>
          <h1 className="text-2xl font-bold">{ex.title}</h1>
          <div className="mt-2 flex items-center gap-2 text-sm text-slate-500">
            <DifficultyBadge d={ex.difficulty} /> {ex.topic}
          </div>
          <Markdown text={ex.description} className="mt-2" />
          <div
            className={`mt-4 rounded-lg border p-3 text-sm ${
              g?.passed
                ? 'border-emerald-300 bg-emerald-50 text-emerald-900 dark:border-emerald-800 dark:bg-emerald-950/40 dark:text-emerald-100'
                : 'border-slate-200 bg-slate-50 dark:border-slate-800 dark:bg-slate-900'
            }`}
            aria-live="polite"
          >
            {!g && 'Checking…'}
            {g?.passed && (
              <span>
                🎉 <strong>Solved!</strong> All proofs check.{' '}
                {next && (
                  <Link className="underline" href={`/practice/${next.id}/`}>
                    Next exercise: {next.title} →
                  </Link>
                )}
              </span>
            )}
            {g && !g.passed && (
              <>
                <div className="font-semibold">Not solved yet</div>
                <ul className="mt-1 list-disc pl-5">
                  {g.problems.map((p, i) => (
                    <li key={i}>{p}</li>
                  ))}
                </ul>
              </>
            )}
          </div>
          <div className="mt-4 flex flex-wrap gap-2">
            {hints < ex.hints.length && (
              <button className="rounded-md border border-slate-300 px-3 py-1.5 text-sm dark:border-slate-700" onClick={() => setHints((h) => h + 1)}>
                Show hint ({hints + 1}/{ex.hints.length})
              </button>
            )}
            <button
              className="rounded-md border border-slate-300 px-3 py-1.5 text-sm dark:border-slate-700"
              onClick={() => {
                ws.current?.setText(ex.starter);
                save(key, ex.starter);
              }}
            >
              Reset
            </button>
            {!confirmSol ? (
              <button className="rounded-md border border-slate-300 px-3 py-1.5 text-sm dark:border-slate-700" onClick={() => setConfirmSol(true)}>
                Show solution
              </button>
            ) : (
              <button
                className="rounded-md bg-amber-500 px-3 py-1.5 text-sm font-medium text-white"
                onClick={() => {
                  ws.current?.setText(ex.solution);
                  setConfirmSol(false);
                }}
              >
                Really replace my work with the solution?
              </button>
            )}
          </div>
          {hints > 0 && (
            <ul className="mt-3 space-y-2">
              {ex.hints.slice(0, hints).map((h, i) => (
                <li key={i} className="rounded-md bg-amber-50 p-2 text-sm dark:bg-amber-950/30">
                  <Markdown text={'💡 ' + h} />
                </li>
              ))}
            </ul>
          )}
        </section>
        <section className="min-w-0">
          <ProofWorkspace ref={ws} initial={initial} onTextChange={(t) => save(key, t)} onChecked={onChecked} editorMinHeight="16rem" />
        </section>
      </div>
    </main>
  );
}
