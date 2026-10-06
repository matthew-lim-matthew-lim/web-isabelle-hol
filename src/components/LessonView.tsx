'use client';
import Link from 'next/link';
import { useRef, useState } from 'react';
import type { Lesson, LessonBlock } from '@/content/lessons';
import { Markdown } from './Markdown';
import { ProofWorkspace, WorkspaceHandle } from './ProofWorkspace';
import { grade } from '@/content/grade';
import { load, save, markSolved } from '@/lib/storage';
import type { CheckerState } from '@/lib/useChecker';

function CodeExample({ block }: { block: Extract<LessonBlock, { t: 'code' }> }) {
  const [open, setOpen] = useState(false);
  return (
    <div className="my-5">
      {block.note && <p className="mb-2 text-sm text-slate-600 dark:text-slate-400">💡 {block.note}</p>}
      {open ? (
        <ProofWorkspace initial={block.code} />
      ) : (
        <div className="overflow-hidden rounded-xl border border-slate-200 dark:border-slate-800">
          <pre className="overflow-x-auto bg-slate-50 p-3 font-mono text-[13px] leading-relaxed dark:bg-slate-900">{block.code}</pre>
          <button
            onClick={() => setOpen(true)}
            className="w-full border-t border-slate-200 bg-white px-3 py-2 text-left text-sm font-semibold text-brand-700 hover:bg-brand-50 dark:border-slate-800 dark:bg-slate-950 dark:text-brand-300 dark:hover:bg-slate-900"
          >
            ▶ Run &amp; edit this example
          </button>
        </div>
      )}
    </div>
  );
}

function Task({ block, lessonSlug, idx }: { block: Extract<LessonBlock, { t: 'task' }>; lessonSlug: string; idx: number }) {
  const key = `isa-lesson-${lessonSlug}-${idx}`;
  const [initial] = useState(() => load<string>(key, block.starter));
  const [status, setStatus] = useState<{ passed: boolean; problems: string[] } | null>(null);
  const [hints, setHints] = useState(0);
  const ws = useRef<WorkspaceHandle>(null);
  const onChecked = (s: CheckerState) => {
    if (!s.result) return;
    const g = grade(s.result, block.required, { requireEnd: false });
    setStatus(g);
    if (g.passed) markSolved('lesson', lessonSlug);
  };
  return (
    <section className="my-8 rounded-xl border-2 border-brand-200 bg-brand-50/40 p-3 dark:border-brand-900 dark:bg-brand-950/20 sm:p-4">
      <h3 className="mb-1 flex items-center gap-2 font-semibold">
        <span className="rounded bg-brand-600 px-2 py-0.5 text-xs uppercase tracking-wide text-white">Try it</span>
        Your turn
      </h3>
      <Markdown text={block.prompt} className="text-[15px]" />
      <ProofWorkspace ref={ws} initial={initial} onTextChange={(t) => save(key, t)} onChecked={onChecked} />
      <div className="mt-3 flex flex-wrap items-center gap-2">
        {status && (
          <span
            className={`rounded-md px-2.5 py-1 text-sm font-medium ${
              status.passed
                ? 'bg-emerald-100 text-emerald-800 dark:bg-emerald-900/40 dark:text-emerald-200'
                : 'bg-slate-100 text-slate-700 dark:bg-slate-800 dark:text-slate-200'
            }`}
          >
            {status.passed ? '🎉 Solved!' : `Not yet: ${status.problems[0]}`}
          </span>
        )}
        <span className="flex-1" />
        {hints < block.hints.length && (
          <button className="rounded-md border border-slate-300 px-3 py-1.5 text-sm dark:border-slate-700" onClick={() => setHints((h) => h + 1)}>
            Hint ({hints + 1}/{block.hints.length})
          </button>
        )}
        <button className="rounded-md border border-slate-300 px-3 py-1.5 text-sm dark:border-slate-700" onClick={() => ws.current?.setText(block.starter)}>
          Reset
        </button>
        <button className="rounded-md border border-slate-300 px-3 py-1.5 text-sm dark:border-slate-700" onClick={() => ws.current?.setText(block.solution)}>
          Show solution
        </button>
      </div>
      {hints > 0 && (
        <ul className="mt-3 space-y-1">
          {block.hints.slice(0, hints).map((h, i) => (
            <li key={i} className="rounded-md bg-amber-50 p-2 text-sm dark:bg-amber-950/30">
              <Markdown text={'💡 ' + h} />
            </li>
          ))}
        </ul>
      )}
    </section>
  );
}

export function LessonView({ lesson, prev, next }: { lesson: Lesson; prev: { slug: string; title: string } | null; next: { slug: string; title: string } | null }) {
  return (
    <main className="mx-auto max-w-3xl px-4 py-6 sm:py-8">
      <Link href="/learn/" className="text-sm text-brand-700 hover:underline dark:text-brand-300">
        ← All lessons
      </Link>
      <h1 className="mt-2 text-2xl font-bold sm:text-3xl">{lesson.title}</h1>
      <p className="mt-1 text-slate-600 dark:text-slate-400">{lesson.summary}</p>
      <div className="mt-4">
        {lesson.blocks.map((b, i) =>
          b.t === 'md' ? <Markdown key={i} text={b.text} /> : b.t === 'code' ? <CodeExample key={i} block={b} /> : <Task key={i} block={b} lessonSlug={lesson.slug} idx={i} />,
        )}
      </div>
      <nav className="mt-10 flex flex-col gap-3 border-t border-slate-200 pt-6 dark:border-slate-800 sm:flex-row sm:justify-between">
        {prev ? (
          <Link href={`/learn/${prev.slug}/`} className="rounded-lg border border-slate-200 px-4 py-3 text-sm hover:border-brand-400 dark:border-slate-800">
            ← {prev.title}
          </Link>
        ) : (
          <span />
        )}
        {next ? (
          <Link href={`/learn/${next.slug}/`} className="rounded-lg border border-slate-200 px-4 py-3 text-right text-sm hover:border-brand-400 dark:border-slate-800">
            {next.title} →
          </Link>
        ) : (
          <Link href="/practice/" className="rounded-lg bg-brand-600 px-4 py-3 text-right text-sm font-semibold text-white">
            Continue with practice exercises →
          </Link>
        )}
      </nav>
    </main>
  );
}
