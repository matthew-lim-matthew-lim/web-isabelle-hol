'use client';
import Link from 'next/link';
import { useEffect, useMemo, useState } from 'react';
import { getProgress, Progress } from '@/lib/storage';

type Ex = { id: string; title: string; difficulty: 'easy' | 'medium' | 'hard'; topic: string };

const DIFF_CLS: Record<string, string> = {
  easy: 'bg-emerald-100 text-emerald-800 dark:bg-emerald-900/40 dark:text-emerald-200',
  medium: 'bg-amber-100 text-amber-800 dark:bg-amber-900/40 dark:text-amber-200',
  hard: 'bg-rose-100 text-rose-800 dark:bg-rose-900/40 dark:text-rose-200',
};

export function DifficultyBadge({ d }: { d: string }) {
  return <span className={`rounded-full px-2 py-0.5 text-xs font-medium capitalize ${DIFF_CLS[d]}`}>{d}</span>;
}

export function ExerciseList({ exercises, topics }: { exercises: Ex[]; topics: string[] }) {
  const [topic, setTopic] = useState<string>('All');
  const [diff, setDiff] = useState<string>('All');
  const [prog, setProg] = useState<Progress>({});
  useEffect(() => setProg(getProgress('exercise')), []);
  const shown = useMemo(() => exercises.filter((e) => (topic === 'All' || e.topic === topic) && (diff === 'All' || e.difficulty === diff)), [exercises, topic, diff]);
  const solved = exercises.filter((e) => prog[e.id]?.solved).length;
  const chip = (active: boolean) =>
    `whitespace-nowrap rounded-full border px-3 py-1 text-sm ${
      active ? 'border-brand-600 bg-brand-600 text-white' : 'border-slate-300 hover:bg-slate-50 dark:border-slate-700 dark:hover:bg-slate-900'
    }`;
  return (
    <div className="mt-6">
      <div className="mb-2 flex items-center gap-3">
        <div className="h-2 flex-1 overflow-hidden rounded-full bg-slate-200 dark:bg-slate-800">
          <div className="h-full bg-emerald-500 transition-all" style={{ width: `${(solved / exercises.length) * 100}%` }} />
        </div>
        <span className="text-sm text-slate-600 dark:text-slate-400">
          {solved}/{exercises.length} solved
        </span>
      </div>
      <div className="no-scrollbar -mx-4 flex gap-2 overflow-x-auto px-4 py-2">
        {['All', ...topics].map((t) => (
          <button key={t} className={chip(topic === t)} onClick={() => setTopic(t)}>
            {t}
          </button>
        ))}
      </div>
      <div className="no-scrollbar -mx-4 flex gap-2 overflow-x-auto px-4 pb-2">
        {['All', 'easy', 'medium', 'hard'].map((d) => (
          <button key={d} className={chip(diff === d) + ' capitalize'} onClick={() => setDiff(d)}>
            {d}
          </button>
        ))}
      </div>
      <ul className="mt-3 grid gap-3 sm:grid-cols-2">
        {shown.map((e) => (
          <li key={e.id}>
            <Link
              href={`/practice/${e.id}/`}
              className="flex h-full items-start gap-3 rounded-xl border border-slate-200 p-4 transition hover:border-brand-400 hover:shadow-sm dark:border-slate-800 dark:hover:border-brand-600"
            >
              <span
                className={`mt-0.5 grid h-6 w-6 shrink-0 place-items-center rounded-full text-xs font-bold ${
                  prog[e.id]?.solved ? 'bg-emerald-500 text-white' : 'bg-slate-200 text-slate-500 dark:bg-slate-800'
                }`}
              >
                {prog[e.id]?.solved ? '✓' : ''}
              </span>
              <span className="min-w-0">
                <span className="block font-semibold">{e.title}</span>
                <span className="mt-1 flex flex-wrap items-center gap-2 text-xs text-slate-500 dark:text-slate-400">
                  <DifficultyBadge d={e.difficulty} />
                  {e.topic}
                </span>
              </span>
            </Link>
          </li>
        ))}
      </ul>
    </div>
  );
}
