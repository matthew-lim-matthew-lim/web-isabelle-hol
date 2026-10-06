'use client';
import Link from 'next/link';
import { useEffect, useState } from 'react';
import { getProgress, Progress } from '@/lib/storage';

export function LessonList({ lessons }: { lessons: { slug: string; title: string; summary: string }[] }) {
  const [prog, setProg] = useState<Progress>({});
  useEffect(() => setProg(getProgress('lesson')), []);
  return (
    <ol className="mt-6 space-y-3">
      {lessons.map((l) => (
        <li key={l.slug}>
          <Link
            href={`/learn/${l.slug}/`}
            className="flex items-start gap-3 rounded-xl border border-slate-200 p-4 transition hover:border-brand-400 hover:shadow-sm dark:border-slate-800 dark:hover:border-brand-600"
          >
            <span
              className={`mt-0.5 grid h-6 w-6 shrink-0 place-items-center rounded-full text-xs font-bold ${
                prog[l.slug]?.solved ? 'bg-emerald-500 text-white' : 'bg-slate-200 text-slate-600 dark:bg-slate-800 dark:text-slate-300'
              }`}
              aria-label={prog[l.slug]?.solved ? 'completed' : 'not completed'}
            >
              {prog[l.slug]?.solved ? '✓' : ''}
            </span>
            <span>
              <span className="block font-semibold">{l.title}</span>
              <span className="block text-sm text-slate-600 dark:text-slate-400">{l.summary}</span>
            </span>
          </Link>
        </li>
      ))}
    </ol>
  );
}
