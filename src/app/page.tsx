import Link from 'next/link';
import { LESSONS } from '@/content/lessons';
import { EXERCISES } from '@/content/exercises';
import { HomeProgress } from '@/components/HomeProgress';

const SAMPLE = `lemma rev_rev: "rev (rev xs) = xs"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  thus ?case by simp
qed`;

export default function Home() {
  return (
    <main className="mx-auto max-w-6xl px-4 pb-16">
      <section className="grid items-center gap-8 py-10 md:grid-cols-2 md:py-16">
        <div>
          <p className="mb-3 inline-block rounded-full bg-brand-50 px-3 py-1 text-xs font-semibold text-brand-700 dark:bg-brand-900/40 dark:text-brand-300">
            Runs entirely in your browser · works on your phone
          </p>
          <h1 className="text-3xl font-bold tracking-tight sm:text-4xl md:text-5xl">
            Learn to prove things with <span className="text-brand-600 dark:text-brand-400">Isabelle/HOL</span>
          </h1>
          <p className="mt-4 text-lg text-slate-600 dark:text-slate-300">
            Interactive lessons, {EXERCISES.length} practice exercises with instant checking, and a full proof IDE with continuous checking, proof
            states, symbols and counterexample search — no installation required.
          </p>
          <div className="mt-6 flex flex-wrap gap-3">
            <Link href="/learn/" className="rounded-lg bg-brand-600 px-5 py-2.5 font-semibold text-white shadow hover:bg-brand-700">
              Start learning
            </Link>
            <Link href="/practice/" className="rounded-lg border border-slate-300 px-5 py-2.5 font-semibold hover:bg-slate-50 dark:border-slate-700 dark:hover:bg-slate-900">
              Practice
            </Link>
            <Link href="/ide/" className="rounded-lg border border-slate-300 px-5 py-2.5 font-semibold hover:bg-slate-50 dark:border-slate-700 dark:hover:bg-slate-900">
              Open the IDE
            </Link>
          </div>
          <HomeProgress lessons={LESSONS.length} exercises={EXERCISES.length} />
        </div>
        <div className="overflow-hidden rounded-xl border border-slate-200 bg-slate-50 shadow-sm dark:border-slate-800 dark:bg-slate-900">
          <div className="flex items-center gap-1.5 border-b border-slate-200 px-3 py-2 dark:border-slate-800">
            <span className="h-2.5 w-2.5 rounded-full bg-red-400" />
            <span className="h-2.5 w-2.5 rounded-full bg-amber-400" />
            <span className="h-2.5 w-2.5 rounded-full bg-emerald-400" />
            <span className="ml-2 text-xs text-slate-500">Scratch.thy</span>
          </div>
          <pre className="overflow-x-auto p-4 font-mono text-[13px] leading-relaxed">{SAMPLE}</pre>
          <div className="border-t border-slate-200 bg-white p-3 font-mono text-xs text-emerald-700 dark:border-slate-800 dark:bg-slate-950 dark:text-emerald-300">
            theorem rev_rev: rev (rev ?xs) = ?xs
          </div>
        </div>
      </section>

      <section className="grid gap-4 md:grid-cols-3">
        {[
          {
            href: '/learn/',
            title: 'Learning mode',
            text: `${LESSONS.length} lessons from first lemma to induction, Isar and inductive predicates — each with runnable examples and a small task.`,
            icon: '📘',
          },
          {
            href: '/practice/',
            title: 'Practice exercises',
            text: 'Graded exercises on logic, arithmetic, lists, trees, structured proofs and sets. Hints and solutions included; progress is saved.',
            icon: '🎯',
          },
          {
            href: '/ide/',
            title: 'IDE mode',
            text: 'The normal Isabelle workflow: write theories, see proof states at the cursor, errors as you type, multiple files, import/export .thy.',
            icon: '🛠️',
          },
        ].map((c) => (
          <Link
            key={c.href}
            href={c.href}
            className="group rounded-xl border border-slate-200 p-5 transition hover:border-brand-400 hover:shadow-md dark:border-slate-800 dark:hover:border-brand-600"
          >
            <div className="text-2xl">{c.icon}</div>
            <h2 className="mt-2 text-lg font-semibold group-hover:text-brand-600 dark:group-hover:text-brand-400">{c.title}</h2>
            <p className="mt-1 text-sm text-slate-600 dark:text-slate-300">{c.text}</p>
          </Link>
        ))}
      </section>

      <section className="mt-12 rounded-xl border border-slate-200 p-5 text-sm text-slate-600 dark:border-slate-800 dark:text-slate-300">
        <h2 className="mb-2 text-base font-semibold text-slate-900 dark:text-slate-100">About this playground</h2>
        <p>
          Real Isabelle needs a JVM and gigabytes of prebuilt heaps, so this site ships its own proof checker written in TypeScript. It implements a
          practical subset of Isabelle/HOL — theories, <code>datatype</code>, <code>fun</code>, <code>definition</code>, <code>inductive</code>,
          apply-scripts and Isar proofs, and the methods <code>simp</code>, <code>auto</code>, <code>blast</code>, <code>arith</code>,{' '}
          <code>induction</code>, <code>cases</code>, <code>rule</code> and more — with the same syntax as the real system, so what you learn here
          transfers directly. It is a learning tool, not a replacement for the trusted Isabelle kernel; see the{' '}
          <Link href="/reference/" className="text-brand-600 underline dark:text-brand-400">
            reference
          </Link>{' '}
          for what is supported, and get the real thing at{' '}
          <a href="https://isabelle.in.tum.de/" className="text-brand-600 underline dark:text-brand-400" target="_blank" rel="noreferrer">
            isabelle.in.tum.de
          </a>
          .
        </p>
      </section>
    </main>
  );
}
