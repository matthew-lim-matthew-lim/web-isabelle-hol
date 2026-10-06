import { LESSONS } from '@/content/lessons';
import { LessonList } from '@/components/LessonList';

export const metadata = { title: 'Learn · Isabelle/HOL Playground' };

export default function LearnPage() {
  return (
    <main className="mx-auto max-w-3xl px-4 py-8">
      <h1 className="text-2xl font-bold sm:text-3xl">Learning mode</h1>
      <p className="mt-2 text-slate-600 dark:text-slate-300">
        A guided tour through Isabelle/HOL, following the structure of Tobias Nipkow’s <em>Programming and Proving in Isabelle/HOL</em>. Every
        example is live: edit it and watch the checker respond.
      </p>
      <LessonList lessons={LESSONS.map((l) => ({ slug: l.slug, title: l.title, summary: l.summary }))} />
    </main>
  );
}
