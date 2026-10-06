import { EXERCISES, TOPICS } from '@/content/exercises';
import { ExerciseList } from '@/components/ExerciseList';

export const metadata = { title: 'Practice · Isabelle/HOL Playground' };

export default function PracticePage() {
  return (
    <main className="mx-auto max-w-5xl px-4 py-8">
      <h1 className="text-2xl font-bold sm:text-3xl">Practice exercises</h1>
      <p className="mt-2 text-slate-600 dark:text-slate-300">
        Replace every <code className="rounded bg-slate-100 px-1 font-mono dark:bg-slate-800">sorry</code> with a real proof. An exercise is
        solved when the theory checks without errors and without <code className="rounded bg-slate-100 px-1 font-mono dark:bg-slate-800">sorry</code>.
        Your work is saved in this browser.
      </p>
      <ExerciseList
        topics={[...TOPICS]}
        exercises={EXERCISES.map((e) => ({ id: e.id, title: e.title, difficulty: e.difficulty, topic: e.topic }))}
      />
    </main>
  );
}
