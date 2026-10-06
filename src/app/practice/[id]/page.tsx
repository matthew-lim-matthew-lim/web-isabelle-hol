import { notFound } from 'next/navigation';
import { EXERCISES } from '@/content/exercises';
import { ExerciseView } from '@/components/ExerciseView';

export function generateStaticParams() {
  return EXERCISES.map((e) => ({ id: e.id }));
}

export async function generateMetadata({ params }: { params: Promise<{ id: string }> }) {
  const { id } = await params;
  const e = EXERCISES.find((x) => x.id === id);
  return { title: e ? `${e.title} · Practice Isabelle/HOL` : 'Exercise' };
}

export default async function ExercisePage({ params }: { params: Promise<{ id: string }> }) {
  const { id } = await params;
  const idx = EXERCISES.findIndex((e) => e.id === id);
  if (idx < 0) notFound();
  const next = EXERCISES[idx + 1];
  const prev = EXERCISES[idx - 1];
  return <ExerciseView ex={EXERCISES[idx]} next={next ? { id: next.id, title: next.title } : null} prev={prev ? { id: prev.id, title: prev.title } : null} />;
}
