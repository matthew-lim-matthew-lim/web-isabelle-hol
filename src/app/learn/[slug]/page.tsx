import { notFound } from 'next/navigation';
import { LESSONS } from '@/content/lessons';
import { LessonView } from '@/components/LessonView';

export function generateStaticParams() {
  return LESSONS.map((l) => ({ slug: l.slug }));
}

export async function generateMetadata({ params }: { params: Promise<{ slug: string }> }) {
  const { slug } = await params;
  const l = LESSONS.find((x) => x.slug === slug);
  return { title: l ? `${l.title} · Learn Isabelle/HOL` : 'Lesson' };
}

export default async function LessonPage({ params }: { params: Promise<{ slug: string }> }) {
  const { slug } = await params;
  const idx = LESSONS.findIndex((l) => l.slug === slug);
  if (idx < 0) notFound();
  const prev = LESSONS[idx - 1];
  const next = LESSONS[idx + 1];
  return (
    <LessonView
      lesson={LESSONS[idx]}
      prev={prev ? { slug: prev.slug, title: prev.title } : null}
      next={next ? { slug: next.slug, title: next.title } : null}
    />
  );
}
