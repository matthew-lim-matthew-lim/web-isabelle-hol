'use client';
import { useEffect, useState } from 'react';
import { getProgress } from '@/lib/storage';

export function HomeProgress({ lessons, exercises }: { lessons: number; exercises: number }) {
  const [p, setP] = useState<{ l: number; e: number } | null>(null);
  useEffect(() => {
    const upd = () =>
      setP({
        l: Object.values(getProgress('lesson')).filter((x) => x.solved).length,
        e: Object.values(getProgress('exercise')).filter((x) => x.solved).length,
      });
    upd();
    window.addEventListener('isa-progress', upd);
    return () => window.removeEventListener('isa-progress', upd);
  }, []);
  if (!p || (p.l === 0 && p.e === 0)) return null;
  return (
    <p className="mt-4 text-sm text-slate-500 dark:text-slate-400">
      Your progress: {p.l}/{lessons} lessons · {p.e}/{exercises} exercises solved
    </p>
  );
}
