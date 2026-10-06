'use client';
// Small wrappers around localStorage that never throw.

export function load<T>(key: string, fallback: T): T {
  try {
    const v = localStorage.getItem(key);
    return v === null ? fallback : (JSON.parse(v) as T);
  } catch {
    return fallback;
  }
}

export function save(key: string, value: unknown) {
  try {
    localStorage.setItem(key, JSON.stringify(value));
  } catch {
    /* storage full or unavailable */
  }
}

export function remove(key: string) {
  try {
    localStorage.removeItem(key);
  } catch {
    /* ignore */
  }
}

export type Progress = Record<string, { solved: boolean; at: number }>;

export function getProgress(kind: 'exercise' | 'lesson'): Progress {
  return load<Progress>(`isa-progress-${kind}`, {});
}

export function markSolved(kind: 'exercise' | 'lesson', id: string) {
  const p = getProgress(kind);
  if (!p[id]?.solved) {
    p[id] = { solved: true, at: Date.now() };
    save(`isa-progress-${kind}`, p);
    window.dispatchEvent(new Event('isa-progress'));
  }
}
