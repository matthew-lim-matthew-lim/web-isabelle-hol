'use client';
// Client-side access to the proof checker running in a Web Worker.
import type { CheckResult } from '@/engine/check';

type Pending = { resolve: (r: CheckResult) => void; reject: (e: Error) => void; timer: ReturnType<typeof setTimeout> };

const TIMEOUT_MS = 20000;
let worker: Worker | null = null;
let nextId = 1;
const pending = new Map<number, Pending>();

function spawn(): Worker {
  const w = new Worker(new URL('../worker/checker.worker.ts', import.meta.url));
  w.onmessage = (e: MessageEvent<{ id: number; result?: CheckResult; error?: string }>) => {
    const p = pending.get(e.data.id);
    if (!p) return;
    clearTimeout(p.timer);
    pending.delete(e.data.id);
    if (e.data.result) p.resolve(e.data.result);
    else p.reject(new Error(e.data.error ?? 'checker failed'));
  };
  w.onerror = (ev) => {
    for (const [, p] of pending) {
      clearTimeout(p.timer);
      p.reject(new Error(ev.message || 'checker crashed'));
    }
    pending.clear();
    worker = null;
  };
  return w;
}

function getWorker() {
  if (!worker) worker = spawn();
  return worker;
}

/** Kill and restart the worker (e.g. after a timeout). */
function restart() {
  worker?.terminate();
  worker = null;
  for (const [, p] of pending) {
    clearTimeout(p.timer);
    p.reject(new Error('Checking timed out (the proof search took too long) — the checker was restarted.'));
  }
  pending.clear();
}

export function checkSource(src: string): Promise<CheckResult> {
  const id = nextId++;
  const w = getWorker();
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => restart(), TIMEOUT_MS);
    pending.set(id, { resolve, reject, timer });
    w.postMessage({ id, src });
  });
}

/** Warm up the worker early so the prelude is loaded before the user starts typing. */
export function warmUp() {
  if (typeof window !== 'undefined') getWorker();
}
