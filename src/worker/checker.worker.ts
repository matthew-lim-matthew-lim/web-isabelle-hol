/// <reference lib="webworker" />
import { check, initPrelude } from '../engine/index';

initPrelude();

self.onmessage = (e: MessageEvent<{ id: number; src: string }>) => {
  const { id, src } = e.data;
  const t0 = performance.now();
  try {
    const result = check(src);
    (self as unknown as Worker).postMessage({ id, result, ms: Math.round(performance.now() - t0) });
  } catch (err) {
    (self as unknown as Worker).postMessage({ id, error: err instanceof Error ? err.message : String(err) });
  }
};
