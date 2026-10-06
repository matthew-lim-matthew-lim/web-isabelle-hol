'use client';
import { useEffect, useRef, useState } from 'react';
import type { CheckResult } from '@/engine/check';
import { checkSource } from './checker';

export interface CheckerState {
  result: CheckResult | null;
  checking: boolean;
  error: string | null;
  checkedText: string | null;
}

/** Continuously check `text` (debounced), like Isabelle/jEdit's continuous checking. */
export function useChecker(text: string, delay = 350): CheckerState {
  const [state, setState] = useState<CheckerState>({ result: null, checking: true, error: null, checkedText: null });
  const seq = useRef(0);
  useEffect(() => {
    const my = ++seq.current;
    setState((s) => ({ ...s, checking: true }));
    const timer = setTimeout(() => {
      checkSource(text)
        .then((result) => {
          if (my === seq.current) setState({ result, checking: false, error: null, checkedText: text });
        })
        .catch((e: Error) => {
          if (my === seq.current) setState((s) => ({ ...s, checking: false, error: e.message, checkedText: text }));
        });
    }, delay);
    return () => clearTimeout(timer);
  }, [text, delay]);
  return state;
}
