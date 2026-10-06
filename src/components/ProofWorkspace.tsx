'use client';
import { forwardRef, useEffect, useImperativeHandle, useRef, useState } from 'react';
import { IsabelleEditor, EditorHandle, diagsFromCommands } from './IsabelleEditor';
import { OutputPanel, StatusChip } from './OutputPanel';
import { SymbolBar } from './SymbolBar';
import { useChecker, CheckerState } from '@/lib/useChecker';

export interface WorkspaceHandle {
  setText(t: string): void;
  getText(): string;
}

interface Props {
  initial: string;
  onTextChange?: (t: string) => void;
  onChecked?: (s: CheckerState) => void;
  variant?: 'embedded' | 'ide';
  toolbar?: React.ReactNode;
  editorMinHeight?: string;
}

export const ProofWorkspace = forwardRef<WorkspaceHandle, Props>(function ProofWorkspace(
  { initial, onTextChange, onChecked, variant = 'embedded', toolbar, editorMinHeight },
  ref,
) {
  const [text, setText] = useState(initial);
  const [cursor, setCursor] = useState(0);
  const [outputOpen, setOutputOpen] = useState(true);
  const editor = useRef<EditorHandle>(null);
  const checker = useChecker(text);
  const cbRef = useRef(onChecked);
  cbRef.current = onChecked;

  useEffect(() => {
    if (checker.result && checker.checkedText === editor.current?.getText()) {
      editor.current?.setDiagnostics(diagsFromCommands(checker.result.commands));
    }
    if (!checker.checking) cbRef.current?.(checker);
  }, [checker]);

  useImperativeHandle(ref, () => ({
    setText(t: string) {
      editor.current?.setText(t);
      setText(t);
    },
    getText() {
      return editor.current?.getText() ?? text;
    },
  }));

  const onChange = (t: string) => {
    setText(t);
    onTextChange?.(t);
  };

  const editorEl = (
    <IsabelleEditor
      ref={editor}
      value={initial}
      onChange={onChange}
      onCursor={setCursor}
      minHeight={editorMinHeight}
      className="h-full"
    />
  );

  if (variant === 'ide') {
    return (
      <div className="flex h-full min-h-0 flex-col lg:flex-row">
        <div className="flex min-h-0 flex-1 flex-col border-slate-200 dark:border-slate-800 lg:border-r">
          {toolbar}
          <SymbolBar onInsert={(s) => editor.current?.insert(s)} className="border-b" />
          <div className="min-h-0 flex-1 overflow-hidden">{editorEl}</div>
        </div>
        <div
          className={`flex min-h-0 flex-col border-t border-slate-200 dark:border-slate-800 lg:h-auto lg:w-[42%] lg:border-t-0 ${
            outputOpen ? 'h-[40%]' : 'h-auto'
          }`}
        >
          {!outputOpen && (
            <button
              className="flex items-center gap-2 px-3 py-2 text-left text-xs text-slate-500 lg:hidden"
              onClick={() => setOutputOpen(true)}
              aria-expanded={false}
            >
              <span className="font-semibold text-slate-800 dark:text-slate-100">Output</span>
              <StatusChip result={checker.result} checking={checker.checking} error={checker.error} />
              <span className="ml-auto">Show ▴</span>
            </button>
          )}
          <OutputPanel
            className={`min-h-0 flex-1 ${outputOpen ? '' : 'hidden lg:flex'}`}
            result={checker.result}
            checking={checker.checking}
            error={checker.error}
            cursor={cursor}
            source={text}
            onJump={(p) => editor.current?.jumpTo(p)}
            headerExtra={
              <button className="ml-1 shrink-0 rounded px-1.5 py-0.5 text-xs text-slate-500 hover:bg-slate-100 dark:hover:bg-slate-800 lg:hidden" onClick={() => setOutputOpen(false)} aria-label="Hide output">
                Hide ▾
              </button>
            }
          />
        </div>
      </div>
    );
  }

  return (
    <div className="overflow-hidden rounded-xl border border-slate-200 shadow-sm dark:border-slate-800">
      {toolbar}
      <SymbolBar onInsert={(s) => editor.current?.insert(s)} className="border-b" />
      <div className="max-h-[60vh] overflow-auto">{editorEl}</div>
      <OutputPanel
        className="max-h-[45vh] border-t border-slate-200 dark:border-slate-800"
        result={checker.result}
        checking={checker.checking}
        error={checker.error}
        cursor={cursor}
        source={text}
        onJump={(p) => editor.current?.jumpTo(p)}
      />
    </div>
  );
});
