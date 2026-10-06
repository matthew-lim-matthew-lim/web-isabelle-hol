'use client';
import { useEffect, useRef, useState } from 'react';
import { ProofWorkspace, WorkspaceHandle } from './ProofWorkspace';
import { EXAMPLES, DEFAULT_THEORY } from '@/content/examples';
import { load, save } from '@/lib/storage';
import { decodeSymbols, encodeSymbols } from '@/engine/symbols';

interface TheoryFile {
  id: string;
  name: string;
  text: string;
}

const FILES_KEY = 'isa-ide-files';
const CURRENT_KEY = 'isa-ide-current';

function theoryName(text: string, fallback: string) {
  const m = /theory\s+([A-Za-z][A-Za-z0-9_']*)/.exec(text);
  return m ? m[1] : fallback;
}

function newId() {
  return Math.random().toString(36).slice(2, 10);
}

export function IdeApp() {
  const [files, setFiles] = useState<TheoryFile[] | null>(null);
  const [current, setCurrent] = useState<string>('');
  const [menu, setMenu] = useState(false);
  const ws = useRef<WorkspaceHandle>(null);
  const fileInput = useRef<HTMLInputElement>(null);
  const [height, setHeight] = useState<string>('calc(100dvh - 3rem)');

  useEffect(() => {
    let fs = load<TheoryFile[]>(FILES_KEY, []);
    if (!fs.length) fs = [{ id: newId(), name: 'Scratch', text: DEFAULT_THEORY }];
    setFiles(fs);
    const cur = load<string>(CURRENT_KEY, fs[0].id);
    setCurrent(fs.some((f) => f.id === cur) ? cur : fs[0].id);
    // track the visual viewport so the editor stays above the on-screen keyboard
    const vv = window.visualViewport;
    const upd = () => {
      if (vv) setHeight(`${Math.round(vv.height - 48)}px`);
    };
    upd();
    vv?.addEventListener('resize', upd);
    return () => vv?.removeEventListener('resize', upd);
  }, []);

  if (!files) return <div className="p-6 text-slate-500">Loading…</div>;
  const file = files.find((f) => f.id === current) ?? files[0];

  const persist = (fs: TheoryFile[]) => {
    setFiles(fs);
    save(FILES_KEY, fs);
  };
  const updateText = (text: string) => {
    const fs = files.map((f) => (f.id === file.id ? { ...f, text, name: theoryName(text, f.name) } : f));
    persist(fs);
  };
  const open = (id: string) => {
    setCurrent(id);
    save(CURRENT_KEY, id);
    setMenu(false);
  };
  const addFile = (name: string, text: string) => {
    const f = { id: newId(), name, text };
    persist([...files, f]);
    open(f.id);
  };
  const del = () => {
    if (!confirm(`Delete theory "${file.name}"?`)) return;
    let fs = files.filter((f) => f.id !== file.id);
    if (!fs.length) fs = [{ id: newId(), name: 'Scratch', text: DEFAULT_THEORY }];
    persist(fs);
    open(fs[0].id);
  };
  const download = (encode: boolean) => {
    const text = ws.current?.getText() ?? file.text;
    const blob = new Blob([encode ? encodeSymbols(text) : text], { type: 'text/plain;charset=utf-8' });
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = `${theoryName(text, file.name)}.thy`;
    a.click();
    setTimeout(() => URL.revokeObjectURL(a.href), 1000);
    setMenu(false);
  };
  const upload = async (ev: React.ChangeEvent<HTMLInputElement>) => {
    const f = ev.target.files?.[0];
    if (!f) return;
    const text = decodeSymbols(await f.text());
    addFile(theoryName(text, f.name.replace(/\.thy$/, '')), text);
    ev.target.value = '';
  };

  const toolbar = (
    <div className="relative flex items-center gap-1 border-b border-slate-200 px-2 py-1.5 dark:border-slate-800">
      <select
        className="min-w-0 max-w-[45%] rounded-md border border-slate-300 bg-white px-2 py-1 text-sm dark:border-slate-700 dark:bg-slate-900"
        value={file.id}
        onChange={(e) => open(e.target.value)}
        aria-label="Theory file"
      >
        {files.map((f) => (
          <option key={f.id} value={f.id}>
            {f.name}.thy
          </option>
        ))}
      </select>
      <button
        className="rounded-md px-2 py-1 text-sm hover:bg-slate-100 dark:hover:bg-slate-800"
        onClick={() => addFile('Untitled', 'theory Untitled\n  imports Main\nbegin\n\n\n\nend\n')}
        title="New theory"
      >
        ＋ New
      </button>
      <button className="rounded-md px-2 py-1 text-sm hover:bg-slate-100 dark:hover:bg-slate-800" onClick={() => setMenu((m) => !m)} aria-expanded={menu}>
        ☰ More
      </button>
      {menu && (
        <div className="absolute left-2 top-full z-20 mt-1 w-64 rounded-lg border border-slate-200 bg-white p-1 text-sm shadow-lg dark:border-slate-700 dark:bg-slate-900">
          <div className="px-2 pb-1 pt-2 text-xs font-semibold uppercase text-slate-500">Examples</div>
          {EXAMPLES.map((ex) => (
            <button key={ex.name} className="block w-full rounded px-2 py-1.5 text-left hover:bg-slate-100 dark:hover:bg-slate-800" onClick={() => addFile(ex.name, ex.text)}>
              {ex.name}
            </button>
          ))}
          <div className="my-1 border-t border-slate-200 dark:border-slate-700" />
          <button className="block w-full rounded px-2 py-1.5 text-left hover:bg-slate-100 dark:hover:bg-slate-800" onClick={() => fileInput.current?.click()}>
            Open .thy file…
          </button>
          <button className="block w-full rounded px-2 py-1.5 text-left hover:bg-slate-100 dark:hover:bg-slate-800" onClick={() => download(true)}>
            Download .thy (for real Isabelle)
          </button>
          <button className="block w-full rounded px-2 py-1.5 text-left hover:bg-slate-100 dark:hover:bg-slate-800" onClick={() => download(false)}>
            Download .thy (Unicode)
          </button>
          <button className="block w-full rounded px-2 py-1.5 text-left text-red-600 hover:bg-red-50 dark:hover:bg-red-950/40" onClick={del}>
            Delete this theory
          </button>
        </div>
      )}
      <input ref={fileInput} type="file" accept=".thy,text/plain" className="hidden" onChange={upload} />
    </div>
  );

  return (
    <div style={{ height }} className="min-h-[24rem]" onClick={() => menu && setMenu(false)}>
      <ProofWorkspace key={file.id} ref={ws} variant="ide" initial={file.text} onTextChange={updateText} toolbar={toolbar} />
    </div>
  );
}
