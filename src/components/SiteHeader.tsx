'use client';
import Link from 'next/link';
import { usePathname } from 'next/navigation';
import { ThemeToggle } from './ThemeToggle';

const NAV = [
  { href: '/learn/', label: 'Learn' },
  { href: '/practice/', label: 'Practice' },
  { href: '/ide/', label: 'IDE' },
  { href: '/reference/', label: 'Reference' },
];

export function SiteHeader() {
  const path = usePathname() ?? '/';
  return (
    <header className="sticky top-0 z-30 border-b border-slate-200 bg-white/90 backdrop-blur dark:border-slate-800 dark:bg-slate-950/90">
      <div className="mx-auto flex h-12 max-w-7xl items-center gap-2 px-3 sm:px-4">
        <Link href="/" className="flex shrink-0 items-center gap-2 font-semibold" aria-label="Home">
          <span className="grid h-7 w-7 place-items-center rounded-lg bg-brand-600 font-serif text-lg text-white">λ</span>
          <span className="hidden sm:inline">Isabelle/HOL Playground</span>
        </Link>
        <nav className="no-scrollbar ml-1 flex min-w-0 flex-1 items-center gap-1 overflow-x-auto sm:ml-4">
          {NAV.map((n) => {
            const active = path.startsWith(n.href.replace(/\/$/, ''));
            return (
              <Link
                key={n.href}
                href={n.href}
                className={`whitespace-nowrap rounded-md px-2.5 py-1.5 text-sm font-medium transition ${
                  active ? 'bg-brand-50 text-brand-700 dark:bg-brand-900/40 dark:text-brand-300' : 'text-slate-600 hover:bg-slate-100 dark:text-slate-300 dark:hover:bg-slate-800'
                }`}
              >
                {n.label}
              </Link>
            );
          })}
        </nav>
        <ThemeToggle />
      </div>
    </header>
  );
}
