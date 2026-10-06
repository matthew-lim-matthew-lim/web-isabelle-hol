# Isabelle/HOL Playground

Learn and practise [Isabelle/HOL](https://isabelle.in.tum.de/) in the browser — on desktop or phone.

- **Learn** – 12 interactive lessons (first lemmas → induction → Isar → inductive predicates → sets), every example runnable, each with a graded task.
- **Practice** – 38 exercises (logic, arithmetic, lists, trees, structured proofs, inductive predicates, sets) with hints, solutions and saved progress.
- **IDE** – the normal Isabelle workflow: continuous checking, proof state at the cursor, errors as you type, symbol bar and ASCII → symbol conversion (`==>` → `⟹`), `\forall`-style completion, several theory files, import/export `.thy` (exported with `\<...>` symbols for real Isabelle), `value`, `term`, `thm`, `find_theorems`, `quickcheck`, `try`.

## How it works

Real Isabelle needs a JVM and multi-GB heap images, so it can't run on Vercel. This app contains its own proof
checker written in TypeScript (`src/engine`), running in a Web Worker:

- outer syntax (theory commands, Isar) and inner syntax (HOL terms, Unicode and ASCII), Hindley–Milner type inference
- `datatype`, `fun`/`primrec` (with sequential pattern completion and `f.induct`), `definition`, `abbreviation`, `inductive`, `type_synonym`
- methods `simp`, `auto`, `blast`, `force`/`fastforce`, `arith`/`linarith`, `metis`, `induction`/`induct` (structural, computation, rule induction, `arbitrary:`), `cases` (incl. rule inversion), `rule`/`erule`/`drule`/`intro`/`elim`/`rule_tac`, `subst`, `unfold`, method combinators
- Isar: `proof … qed`, `fix`, `assume`, `have`/`show`, `then`/`hence`/`thus`/`from`/`with`/`using`, `case`/`next`, `obtain`, `also`/`finally`, `moreover`/`ultimately`, `let`
- a `Main` library of list/set/arithmetic functions and lemmas (`src/engine/prelude.ts`)

It is a learning tool, not Isabelle's trusted kernel; see `/reference` in the app for differences.

## Development

```bash
npm install
npm run dev        # http://localhost:3000
npm test           # engine, soundness, all lesson examples and exercise solutions
npm run build      # static export to out/
npm run e2e        # mobile smoke test against a served out/ (default http://localhost:4173)
```

Check a theory file from the command line: `npx tsx scripts/run.ts file.thy -v`.

## Deploying to Vercel

Import the repository in Vercel — the Next.js framework is detected automatically, no environment variables are
needed. The site is a fully static export (`output: 'export'`), so it can also be hosted on any static host.
