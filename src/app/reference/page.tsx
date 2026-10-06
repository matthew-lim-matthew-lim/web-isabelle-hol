import { ABBREVIATIONS } from '@/engine/symbols';

export const metadata = { title: 'Reference · Isabelle/HOL Playground' };

const H = ({ children }: { children: React.ReactNode }) => <h2 className="mb-3 mt-10 text-xl font-semibold">{children}</h2>;

function Table({ rows, head }: { rows: [string, string][]; head: [string, string] }) {
  return (
    <div className="overflow-x-auto">
      <table className="w-full text-left text-sm">
        <thead>
          <tr className="border-b border-slate-200 dark:border-slate-800">
            <th className="py-2 pr-4 font-semibold">{head[0]}</th>
            <th className="py-2 font-semibold">{head[1]}</th>
          </tr>
        </thead>
        <tbody>
          {rows.map(([a, b]) => (
            <tr key={a} className="border-b border-slate-100 align-top dark:border-slate-900">
              <td className="whitespace-nowrap py-2 pr-4 font-mono text-[13px]">{a}</td>
              <td className="py-2 text-slate-700 dark:text-slate-300">{b}</td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}

export default function ReferencePage() {
  return (
    <main className="mx-auto max-w-4xl px-4 py-8">
      <h1 className="text-2xl font-bold sm:text-3xl">Quick reference</h1>
      <p className="mt-2 text-slate-600 dark:text-slate-300">
        The syntax, commands and proof methods supported by this web edition. Everything here uses the same notation as real Isabelle/HOL.
      </p>

      <H>Theory commands</H>
      <Table
        head={['Command', 'Meaning']}
        rows={[
          ['theory T imports Main begin … end', 'A theory file'],
          ['datatype \'a t = C1 | C2 \'a "\'a t"', 'Algebraic datatype; generates t.induct, t.exhaust, injectivity/distinctness'],
          ['fun f :: "τ" where "eq1" | "eq2"', 'Recursive function by pattern matching (sequential patterns, f.simps, f.induct)'],
          ['primrec f :: "τ" where …', 'Primitive recursion (same as fun here)'],
          ['definition c :: "τ" where "c x = t"', 'Non-recursive definition; theorem c_def (not a simp rule)'],
          ['abbreviation c where "c x ≡ t"', 'Abbreviation (unfolded by simp)'],
          ['inductive p :: "τ" where r1: "…" | r2: "…"', 'Inductive predicate; p.intros, p.induct (rule induction), cases (inversion)'],
          ['type_synonym \'a t = "τ"', 'Type abbreviation'],
          ['lemma name [simp]: "P"', 'State a theorem (also theorem, corollary, proposition)'],
          ['lemma assumes a: "A" shows "B"', 'Long form with named assumptions (assms)'],
          ['lemmas name = facts', 'Name a list of facts'],
          ['declare foo [simp] / [simp del]', 'Add/remove simp rules'],
          ['value "t"', 'Evaluate a term'],
          ['term "t" / typ "τ"', 'Show a term with its type / a type'],
          ['thm name', 'Show a theorem'],
          ['find_theorems "pattern" name: x', 'Search the library'],
        ]}
      />

      <H>Proof commands</H>
      <Table
        head={['Command', 'Meaning']}
        rows={[
          ['apply method', 'Apply a method to the goal(s)'],
          ['done', 'Finish an apply-script'],
          ['by method [method]', 'Terminal proof'],
          ['sorry / oops', 'Skip a proof / abandon it'],
          ['proof [method] … qed', 'Structured (Isar) proof block; proof - applies nothing'],
          ['fix x / assume a: "A"', 'Introduce variables / assumptions'],
          ['have h: "P" / show "P"', 'Intermediate fact / goal'],
          ['then, hence, thus, from a, with a, using a', 'Chain facts into the next proof'],
          ['case Name / case (Name x y), next', 'Select an induction/case-analysis case'],
          ['?thesis, ?case, ...', 'Current statement, current case goal, previous right-hand side'],
          ['obtain x where "P x" by …', 'Get a witness from an existential'],
          ['also / finally / moreover / ultimately', 'Calculational reasoning'],
          ['let ?t = "term"', 'Local term abbreviation'],
          ['subgoal … done, defer, prefer n', 'Goal management'],
          ['quickcheck / nitpick', 'Search for a counterexample'],
          ['try / sledgehammer / try0', 'Search for a proof method'],
        ]}
      />

      <H>Proof methods</H>
      <Table
        head={['Method', 'What it does']}
        rows={[
          ['simp, simp add: a b, simp only: a, simp del: a', 'Rewriting with simp rules (+ arithmetic, if-splitting); first subgoal'],
          ['simp_all', 'simp on all subgoals'],
          ['auto [simp add: …] [intro: …] [dest: …]', 'Simplification + safe logic + light search, all subgoals'],
          ['blast, fast, metis a b', 'Classical first-order reasoning (tableau)'],
          ['force, fastforce', 'Like auto but must solve the goal'],
          ['arith, linarith, presburger', 'Linear arithmetic over nat/int'],
          ['induction x [arbitrary: y] [rule: f.induct]', 'Induction (structural, computation, or rule induction)'],
          ['induct x, induct_tac x', 'Variants of induction'],
          ['cases x, cases "P"', 'Case analysis on a datatype value or formula'],
          ['rule r, erule r, drule r, frule r', 'Natural deduction steps'],
          ['intro r…, elim r…', 'Repeated rule / erule'],
          ['rule_tac x = "t" in r', 'Rule with explicit instantiation'],
          ['assumption, this, fact a', 'Close a goal by an assumption / fact'],
          ['subst eq, unfold defs, insert facts', 'Rewriting once, unfolding definitions, adding facts'],
          ['clarify, clarsimp, safe', 'Safe logical decomposition'],
          ['m1, m2  m1; m2  m+  m?  m1 | m2  m[n]', 'Method combinators'],
        ]}
      />

      <H>Attributes</H>
      <Table
        head={['Attribute', 'Effect']}
        rows={[
          ['thm[of a b]', 'Instantiate schematic variables in order'],
          ['thm[where x = "t"]', 'Instantiate by name'],
          ['thm[OF f1 f2]', 'Discharge premises with facts'],
          ['thm[symmetric]', 'Flip an equation'],
          ['thm[THEN r]', 'Forward reasoning with rule r'],
          ['thm[rule_format]', 'Turn ∀/⟶ into schematic variables/⟹'],
          ['[simp], [intro], [dest], [elim]', 'Declare rules'],
        ]}
      />

      <H>Symbols</H>
      <p className="mb-3 text-sm text-slate-600 dark:text-slate-300">
        Type these ASCII sequences in the editor and they are converted automatically (as in Isabelle/jEdit). You can also type a backslash
        and a name, e.g. <code className="font-mono">\forall</code>, and pick from the completion list, or use the symbol bar.
      </p>
      <div className="grid grid-cols-2 gap-2 sm:grid-cols-4">
        {ABBREVIATIONS.filter(([a]) => !['<==>', '==', 'ALL', 'EX', ':~', '<-', '->'].includes(a)).map(([a, s]) => (
          <div key={a} className="flex items-center justify-between rounded-md border border-slate-200 px-3 py-2 font-mono text-sm dark:border-slate-800">
            <span className="text-slate-500">{a}</span>
            <span className="text-lg">{s}</span>
          </div>
        ))}
      </div>

      <H>Library (Main)</H>
      <p className="text-sm text-slate-700 dark:text-slate-300">
        Types <code>bool</code>, <code>nat</code>, <code>int</code>, <code>&apos;a list</code>, <code>&apos;a option</code>, <code>&apos;a × &apos;b</code>,{' '}
        <code>&apos;a set</code>. List functions: <code>@ rev length map filter concat sum_list prod_list replicate take drop hd tl last butlast ! set
        zip foldr foldl fold list_all list_ex distinct remdups count_list takeWhile dropWhile upt [a..&lt;b] sorted insort sort list_update null</code>.
        Pairs: <code>fst snd</code>; options: <code>the</code>. Sets: <code>{'{}'} insert ∪ ∩ - ⊆ {'{x. P x}'} ` UNIV</code>. Arithmetic:{' '}
        <code>+ - * div mod ^ Suc max min dvd</code>. Standard rules such as <code>conjI impI allI exI disjE</code> and lemmas such as{' '}
        <code>append_assoc rev_rev_ident add.commute algebra_simps</code> are available by their usual names.
      </p>

      <H>Differences from real Isabelle</H>
      <ul className="list-disc space-y-1 pl-6 text-sm text-slate-700 dark:text-slate-300">
        <li>Proofs are checked by a TypeScript reimplementation of the proof methods, not by Isabelle&apos;s LCF kernel. It aims to be sound for the supported fragment but is a learning tool.</li>
        <li>Automation is similar but not identical: occasionally a method succeeds here and fails in Isabelle or vice versa. Arithmetic (linear, with nonlinear terms treated as atoms) tends to be a little stronger.</li>
        <li>Not supported: locales, type classes, user-defined syntax (mixfix), mutual recursion, <code>function</code> with custom termination proofs, code generation, Sledgehammer&apos;s external provers, and theories beyond Main.</li>
        <li>Termination of <code>fun</code> is checked heuristically; if it cannot be shown a warning is given.</li>
      </ul>
    </main>
  );
}
