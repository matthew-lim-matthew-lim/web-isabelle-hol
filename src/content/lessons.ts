// Learning mode: lessons modelled on "Programming and Proving in Isabelle/HOL" (Nipkow).
// Every `code` block and every task solution is checked by the test suite.

export type LessonBlock =
  | { t: 'md'; text: string }
  | { t: 'code'; code: string; note?: string }
  | { t: 'task'; prompt: string; starter: string; solution: string; required: string[]; hints: string[] };

export interface Lesson {
  slug: string;
  title: string;
  summary: string;
  blocks: LessonBlock[];
}

export const LESSONS: Lesson[] = [
  {
    slug: 'welcome',
    title: '1. Welcome to Isabelle/HOL',
    summary: 'What a proof assistant is, theory files, and your first lemma.',
    blocks: [
      {
        t: 'md',
        text: `**Isabelle/HOL** is an interactive *proof assistant*: you write definitions and theorems, and Isabelle checks every step of your proofs with machine precision. *HOL* stands for **Higher-Order Logic** — roughly "functional programming + logic".

Everything lives in a **theory** file:

\`\`\`
theory Hello
  imports Main
begin
  (* definitions, lemmas and proofs *)
end
\`\`\`

\`Main\` is the standard library: natural numbers, lists, sets, … The editor checks your text *continuously* — just like Isabelle/jEdit. Commands that are fine are shown normally; errors are underlined in red, and the **Output** panel shows the *proof state* at your cursor.

A lemma consists of a statement in double quotes and a proof. The simplest proofs are one-liners like \`by simp\` ("by simplification") or \`by auto\`.`,
      },
      {
        t: 'code',
        note: 'Click inside a line to see the proof state. Try changing the statement to something false, e.g. `rev (rev xs) = rev xs`.',
        code: `theory Hello
  imports Main
begin

lemma my_first_lemma: "rev (rev xs) = xs"
  by simp

lemma "length (xs @ ys) = length xs + length ys"
  by simp

value "rev [1, 2, 3 :: nat]"

end`,
      },
      {
        t: 'md',
        text: `### Commands you just saw
- \`lemma name: "statement"\` — state a theorem (the name is optional).
- \`by simp\` — prove it by the simplifier.
- \`value "term"\` — evaluate a term (like a REPL).

### Typing mathematical symbols
Isabelle uses symbols like \`⟹ ∀ ∃ λ ∧ ∨ ¬ ≠ ≤\`. Use the **symbol bar** above the editor, or type ASCII abbreviations that are converted automatically: \`==>\` → \`⟹\`, \`-->\` → \`⟶\`, \`/\\\` → \`∧\`, \`\\/\` → \`∨\`, \`~=\` → \`≠\`, \`<=\` → \`≤\`, \`!!\` → \`⋀\`, \`%\` → \`λ\`. You can also type \`\\forall\`, \`\\exists\`, \`\\lambda\`, … and pick from the completion list.`,
      },
      {
        t: 'task',
        prompt: 'Prove that appending the empty list does nothing. Replace `sorry` with a proof.',
        starter: `lemma app_nil: "xs @ [] = xs"\n  sorry`,
        solution: `lemma app_nil: "xs @ [] = xs"\n  by simp`,
        required: ['app_nil'],
        hints: ['`by simp` is enough: this is a library simp rule.'],
      },
    ],
  },
  {
    slug: 'terms-types',
    title: '2. Terms, types and functions',
    summary: 'HOL as a functional language: types, λ, if, case, and `value`.',
    blocks: [
      {
        t: 'md',
        text: `HOL is a typed functional language. Basic types include \`bool\`, \`nat\` (natural numbers 0, 1, 2, …), \`int\`, and type constructors like \`'a list\` and \`'a set\`. Function types are written \`τ₁ ⇒ τ₂\`. Type variables are written \`'a\`, \`'b\`.

**Terms** are built by function application \`f x y\`, lambda abstraction \`λx. t\`, and syntax such as \`if b then x else y\`, \`case xs of [] ⇒ … | y # ys ⇒ …\`, \`let x = t in u\`.

Use \`term\` to see the type of a term, and \`value\` to evaluate it.`,
      },
      {
        t: 'code',
        note: 'Look at the Output panel for each command.',
        code: `term "λx. x + 1"
term "map (λx. x * 2) [1, 2, 3 :: nat]"
value "map (λx. x * 2) [1, 2, 3 :: nat]"
value "if 3 < (5::nat) then True else False"
value "case [1, 2, 3 :: nat] of [] ⇒ 0 | x # xs ⇒ x"
value "filter (λn. n mod 2 = 0) [0 ..< 10]"`,
      },
      {
        t: 'md',
        text: `### Lists
Lists are built from \`[]\` (empty) and \`x # xs\` (cons). \`[a, b, c]\` abbreviates \`a # b # c # []\`. Important functions: \`@\` (append), \`rev\`, \`length\`, \`map\`, \`filter\`, \`sum_list\`, \`take\`, \`drop\`, \`set\` (the set of elements).

### Numbers
Numerals like \`3\` are overloaded; write \`(3::nat)\` or \`(3::int)\` to fix the type. On \`nat\`, subtraction is truncated: \`2 - 5 = 0\`.`,
      },
      {
        t: 'code',
        code: `value "(2::nat) - 5"
value "(2::int) - 5"
value "length [a, b, c]"
value "[1, 2] @ [3, 4 :: nat]"
value "sum_list [1, 2, 3, 4 :: nat]"`,
      },
      {
        t: 'task',
        prompt: 'Use `value` to compute `rev [1, 2, 3]` and then prove the lemma below with `by simp`.',
        starter: `value "rev [1, 2, 3 :: nat]"\n\nlemma rev_ex: "rev [1, 2, 3 :: nat] = [3, 2, 1]"\n  sorry`,
        solution: `value "rev [1, 2, 3 :: nat]"\n\nlemma rev_ex: "rev [1, 2, 3 :: nat] = [3, 2, 1]"\n  by simp`,
        required: ['rev_ex'],
        hints: ['Concrete computations are solved by `simp`.'],
      },
    ],
  },
  {
    slug: 'datatypes-fun',
    title: '3. Datatypes and recursive functions',
    summary: 'Define your own types with `datatype` and functions with `fun`.',
    blocks: [
      {
        t: 'md',
        text: `New types are introduced with \`datatype\`. Each alternative is a *constructor*:

\`\`\`
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
\`\`\`

Recursive functions are defined with \`fun\` by *pattern matching* on constructors. Isabelle proves termination and generates simplification rules \`f.simps\` automatically (they are added to the simplifier) and an induction rule \`f.induct\`.`,
      },
      {
        t: 'code',
        code: `datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree ⇒ 'a tree" where
  "mirror Tip = Tip"
| "mirror (Node l a r) = Node (mirror r) a (mirror l)"

fun size_tree :: "'a tree ⇒ nat" where
  "size_tree Tip = 0"
| "size_tree (Node l a r) = size_tree l + 1 + size_tree r"

value "mirror (Node Tip (1::nat) (Node Tip 2 Tip))"
value "size_tree (Node Tip (1::nat) (Node Tip 2 Tip))"

thm mirror.simps`,
      },
      {
        t: 'md',
        text: `### Natural numbers are a datatype too
Conceptually \`datatype nat = 0 | Suc nat\`, so you can pattern match on \`0\` and \`Suc n\`. Here is our own addition:`,
      },
      {
        t: 'code',
        code: `fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

value "add 2 3"

lemma add_02: "add 0 n = n"
  by simp`,
      },
      {
        t: 'task',
        prompt: 'Define `double :: nat ⇒ nat` by recursion (so that `double n = 2 * n`) and check it with `value`. Then prove the given lemma about a concrete value.',
        starter: `fun double :: "nat ⇒ nat" where
  "double 0 = 0"
| "double (Suc n) = undefined"

lemma double_3: "double 3 = 6"
  sorry`,
        solution: `fun double :: "nat ⇒ nat" where
  "double 0 = 0"
| "double (Suc n) = Suc (Suc (double n))"

lemma double_3: "double 3 = 6"
  by simp`,
        required: ['double_3'],
        hints: ['`double (Suc n) = Suc (Suc (double n))`', 'Then `by simp` evaluates `double 3`.'],
      },
    ],
  },
  {
    slug: 'induction',
    title: '4. Proof by induction',
    summary: 'Structural induction with `apply (induction x)` and `auto`.',
    blocks: [
      {
        t: 'md',
        text: `Most interesting facts about recursive functions need **induction**. The method \`induction xs\` replaces the goal by one subgoal per constructor; in the recursive cases you get an **induction hypothesis** (IH).

An *apply-script* proof applies methods one at a time and ends with \`done\`. Put your cursor after each line to watch the proof state evolve.`,
      },
      {
        t: 'code',
        code: `fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_02: "add m 0 = m"
  apply (induction m)
   apply simp
  apply simp
  done`,
        note: 'After `apply (induction m)` there are two subgoals: the base case `add 0 0 = 0` and the step case with IH `add m 0 = m`.',
      },
      {
        t: 'md',
        text: `### Shortcuts
- \`apply auto\` works on *all* subgoals at once (\`simp\` only on the first).
- \`by (induction m) auto\` is the one-line form: first method, then a closing method for all remaining goals.

Proof state notation: \`⋀x. P x\` means "for an arbitrary but fixed x", and \`A ⟹ B\` means "assuming A, show B". Several assumptions are written \`⟦A; B⟧ ⟹ C\`.`,
      },
      {
        t: 'code',
        code: `lemma rev_app: "rev (xs @ ys) = rev ys @ rev xs"
  by (induction xs) auto

lemma len_map: "length (map f xs) = length xs"
  by (induction xs) auto`,
      },
      {
        t: 'task',
        prompt: 'Prove that our `add` is associative.',
        starter: `fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_assoc: "add (add m n) p = add m (add n p)"
  sorry`,
        solution: `fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_assoc: "add (add m n) p = add m (add n p)"
  by (induction m) auto`,
        required: ['add_assoc'],
        hints: ['Induct on the variable the function recurses on: `m`.'],
      },
    ],
  },
  {
    slug: 'lemmas-simp',
    title: '5. Auxiliary lemmas and the simplifier',
    summary: 'When induction gets stuck: find the missing lemma and add it with `[simp]` or `simp add:`.',
    blocks: [
      {
        t: 'md',
        text: `Often an induction gets stuck because a fact is missing. The remedy is to prove an **auxiliary lemma** first. There are two ways to make it available:

- give it the \`[simp]\` attribute: \`lemma foo [simp]: "..."\`, then the simplifier uses it everywhere afterwards;
- or pass it explicitly: \`by (simp add: foo)\` / \`by (auto simp add: foo)\`.

Simp lemmas are used *left to right* as rewrite rules, so the right-hand side should be "simpler".`,
      },
      {
        t: 'code',
        note: 'Classic example from the tutorial: proving `rev2 (rev2 xs) = xs` for our own reverse. Each lemma prepares the next.',
        code: `fun app :: "'a list ⇒ 'a list ⇒ 'a list" where
  "app [] ys = ys"
| "app (x # xs) ys = x # app xs ys"

fun rev2 :: "'a list ⇒ 'a list" where
  "rev2 [] = []"
| "rev2 (x # xs) = app (rev2 xs) [x]"

lemma app_Nil2 [simp]: "app xs [] = xs"
  by (induction xs) auto

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  by (induction xs) auto

lemma rev2_app [simp]: "rev2 (app xs ys) = app (rev2 ys) (rev2 xs)"
  by (induction xs) auto

theorem rev2_rev2 [simp]: "rev2 (rev2 xs) = xs"
  by (induction xs) auto`,
      },
      {
        t: 'md',
        text: `### Finding lemmas
- \`thm name\` shows a theorem.
- \`find_theorems "rev (_ @ _)"\` searches the library by pattern; \`find_theorems name: append\` by name.
- In a proof, \`try\` (or \`sledgehammer\`) searches for a working proof method, and \`quickcheck\` looks for counterexamples — very useful before you invest effort in a false statement!`,
      },
      {
        t: 'code',
        code: `find_theorems "rev (_ @ _)"

lemma "rev xs = xs"
  quickcheck
  oops`,
        note: '`oops` abandons a proof attempt.',
      },
      {
        t: 'task',
        prompt: 'Prove `sum (rev xs) = sum xs`. First prove (and use) a lemma about `sum (xs @ ys)`.',
        starter: `fun sum :: "nat list ⇒ nat" where
  "sum [] = 0"
| "sum (x # xs) = x + sum xs"

lemma sum_app: "sum (xs @ ys) = sum xs + sum ys"
  sorry

lemma sum_rev: "sum (rev xs) = sum xs"
  sorry`,
        solution: `fun sum :: "nat list ⇒ nat" where
  "sum [] = 0"
| "sum (x # xs) = x + sum xs"

lemma sum_app [simp]: "sum (xs @ ys) = sum xs + sum ys"
  by (induction xs) auto

lemma sum_rev: "sum (rev xs) = sum xs"
  by (induction xs) auto`,
        required: ['sum_app', 'sum_rev'],
        hints: ['Both by induction on `xs`.', 'Either add `[simp]` to `sum_app` or use `auto simp add: sum_app`.'],
      },
    ],
  },
  {
    slug: 'generalization',
    title: '6. Generalising the induction',
    summary: 'Accumulators need `arbitrary:` — the most common stumbling block.',
    blocks: [
      {
        t: 'md',
        text: `Tail-recursive functions with an **accumulator** change an argument in the recursive call. A plain induction then fails: the IH is about the *original* accumulator, but we need it for a different one.

The fix is to **generalise**: \`induction xs arbitrary: ys\` makes the IH hold *for all* \`ys\` (you will see \`⋀ys.\` in the IH).`,
      },
      {
        t: 'code',
        note: 'Try replacing `arbitrary: ys` by nothing and look at the stuck goal.',
        code: `fun itrev :: "'a list ⇒ 'a list ⇒ 'a list" where
  "itrev [] ys = ys"
| "itrev (x # xs) ys = itrev xs (x # ys)"

lemma itrev_rev: "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys)
   apply auto
  done

corollary "itrev xs [] = rev xs"
  by (simp add: itrev_rev)`,
      },
      {
        t: 'md',
        text: `**Rule of thumb:** generalise every variable that changes in the recursive call, and every free variable other than the induction variable that appears in an argument position that changes.`,
      },
      {
        t: 'task',
        prompt: 'Prove that tail-recursive addition agrees with `+`.',
        starter: `fun itadd :: "nat ⇒ nat ⇒ nat" where
  "itadd 0 n = n"
| "itadd (Suc m) n = itadd m (Suc n)"

lemma itadd_add: "itadd m n = m + n"
  sorry`,
        solution: `fun itadd :: "nat ⇒ nat ⇒ nat" where
  "itadd 0 n = n"
| "itadd (Suc m) n = itadd m (Suc n)"

lemma itadd_add: "itadd m n = m + n"
  by (induction m arbitrary: n) auto`,
        required: ['itadd_add'],
        hints: ['The second argument changes from `n` to `Suc n`.', '`by (induction m arbitrary: n) auto`'],
      },
    ],
  },
  {
    slug: 'logic',
    title: '7. Logic and proof methods',
    summary: 'Connectives, quantifiers, natural deduction rules, and `blast`/`auto`.',
    blocks: [
      {
        t: 'md',
        text: `HOL formulas use \`∧ ∨ ⟶ ¬ ⟷ ∀ ∃\`. Note the two implications: \`⟶\` is *object-level* (inside formulas) and \`⟹\` is *meta-level* (assumptions of a rule or goal).

**Automatic methods:**
- \`simp\`: rewriting with equations.
- \`auto\`: simplification + logical splitting; may leave goals.
- \`blast\`: strong for pure logic and sets; either succeeds or fails.
- \`force\`, \`fastforce\`: like \`auto\` but must solve the goal.
- \`arith\`/\`linarith\`: linear arithmetic.`,
      },
      {
        t: 'code',
        code: `lemma "A ∧ B ⟶ B ∧ A" by blast
lemma "(∀x. P x ⟶ Q x) ⟹ (∃x. P x) ⟶ (∃x. Q x)" by blast
lemma "(¬ (∃x. P x)) = (∀x. ¬ P x)" by auto
lemma "(x::nat) < y ⟹ y < z ⟹ x + 1 < z" by arith`,
      },
      {
        t: 'md',
        text: `### Natural deduction by hand
You can apply rules explicitly:
- \`rule r\`: unify the **conclusion** of \`r\` with the goal; new goals are the premises of \`r\` (*introduction*).
- \`erule r\`: like \`rule\`, but also consumes an assumption matching the first premise (*elimination*).
- \`drule r\`: forward reasoning from an assumption.

Introduction rules: \`conjI\`, \`disjI1\`, \`disjI2\`, \`impI\`, \`allI\`, \`exI\`, \`notI\`, \`iffI\`. Elimination rules: \`conjE\`, \`disjE\`, \`impE\`, \`allE\`, \`exE\`, \`notE\`. Use \`thm conjI\` to look at a rule.`,
      },
      {
        t: 'code',
        code: `thm conjI conjE disjE exI exE

lemma "A ∧ B ⟶ B ∧ A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
   apply assumption
  apply assumption
  done

lemma "∃x::nat. x + 2 = 5"
  apply (rule exI[of _ 3])
  apply simp
  done`,
      },
      {
        t: 'task',
        prompt: 'Prove `(∃x. ∀y. P x y) ⟶ (∀y. ∃x. P x y)` — with `blast`, or step by step with rules.',
        starter: `lemma swap: "(∃x. ∀y. P x y) ⟶ (∀y. ∃x. P x y)"\n  sorry`,
        solution: `lemma swap: "(∃x. ∀y. P x y) ⟶ (∀y. ∃x. P x y)"\n  by blast`,
        required: ['swap'],
        hints: ['`by blast`'],
      },
    ],
  },
  {
    slug: 'isar',
    title: '8. Structured proofs in Isar',
    summary: 'Readable proofs: `proof`, `assume`, `have`, `show`, `qed`.',
    blocks: [
      {
        t: 'md',
        text: `Apply-scripts are hard to read. **Isar** lets you write proofs that look like textbook mathematics:

\`\`\`
proof
  assume "A"
  have "B" by …
  show "C" by …
qed
\`\`\`

- \`proof\` applies a default introduction rule (for \`⟶\` it is \`impI\`); \`proof -\` applies none.
- \`fix x\` introduces an arbitrary \`x\` (for \`∀\`), \`assume\` introduces assumptions.
- \`have\` proves an intermediate fact; \`show\` proves the current goal.
- \`then\`/\`from facts\`/\`with facts\` feed facts into the next proof; \`hence\` = \`then have\`, \`thus\` = \`then show\`.
- \`?thesis\` abbreviates the statement being proved.`,
      },
      {
        t: 'code',
        code: `lemma "(∀x. P x ⟶ Q x) ⟹ (∀x. P x) ⟶ (∀x. Q x)"
proof
  assume a: "∀x. P x ⟶ Q x"
  assume b: "∀x. P x"
  show "∀x. Q x"
  proof
    fix x
    from b have "P x" by simp
    with a show "Q x" by simp
  qed
qed

lemma
  assumes "P ∧ Q"
  shows "Q ∧ P"
proof -
  from assms have p: "P" by simp
  from assms have q: "Q" by simp
  from q p show ?thesis by simp
qed`,
      },
      {
        t: 'md',
        text: `### Fact references
Facts can be referred to by name (\`a\`, \`assms\`), by \`this\` (the last fact), or by *quoting* them with cartouches: \`‹P x›\`.`,
      },
      {
        t: 'task',
        prompt: 'Complete the Isar proof by replacing the `sorry`s.',
        starter: `lemma conj_swap:
  assumes ab: "A ∧ B"
  shows "B ∧ A"
proof
  show "B" sorry
next
  show "A" sorry
qed`,
        solution: `lemma conj_swap:
  assumes ab: "A ∧ B"
  shows "B ∧ A"
proof
  show "B" using ab by simp
next
  show "A" using ab by simp
qed`,
        required: ['conj_swap'],
        hints: ['`show "B" using ab by simp`'],
      },
    ],
  },
  {
    slug: 'isar-induction',
    title: '9. Induction and case analysis in Isar',
    summary: '`proof (induction …)`, `case`, `?case`, `next`; `proof (cases …)`.',
    blocks: [
      {
        t: 'md',
        text: `In a structured induction proof each case is started with \`case\` and the constructor name (with names for its arguments). \`?case\` is the goal of that case, and the induction hypothesis is available as \`Name.IH\` (and is chained with \`then\`/\`thus\`).`,
      },
      {
        t: 'code',
        code: `lemma rev_rev: "rev (rev xs) = xs"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  thus ?case by simp
qed

fun sum_upto :: "nat ⇒ nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = Suc n + sum_upto n"

lemma "2 * sum_upto n = n * (n + 1)"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "2 * sum_upto (Suc n) = 2 * (Suc n) + 2 * sum_upto n" by simp
  also have "... = 2 * (Suc n) + n * (n + 1)" using Suc.IH by simp
  also have "... = Suc n * (Suc n + 1)" by simp
  finally show ?case .
qed`,
      },
      {
        t: 'md',
        text: `### Case analysis
\`proof (cases xs)\` splits into one case per constructor; \`proof (cases "P")\` splits on a formula (\`case True\` / \`case False\`).

### Calculations
\`also\`/\`finally\` chain equations (and inequalities): \`...\` refers to the right-hand side of the previous step.`,
      },
      {
        t: 'code',
        code: `lemma "length (tl xs) = length xs - 1"
proof (cases xs)
  case Nil
  thus ?thesis by simp
next
  case (Cons y ys)
  thus ?thesis by simp
qed`,
      },
      {
        t: 'task',
        prompt: 'Write a structured induction proof that `mirror (mirror t) = t`.',
        starter: `datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree ⇒ 'a tree" where
  "mirror Tip = Tip"
| "mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma mirror_mirror: "mirror (mirror t) = t"
proof (induction t)
  case Tip
  show ?case sorry
next
  case (Node l a r)
  thus ?case sorry
qed`,
        solution: `datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree ⇒ 'a tree" where
  "mirror Tip = Tip"
| "mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma mirror_mirror: "mirror (mirror t) = t"
proof (induction t)
  case Tip
  show ?case by simp
next
  case (Node l a r)
  thus ?case by simp
qed`,
        required: ['mirror_mirror'],
        hints: ['Both cases: `by simp` (the `Node` case uses the two IHs chained by `thus`).'],
      },
    ],
  },
  {
    slug: 'computation-induction',
    title: '10. Computation induction',
    summary: 'Induction following the recursion of a function: `rule: f.induct`.',
    blocks: [
      {
        t: 'md',
        text: `When a function's recursion is not a simple structural one (e.g. it peels off two elements at a time), structural induction is awkward. Every \`fun\` definition comes with its own induction rule \`f.induct\`, with one case per defining equation. Use it with \`induction x y rule: f.induct\`, listing the variables in the order of the function's arguments.`,
      },
      {
        t: 'code',
        code: `fun sep :: "'a ⇒ 'a list ⇒ 'a list" where
  "sep a [] = []"
| "sep a [x] = [x]"
| "sep a (x # y # zs) = x # a # sep a (y # zs)"

lemma "map f (sep a xs) = sep (f a) (map f xs)"
  apply (induction a xs rule: sep.induct)
    apply auto
  done`,
      },
      {
        t: 'task',
        prompt: 'Prove that `evn` (defined with three equations) holds for every `n + n`, or use computation induction on `evn` for the lemma below.',
        starter: `fun evn :: "nat ⇒ bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma evn_add: "evn n ⟹ evn (n + 2)"
  sorry`,
        solution: `fun evn :: "nat ⇒ bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma evn_add: "evn n ⟹ evn (n + 2)"
  by (induction n rule: evn.induct) auto`,
        required: ['evn_add'],
        hints: ['`by (induction n rule: evn.induct) auto` — or even just `by simp`.'],
      },
    ],
  },
  {
    slug: 'inductive',
    title: '11. Inductive predicates',
    summary: 'Defining predicates by rules, and rule induction.',
    blocks: [
      {
        t: 'md',
        text: `An **inductive predicate** is defined by introduction rules; it is the *least* predicate closed under them. Example: the even numbers.

\`\`\`
inductive ev :: "nat ⇒ bool" where
  ev0: "ev 0"
| evSS: "ev n ⟹ ev (Suc (Suc n))"
\`\`\`

- Prove \`ev\` facts by applying the rules: \`rule evSS\`, \`rule ev0\`.
- Prove things *from* \`ev n\` by **rule induction**: \`induction rule: ev.induct\` — one case per rule.
- **Rule inversion**: from \`ev (Suc 0)\` you get \`False\` by \`cases\`.`,
      },
      {
        t: 'code',
        code: `inductive ev :: "nat ⇒ bool" where
  ev0: "ev 0"
| evSS: "ev n ⟹ ev (Suc (Suc n))"

lemma "ev 4"
  apply (rule evSS)
  apply (rule evSS)
  apply (rule ev0)
  done

lemma ev_double: "ev (n + n)"
  by (induction n) (auto intro: ev0 evSS)

lemma "ev m ⟹ ev (m + 2)"
  by (simp add: evSS)

lemma "¬ ev (Suc 0)"
proof
  assume "ev (Suc 0)"
  then show False by cases
qed

lemma "ev n ⟹ ∃k. n = 2 * k"
proof (induction rule: ev.induct)
  case ev0
  show ?case by simp
next
  case (evSS n)
  then obtain k where "n = 2 * k" by blast
  hence "Suc (Suc n) = 2 * (k + 1)" by simp
  thus ?case by blast
qed`,
      },
      {
        t: 'task',
        prompt: 'Prove by rule induction that every `ev` number has an even double… more precisely: if `ev m` then `ev (m + m)`.',
        starter: `inductive ev :: "nat ⇒ bool" where
  ev0: "ev 0"
| evSS: "ev n ⟹ ev (Suc (Suc n))"

lemma ev_add_self: "ev m ⟹ ev (m + m)"
  sorry`,
        solution: `inductive ev :: "nat ⇒ bool" where
  ev0: "ev 0"
| evSS: "ev n ⟹ ev (Suc (Suc n))"

lemma ev_add_self: "ev m ⟹ ev (m + m)"
  apply (induction rule: ev.induct)
   apply (simp add: ev0)
  apply (simp add: evSS)
  done`,
        required: ['ev_add_self'],
        hints: ['`apply (induction rule: ev.induct)`', 'Step case: `Suc (Suc n) + Suc (Suc n)` simplifies to `Suc (Suc (Suc (Suc (n + n))))`, so `evSS` twice — `simp add: evSS` does it.'],
      },
    ],
  },
  {
    slug: 'sets',
    title: '12. Sets',
    summary: 'Set notation, membership reasoning, and `blast`.',
    blocks: [
      {
        t: 'md',
        text: `Sets of type \`'a set\` come with \`{}\`, \`{a, b}\`, \`{x. P x}\`, \`∈\`, \`∪\`, \`∩\`, \`-\`, \`⊆\`. The function \`set :: 'a list ⇒ 'a set\` gives the elements of a list. Set equalities are proved by *extensionality*: two sets are equal if they have the same elements. \`blast\` and \`auto\` know this.`,
      },
      {
        t: 'code',
        code: `lemma "A ∪ B = B ∪ A" by blast
lemma "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)" by blast
lemma "A ⊆ B ⟹ B ⊆ C ⟹ A ⊆ C" by blast
lemma "x ∈ {y. y > (3::nat)} ⟷ x > 3" by simp
lemma "set (xs @ ys) = set xs ∪ set ys" by simp
lemma "x ∈ set xs ⟹ x ∈ set (rev xs)" by simp`,
      },
      {
        t: 'task',
        prompt: 'Prove the distributive law for `∪` over `∩`.',
        starter: `lemma union_inter: "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)"\n  sorry`,
        solution: `lemma union_inter: "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)"\n  by blast`,
        required: ['union_inter'],
        hints: ['`by blast`'],
      },
    ],
  },
];
