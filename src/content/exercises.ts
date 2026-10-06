// Practice exercises. Every solution is checked by the test suite (tests/content.test.ts).

export type Difficulty = 'easy' | 'medium' | 'hard';

export interface Exercise {
  id: string;
  title: string;
  difficulty: Difficulty;
  topic: string;
  description: string;
  starter: string;
  solution: string;
  hints: string[];
  /** lemma names that must be proved (no sorry, no error) */
  required: string[];
}

const thy = (name: string, body: string) => `theory ${name}\n  imports Main\nbegin\n\n${body.trim()}\n\nend\n`;

export const TOPICS = ['Logic', 'Natural numbers', 'Lists', 'Datatypes', 'Structured proofs', 'Inductive predicates', 'Sets'] as const;

export const EXERCISES: Exercise[] = [
  // ---------------- Logic ----------------
  {
    id: 'conj-comm',
    title: 'Conjunction commutes',
    difficulty: 'easy',
    topic: 'Logic',
    description: 'Prove that conjunction is commutative using only the natural-deduction rules `impI`, `conjE` and `conjI` with `apply (rule ...)` / `apply (erule ...)` and `assumption`. (Of course `by blast` would also work — try the step-by-step way first!)',
    starter: thy('ConjComm', `lemma conj_comm: "A ∧ B ⟶ B ∧ A"\n  sorry`),
    solution: thy(
      'ConjComm',
      `lemma conj_comm: "A ∧ B ⟶ B ∧ A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
   apply assumption
  apply assumption
  done`,
    ),
    hints: ['Start with `apply (rule impI)` to move `A ∧ B` into the assumptions.', '`apply (erule conjE)` splits the assumption `A ∧ B` into `A` and `B`.', 'Then `apply (rule conjI)` creates two subgoals, each closed by `apply assumption`.'],
    required: ['conj_comm'],
  },
  {
    id: 'disj-comm',
    title: 'Disjunction commutes',
    difficulty: 'easy',
    topic: 'Logic',
    description: 'Prove `A ∨ B ⟶ B ∨ A`. Use `disjE` to do a case analysis on the assumption, and `disjI1`/`disjI2` to prove a disjunction.',
    starter: thy('DisjComm', `lemma disj_comm: "A ∨ B ⟶ B ∨ A"\n  sorry`),
    solution: thy(
      'DisjComm',
      `lemma disj_comm: "A ∨ B ⟶ B ∨ A"
  apply (rule impI)
  apply (erule disjE)
   apply (rule disjI2)
   apply assumption
  apply (rule disjI1)
  apply assumption
  done`,
    ),
    hints: ['`apply (rule impI)` first.', '`apply (erule disjE)` gives you two subgoals: one with `A`, one with `B`.', 'For the first subgoal use `rule disjI2` (the right disjunct `A`).'],
    required: ['disj_comm'],
  },
  {
    id: 'curry',
    title: 'Currying',
    difficulty: 'easy',
    topic: 'Logic',
    description: 'Show that `(A ∧ B ⟶ C)` is equivalent to `(A ⟶ B ⟶ C)`. Any proof method is allowed.',
    starter: thy('Curry', `lemma curry: "(A ∧ B ⟶ C) = (A ⟶ B ⟶ C)"\n  sorry`),
    solution: thy('Curry', `lemma curry: "(A ∧ B ⟶ C) = (A ⟶ B ⟶ C)"\n  by blast`),
    hints: ['Try `by auto` or `by blast` — both are complete for propositional logic.'],
    required: ['curry'],
  },
  {
    id: 'de-morgan',
    title: 'De Morgan',
    difficulty: 'easy',
    topic: 'Logic',
    description: 'Prove one of De Morgan’s laws.',
    starter: thy('DeMorgan', `lemma de_morgan: "¬ (A ∨ B) ⟷ ¬ A ∧ ¬ B"\n  sorry`),
    solution: thy('DeMorgan', `lemma de_morgan: "¬ (A ∨ B) ⟷ ¬ A ∧ ¬ B"\n  by auto`),
    hints: ['`by auto` or `by simp` will do it.'],
    required: ['de_morgan'],
  },
  {
    id: 'quant-swap',
    title: 'Swapping quantifiers',
    difficulty: 'medium',
    topic: 'Logic',
    description: 'Prove that an existential quantifier can be pulled out of a universal one (but not the other way round!). Use `blast`, or step by step with `exE`, `allI`, `exI`, `allE`.',
    starter: thy('QuantSwap', `lemma quant_swap: "(∃x. ∀y. P x y) ⟶ (∀y. ∃x. P x y)"\n  sorry`),
    solution: thy(
      'QuantSwap',
      `lemma quant_swap: "(∃x. ∀y. P x y) ⟶ (∀y. ∃x. P x y)"
  apply (rule impI)
  apply (rule allI)
  apply (erule exE)
  apply (rule exI)
  apply (erule allE)
  apply assumption
  done`,
    ),
    hints: ['`by blast` works.', 'Step by step: `rule impI`, `rule allI`, `erule exE`, then `rule exI` and `erule allE`.'],
    required: ['quant_swap'],
  },
  {
    id: 'drinker',
    title: 'Classical reasoning',
    difficulty: 'medium',
    topic: 'Logic',
    description: 'Prove the law of the excluded middle in the form below and a classic consequence. Classical provers like `blast` handle this automatically.',
    starter: thy(
      'Classical',
      `lemma peirce: "((A ⟶ B) ⟶ A) ⟶ A"
  sorry

lemma contra: "(¬ B ⟶ ¬ A) ⟶ (A ⟶ B)"
  sorry`,
    ),
    solution: thy(
      'Classical',
      `lemma peirce: "((A ⟶ B) ⟶ A) ⟶ A"
  by blast

lemma contra: "(¬ B ⟶ ¬ A) ⟶ (A ⟶ B)"
  by blast`,
    ),
    hints: ['Both are one-liners with `by blast`.'],
    required: ['peirce', 'contra'],
  },
  {
    id: 'isar-logic',
    title: 'A structured proof',
    difficulty: 'medium',
    topic: 'Structured proofs',
    description: 'Fill in the Isar proof. Replace each `sorry` with a short proof (e.g. `by simp`, `by blast`, or `using … by …`).',
    starter: thy(
      'IsarLogic',
      `lemma isar_logic:
  assumes ab: "A ∧ B" and bc: "B ⟶ C"
  shows "A ∧ C"
proof
  show "A" sorry
next
  from ab have "B" sorry
  with bc show "C" sorry
qed`,
    ),
    solution: thy(
      'IsarLogic',
      `lemma isar_logic:
  assumes ab: "A ∧ B" and bc: "B ⟶ C"
  shows "A ∧ C"
proof
  show "A" using ab by simp
next
  from ab have "B" by simp
  with bc show "C" by simp
qed`,
    ),
    hints: ['`show "A" using ab by simp`', '`from ab have "B" by simp` — the fact `ab` is chained into the proof.', '`with bc show "C" by simp` uses both `bc` and the previous fact `B`.'],
    required: ['isar_logic'],
  },
  // ---------------- Natural numbers ----------------
  {
    id: 'add-zero',
    title: 'Addition: right zero',
    difficulty: 'easy',
    topic: 'Natural numbers',
    description: 'We define our own addition on natural numbers by recursion on the first argument. Prove that `0` is also a right identity. You need induction!',
    starter: thy(
      'AddZero',
      `fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_0_right: "add m 0 = m"
  sorry`,
    ),
    solution: thy(
      'AddZero',
      `fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_0_right: "add m 0 = m"
  apply (induction m)
   apply auto
  done`,
    ),
    hints: ['Use `apply (induction m)`.', 'Both resulting subgoals are solved by `auto` (or `simp`).'],
    required: ['add_0_right'],
  },
  {
    id: 'add-assoc',
    title: 'Addition is associative',
    difficulty: 'easy',
    topic: 'Natural numbers',
    description: 'Prove associativity of `add`.',
    starter: thy(
      'AddAssoc',
      `fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_assoc: "add (add m n) p = add m (add n p)"
  sorry`,
    ),
    solution: thy(
      'AddAssoc',
      `fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_assoc: "add (add m n) p = add m (add n p)"
  by (induction m) auto`,
    ),
    hints: ['Induct on the variable in the recursive (first) argument position: `m`.'],
    required: ['add_assoc'],
  },
  {
    id: 'add-comm',
    title: 'Addition is commutative',
    difficulty: 'medium',
    topic: 'Natural numbers',
    description: 'Prove commutativity of `add`. You will need two auxiliary lemmas first (prove them yourself!).',
    starter: thy(
      'AddComm',
      `fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_0_right: "add m 0 = m"
  sorry

lemma add_Suc_right: "add m (Suc n) = Suc (add m n)"
  sorry

lemma add_comm: "add m n = add n m"
  sorry`,
    ),
    solution: thy(
      'AddComm',
      `fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_0_right: "add m 0 = m"
  by (induction m) auto

lemma add_Suc_right: "add m (Suc n) = Suc (add m n)"
  by (induction m) auto

lemma add_comm: "add m n = add n m"
  by (induction m) (auto simp add: add_0_right add_Suc_right)`,
    ),
    hints: ['Each auxiliary lemma: `by (induction m) auto`.', 'In the main lemma, pass the auxiliary lemmas to the simplifier: `auto simp add: add_0_right add_Suc_right`.'],
    required: ['add_0_right', 'add_Suc_right', 'add_comm'],
  },
  {
    id: 'double',
    title: 'Doubling',
    difficulty: 'easy',
    topic: 'Natural numbers',
    description: 'Define `double` so that the lemma holds, then prove it. (A definition is given — just prove the lemma.)',
    starter: thy(
      'Double',
      `fun double :: "nat ⇒ nat" where
  "double 0 = 0"
| "double (Suc n) = Suc (Suc (double n))"

lemma double_add: "double m = m + m"
  sorry`,
    ),
    solution: thy(
      'Double',
      `fun double :: "nat ⇒ nat" where
  "double 0 = 0"
| "double (Suc n) = Suc (Suc (double n))"

lemma double_add: "double m = m + m"
  by (induction m) auto`,
    ),
    hints: ['Induction on `m`, then `auto` — the built-in arithmetic does the rest.'],
    required: ['double_add'],
  },
  {
    id: 'gauss',
    title: 'Gauss’s formula',
    difficulty: 'medium',
    topic: 'Natural numbers',
    description: 'Prove the classic formula `0 + 1 + … + n = n(n+1)/2`, stated without division.',
    starter: thy(
      'Gauss',
      `fun sum_upto :: "nat ⇒ nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = Suc n + sum_upto n"

lemma gauss: "2 * sum_upto n = n * (n + 1)"
  sorry`,
    ),
    solution: thy(
      'Gauss',
      `fun sum_upto :: "nat ⇒ nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = Suc n + sum_upto n"

lemma gauss: "2 * sum_upto n = n * (n + 1)"
  by (induction n) auto`,
    ),
    hints: ['Induction on `n`; the step case is linear arithmetic once the IH is available.'],
    required: ['gauss'],
  },
  {
    id: 'sum-odd',
    title: 'Sum of odd numbers',
    difficulty: 'medium',
    topic: 'Natural numbers',
    description: 'The sum of the first `n` odd numbers is `n²`. Prove it.',
    starter: thy(
      'SumOdd',
      `fun sum_odd :: "nat ⇒ nat" where
  "sum_odd 0 = 0"
| "sum_odd (Suc n) = (2 * n + 1) + sum_odd n"

lemma sum_odd_square: "sum_odd n = n * n"
  sorry`,
    ),
    solution: thy(
      'SumOdd',
      `fun sum_odd :: "nat ⇒ nat" where
  "sum_odd 0 = 0"
| "sum_odd (Suc n) = (2 * n + 1) + sum_odd n"

lemma sum_odd_square: "sum_odd n = n * n"
  by (induction n) auto`,
    ),
    hints: ['`by (induction n) auto`'],
    required: ['sum_odd_square'],
  },
  {
    id: 'pow-two',
    title: 'Powers of two',
    difficulty: 'medium',
    topic: 'Natural numbers',
    description: 'Show that `pow2 n` is always positive and that `pow2 (m + n) = pow2 m * pow2 n`.',
    starter: thy(
      'PowTwo',
      `fun pow2 :: "nat ⇒ nat" where
  "pow2 0 = 1"
| "pow2 (Suc n) = 2 * pow2 n"

lemma pow2_pos: "0 < pow2 n"
  sorry

lemma pow2_add: "pow2 (m + n) = pow2 m * pow2 n"
  sorry`,
    ),
    solution: thy(
      'PowTwo',
      `fun pow2 :: "nat ⇒ nat" where
  "pow2 0 = 1"
| "pow2 (Suc n) = 2 * pow2 n"

lemma pow2_pos: "0 < pow2 n"
  by (induction n) auto

lemma pow2_add: "pow2 (m + n) = pow2 m * pow2 n"
  by (induction m) auto`,
    ),
    hints: ['Which variable does `pow2 (m + n)` recurse on? `m + n` unfolds when `m` is `Suc …`, so induct on `m`.'],
    required: ['pow2_pos', 'pow2_add'],
  },
  {
    id: 'evn-double',
    title: 'Even numbers (recursive)',
    difficulty: 'medium',
    topic: 'Natural numbers',
    description: 'Prove that doubling always gives an even number, using the recursive predicate `evn`. Computation induction on `evn` is not needed here — plain induction suffices.',
    starter: thy(
      'EvnDouble',
      `fun evn :: "nat ⇒ bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma evn_double: "evn (n + n)"
  sorry`,
    ),
    solution: thy(
      'EvnDouble',
      `fun evn :: "nat ⇒ bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma evn_double: "evn (n + n)"
  by (induction n) auto`,
    ),
    hints: ['`Suc n + Suc n` simplifies to `Suc (Suc (n + n))`.'],
    required: ['evn_double'],
  },
  // ---------------- Lists ----------------
  {
    id: 'app-nil',
    title: 'Appending the empty list',
    difficulty: 'easy',
    topic: 'Lists',
    description: 'Define your own append function `app` and prove `app xs [] = xs`.',
    starter: thy(
      'AppNil',
      `fun app :: "'a list ⇒ 'a list ⇒ 'a list" where
  "app [] ys = ys"
| "app (x # xs) ys = x # app xs ys"

lemma app_Nil2: "app xs [] = xs"
  sorry`,
    ),
    solution: thy(
      'AppNil',
      `fun app :: "'a list ⇒ 'a list ⇒ 'a list" where
  "app [] ys = ys"
| "app (x # xs) ys = x # app xs ys"

lemma app_Nil2: "app xs [] = xs"
  apply (induction xs)
   apply auto
  done`,
    ),
    hints: ['Structural induction on `xs`.'],
    required: ['app_Nil2'],
  },
  {
    id: 'rev-rev',
    title: 'Reverse is an involution',
    difficulty: 'medium',
    topic: 'Lists',
    description: "This is the first big example of the Isabelle tutorial. Define `app` and `rev'` yourself and prove that reversing twice gives the original list. You need several lemmas — in this order.",
    starter: thy(
      'RevRev',
      `fun app :: "'a list ⇒ 'a list ⇒ 'a list" where
  "app [] ys = ys"
| "app (x # xs) ys = x # app xs ys"

fun rev' :: "'a list ⇒ 'a list" where
  "rev' [] = []"
| "rev' (x # xs) = app (rev' xs) [x]"

lemma app_Nil2 [simp]: "app xs [] = xs"
  sorry

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  sorry

lemma rev_app [simp]: "rev' (app xs ys) = app (rev' ys) (rev' xs)"
  sorry

theorem rev_rev [simp]: "rev' (rev' xs) = xs"
  sorry`,
    ),
    solution: thy(
      'RevRev',
      `fun app :: "'a list ⇒ 'a list ⇒ 'a list" where
  "app [] ys = ys"
| "app (x # xs) ys = x # app xs ys"

fun rev' :: "'a list ⇒ 'a list" where
  "rev' [] = []"
| "rev' (x # xs) = app (rev' xs) [x]"

lemma app_Nil2 [simp]: "app xs [] = xs"
  by (induction xs) auto

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  by (induction xs) auto

lemma rev_app [simp]: "rev' (app xs ys) = app (rev' ys) (rev' xs)"
  by (induction xs) auto

theorem rev_rev [simp]: "rev' (rev' xs) = xs"
  by (induction xs) auto`,
    ),
    hints: ['Each lemma is `by (induction xs) auto`.', 'The `[simp]` attribute makes each lemma available to later `auto` calls — that is why the order matters.'],
    required: ['app_Nil2', 'app_assoc', 'rev_app', 'rev_rev'],
  },
  {
    id: 'itrev',
    title: 'Tail-recursive reverse',
    difficulty: 'medium',
    topic: 'Lists',
    description: 'Prove that the accumulator-based `itrev` computes `rev`. The induction needs to be generalised — this is a key technique!',
    starter: thy(
      'Itrev',
      `fun itrev :: "'a list ⇒ 'a list ⇒ 'a list" where
  "itrev [] ys = ys"
| "itrev (x # xs) ys = itrev xs (x # ys)"

lemma itrev_rev: "itrev xs ys = rev xs @ ys"
  sorry

corollary "itrev xs [] = rev xs"
  by (simp add: itrev_rev)`,
    ),
    solution: thy(
      'Itrev',
      `fun itrev :: "'a list ⇒ 'a list ⇒ 'a list" where
  "itrev [] ys = ys"
| "itrev (x # xs) ys = itrev xs (x # ys)"

lemma itrev_rev: "itrev xs ys = rev xs @ ys"
  by (induction xs arbitrary: ys) auto

corollary "itrev xs [] = rev xs"
  by (simp add: itrev_rev)`,
    ),
    hints: ['A plain `induction xs` fails: the IH talks about a fixed `ys`, but the recursive call uses `x # ys`.', 'Use `induction xs arbitrary: ys`.'],
    required: ['itrev_rev'],
  },
  {
    id: 'length-app',
    title: 'Length of append',
    difficulty: 'easy',
    topic: 'Lists',
    description: 'With your own length function `len`, show that the length of an append is the sum of the lengths.',
    starter: thy(
      'LenApp',
      `fun len :: "'a list ⇒ nat" where
  "len [] = 0"
| "len (x # xs) = Suc (len xs)"

lemma len_app: "len (xs @ ys) = len xs + len ys"
  sorry`,
    ),
    solution: thy(
      'LenApp',
      `fun len :: "'a list ⇒ nat" where
  "len [] = 0"
| "len (x # xs) = Suc (len xs)"

lemma len_app: "len (xs @ ys) = len xs + len ys"
  by (induction xs) auto`,
    ),
    hints: ['Induct on `xs`, the list that `@` recurses on.'],
    required: ['len_app'],
  },
  {
    id: 'count',
    title: 'Counting occurrences',
    difficulty: 'easy',
    topic: 'Lists',
    description: 'Define `count x xs` (number of occurrences of `x` in `xs`) — it is given — and prove `count x xs ≤ length xs`.',
    starter: thy(
      'Count',
      `fun count :: "'a ⇒ 'a list ⇒ nat" where
  "count x [] = 0"
| "count x (y # ys) = (if x = y then Suc (count x ys) else count x ys)"

lemma count_le_length: "count x xs ≤ length xs"
  sorry`,
    ),
    solution: thy(
      'Count',
      `fun count :: "'a ⇒ 'a list ⇒ nat" where
  "count x [] = 0"
| "count x (y # ys) = (if x = y then Suc (count x ys) else count x ys)"

lemma count_le_length: "count x xs ≤ length xs"
  by (induction xs) auto`,
    ),
    hints: ['`auto` splits the `if` automatically.'],
    required: ['count_le_length'],
  },
  {
    id: 'snoc-reverse',
    title: 'snoc and reverse',
    difficulty: 'medium',
    topic: 'Lists',
    description: 'Exercise 2.6 of *Programming and Proving*: define `snoc` (append at the end) and `reverse` via `snoc`, then prove `reverse (reverse xs) = xs`. You will need a lemma about `reverse (snoc xs x)`.',
    starter: thy(
      'SnocReverse',
      `fun snoc :: "'a list ⇒ 'a ⇒ 'a list" where
  "snoc [] x = [x]"
| "snoc (y # ys) x = y # snoc ys x"

fun reverse :: "'a list ⇒ 'a list" where
  "reverse [] = []"
| "reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc: "reverse (snoc xs x) = x # reverse xs"
  sorry

theorem reverse_reverse: "reverse (reverse xs) = xs"
  sorry`,
    ),
    solution: thy(
      'SnocReverse',
      `fun snoc :: "'a list ⇒ 'a ⇒ 'a list" where
  "snoc [] x = [x]"
| "snoc (y # ys) x = y # snoc ys x"

fun reverse :: "'a list ⇒ 'a list" where
  "reverse [] = []"
| "reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc: "reverse (snoc xs x) = x # reverse xs"
  by (induction xs) auto

theorem reverse_reverse: "reverse (reverse xs) = xs"
  by (induction xs) (auto simp add: reverse_snoc)`,
    ),
    hints: ['First lemma: induction on `xs`.', 'Main theorem: induction, and give `reverse_snoc` to the simplifier: `(auto simp add: reverse_snoc)`.'],
    required: ['reverse_snoc', 'reverse_reverse'],
  },
  {
    id: 'map-comp',
    title: 'Map fusion',
    difficulty: 'easy',
    topic: 'Lists',
    description: 'With your own `mymap`, prove that mapping twice is mapping the composition.',
    starter: thy(
      'MapComp',
      `fun mymap :: "('a ⇒ 'b) ⇒ 'a list ⇒ 'b list" where
  "mymap f [] = []"
| "mymap f (x # xs) = f x # mymap f xs"

lemma mymap_mymap: "mymap f (mymap g xs) = mymap (λx. f (g x)) xs"
  sorry`,
    ),
    solution: thy(
      'MapComp',
      `fun mymap :: "('a ⇒ 'b) ⇒ 'a list ⇒ 'b list" where
  "mymap f [] = []"
| "mymap f (x # xs) = f x # mymap f xs"

lemma mymap_mymap: "mymap f (mymap g xs) = mymap (λx. f (g x)) xs"
  by (induction xs) auto`,
    ),
    hints: ['Induction on `xs`.'],
    required: ['mymap_mymap'],
  },
  {
    id: 'sum-list-rev',
    title: 'Summing a reversed list',
    difficulty: 'medium',
    topic: 'Lists',
    description: 'Define `sum` on lists of naturals and prove that reversing does not change the sum. A lemma about `sum (xs @ ys)` helps.',
    starter: thy(
      'SumRev',
      `fun sum :: "nat list ⇒ nat" where
  "sum [] = 0"
| "sum (x # xs) = x + sum xs"

lemma sum_app: "sum (xs @ ys) = sum xs + sum ys"
  sorry

lemma sum_rev: "sum (rev xs) = sum xs"
  sorry`,
    ),
    solution: thy(
      'SumRev',
      `fun sum :: "nat list ⇒ nat" where
  "sum [] = 0"
| "sum (x # xs) = x + sum xs"

lemma sum_app: "sum (xs @ ys) = sum xs + sum ys"
  by (induction xs) auto

lemma sum_rev: "sum (rev xs) = sum xs"
  by (induction xs) (auto simp add: sum_app)`,
    ),
    hints: ['`sum (rev (x # xs)) = sum (rev xs @ [x])` — so `sum_app` is exactly what is needed.'],
    required: ['sum_app', 'sum_rev'],
  },
  {
    id: 'intersperse',
    title: 'intersperse',
    difficulty: 'hard',
    topic: 'Lists',
    description: 'Exercise 2.8 of *Programming and Proving*. `intersperse a [x1, …, xn] = [x1, a, x2, a, …, a, xn]`. Prove `map f (intersperse a xs) = intersperse (f a) (map f xs)`. Hint: use computation induction (`rule: intersperse.induct`).',
    starter: thy(
      'Intersperse',
      `fun intersperse :: "'a ⇒ 'a list ⇒ 'a list" where
  "intersperse a [] = []"
| "intersperse a [x] = [x]"
| "intersperse a (x # y # zs) = x # a # intersperse a (y # zs)"

lemma map_intersperse: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  sorry`,
    ),
    solution: thy(
      'Intersperse',
      `fun intersperse :: "'a ⇒ 'a list ⇒ 'a list" where
  "intersperse a [] = []"
| "intersperse a [x] = [x]"
| "intersperse a (x # y # zs) = x # a # intersperse a (y # zs)"

lemma map_intersperse: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  by (induction a xs rule: intersperse.induct) auto`,
    ),
    hints: ['The recursion is not structural in a simple way, so use the induction rule generated by `fun`.', '`by (induction a xs rule: intersperse.induct) auto`'],
    required: ['map_intersperse'],
  },
  {
    id: 'itadd',
    title: 'Tail-recursive addition',
    difficulty: 'hard',
    topic: 'Natural numbers',
    description: 'Exercise 2.9 of *Programming and Proving*: prove that the tail-recursive `itadd` agrees with `+`. Generalisation is needed again.',
    starter: thy(
      'Itadd',
      `fun itadd :: "nat ⇒ nat ⇒ nat" where
  "itadd 0 n = n"
| "itadd (Suc m) n = itadd m (Suc n)"

lemma itadd_add: "itadd m n = m + n"
  sorry`,
    ),
    solution: thy(
      'Itadd',
      `fun itadd :: "nat ⇒ nat ⇒ nat" where
  "itadd 0 n = n"
| "itadd (Suc m) n = itadd m (Suc n)"

lemma itadd_add: "itadd m n = m + n"
  by (induction m arbitrary: n) auto`,
    ),
    hints: ['The second argument changes in the recursive call, so it must be `arbitrary`.'],
    required: ['itadd_add'],
  },
  // ---------------- Datatypes ----------------
  {
    id: 'mirror',
    title: 'Mirroring trees',
    difficulty: 'easy',
    topic: 'Datatypes',
    description: 'Define binary trees and the mirror function, and prove that mirroring twice gives back the original tree.',
    starter: thy(
      'Mirror',
      `datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree ⇒ 'a tree" where
  "mirror Tip = Tip"
| "mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma mirror_mirror: "mirror (mirror t) = t"
  sorry`,
    ),
    solution: thy(
      'Mirror',
      `datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree ⇒ 'a tree" where
  "mirror Tip = Tip"
| "mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma mirror_mirror: "mirror (mirror t) = t"
  by (induction t) auto`,
    ),
    hints: ['Structural induction on the tree `t` gives two IHs in the `Node` case.'],
    required: ['mirror_mirror'],
  },
  {
    id: 'tree-contents',
    title: 'Tree contents and sum',
    difficulty: 'medium',
    topic: 'Datatypes',
    description: 'Exercise 2.6: define `contents` (in-order list of the elements) and `sum_tree`, and prove `sum_tree t = sum_list (contents t)`.',
    starter: thy(
      'TreeSum',
      `datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree ⇒ 'a list" where
  "contents Tip = []"
| "contents (Node l a r) = contents l @ a # contents r"

fun sum_tree :: "nat tree ⇒ nat" where
  "sum_tree Tip = 0"
| "sum_tree (Node l a r) = sum_tree l + a + sum_tree r"

lemma sum_contents: "sum_tree t = sum_list (contents t)"
  sorry`,
    ),
    solution: thy(
      'TreeSum',
      `datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree ⇒ 'a list" where
  "contents Tip = []"
| "contents (Node l a r) = contents l @ a # contents r"

fun sum_tree :: "nat tree ⇒ nat" where
  "sum_tree Tip = 0"
| "sum_tree (Node l a r) = sum_tree l + a + sum_tree r"

lemma sum_contents: "sum_tree t = sum_list (contents t)"
  by (induction t) auto`,
    ),
    hints: ['`sum_list_append` is a library simp rule, so `auto` knows `sum_list (xs @ ys) = sum_list xs + sum_list ys`.'],
    required: ['sum_contents'],
  },
  {
    id: 'tree-size',
    title: 'Counting nodes and leaves',
    difficulty: 'medium',
    topic: 'Datatypes',
    description: 'In every binary tree, the number of leaves is one more than the number of nodes.',
    starter: thy(
      'TreeSize',
      `datatype tree = Leaf | Node tree tree

fun leaves :: "tree ⇒ nat" where
  "leaves Leaf = 1"
| "leaves (Node l r) = leaves l + leaves r"

fun nodes :: "tree ⇒ nat" where
  "nodes Leaf = 0"
| "nodes (Node l r) = nodes l + nodes r + 1"

lemma leaves_nodes: "leaves t = nodes t + 1"
  sorry`,
    ),
    solution: thy(
      'TreeSize',
      `datatype tree = Leaf | Node tree tree

fun leaves :: "tree ⇒ nat" where
  "leaves Leaf = 1"
| "leaves (Node l r) = leaves l + leaves r"

fun nodes :: "tree ⇒ nat" where
  "nodes Leaf = 0"
| "nodes (Node l r) = nodes l + nodes r + 1"

lemma leaves_nodes: "leaves t = nodes t + 1"
  by (induction t) auto`,
    ),
    hints: ['Induction on `t`; the arithmetic in the `Node` case is linear.'],
    required: ['leaves_nodes'],
  },
  {
    id: 'expr-eval',
    title: 'Arithmetic expressions',
    difficulty: 'hard',
    topic: 'Datatypes',
    description: 'A tiny compiler-correctness style exercise. Expressions are evaluated directly by `eval`; `simp_expr` removes additions of zero. Prove that simplification preserves the value.',
    starter: thy(
      'Expr',
      `datatype expr = N nat | V nat | Plus expr expr

fun eval :: "expr ⇒ (nat ⇒ nat) ⇒ nat" where
  "eval (N n) s = n"
| "eval (V x) s = s x"
| "eval (Plus a b) s = eval a s + eval b s"

fun plus0 :: "expr ⇒ expr ⇒ expr" where
  "plus0 (N 0) e = e"
| "plus0 e (N 0) = e"
| "plus0 a b = Plus a b"

fun simp_expr :: "expr ⇒ expr" where
  "simp_expr (N n) = N n"
| "simp_expr (V x) = V x"
| "simp_expr (Plus a b) = plus0 (simp_expr a) (simp_expr b)"

lemma eval_plus0: "eval (plus0 a b) s = eval a s + eval b s"
  sorry

theorem eval_simp_expr: "eval (simp_expr e) s = eval e s"
  sorry`,
    ),
    solution: thy(
      'Expr',
      `datatype expr = N nat | V nat | Plus expr expr

fun eval :: "expr ⇒ (nat ⇒ nat) ⇒ nat" where
  "eval (N n) s = n"
| "eval (V x) s = s x"
| "eval (Plus a b) s = eval a s + eval b s"

fun plus0 :: "expr ⇒ expr ⇒ expr" where
  "plus0 (N 0) e = e"
| "plus0 e (N 0) = e"
| "plus0 a b = Plus a b"

fun simp_expr :: "expr ⇒ expr" where
  "simp_expr (N n) = N n"
| "simp_expr (V x) = V x"
| "simp_expr (Plus a b) = plus0 (simp_expr a) (simp_expr b)"

lemma eval_plus0: "eval (plus0 a b) s = eval a s + eval b s"
  by (induction a b rule: plus0.induct) auto

theorem eval_simp_expr: "eval (simp_expr e) s = eval e s"
  by (induction e) (auto simp add: eval_plus0)`,
    ),
    hints: ['`plus0` has overlapping patterns; use its computation induction rule: `induction a b rule: plus0.induct`.', 'For the theorem, structural induction on `e` plus the lemma `eval_plus0`.'],
    required: ['eval_plus0', 'eval_simp_expr'],
  },
  {
    id: 'option-map',
    title: 'Options',
    difficulty: 'easy',
    topic: 'Datatypes',
    description: 'Define a map function on options and prove a composition law. Use `cases` for case analysis on an option.',
    starter: thy(
      'OptionMap',
      `fun omap :: "('a ⇒ 'b) ⇒ 'a option ⇒ 'b option" where
  "omap f None = None"
| "omap f (Some x) = Some (f x)"

lemma omap_comp: "omap f (omap g x) = omap (λy. f (g y)) x"
  sorry`,
    ),
    solution: thy(
      'OptionMap',
      `fun omap :: "('a ⇒ 'b) ⇒ 'a option ⇒ 'b option" where
  "omap f None = None"
| "omap f (Some x) = Some (f x)"

lemma omap_comp: "omap f (omap g x) = omap (λy. f (g y)) x"
  by (cases x) auto`,
    ),
    hints: ['No induction needed: `by (cases x) auto`.'],
    required: ['omap_comp'],
  },
  // ---------------- Structured proofs ----------------
  {
    id: 'isar-induction',
    title: 'Induction in Isar',
    difficulty: 'medium',
    topic: 'Structured proofs',
    description: 'Write a structured proof by induction. The skeleton is given: fill in the `sorry`s.',
    starter: thy(
      'IsarInduct',
      `fun sum_upto :: "nat ⇒ nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = Suc n + sum_upto n"

lemma "sum_upto n = n * (n + 1) div 2"
proof (induction n)
  case 0
  show ?case sorry
next
  case (Suc n)
  thus ?case sorry
qed`,
    ),
    solution: thy(
      'IsarInduct',
      `fun sum_upto :: "nat ⇒ nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = Suc n + sum_upto n"

lemma sum_formula: "sum_upto n = n * (n + 1) div 2"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  thus ?case by simp
qed`,
    ),
    hints: ['`?case` is the goal for the current case.', 'Both cases go through `by simp`; `thus` chains the induction hypothesis.'],
    required: [],
  },
  {
    id: 'isar-calc',
    title: 'Calculational reasoning',
    difficulty: 'medium',
    topic: 'Structured proofs',
    description: 'Complete the chain of equations with `also` / `finally`. Each step should be justified by a short method.',
    starter: thy(
      'Calc',
      `lemma calc_example:
  fixes a b :: nat
  shows "(a + b) * (a + b) = a * a + 2 * a * b + b * b"
proof -
  have "(a + b) * (a + b) = a * (a + b) + b * (a + b)" sorry
  also have "... = a * a + a * b + b * a + b * b" sorry
  also have "... = a * a + 2 * a * b + b * b" sorry
  finally show ?thesis .
qed`,
    ),
    solution: thy(
      'Calc',
      `lemma calc_example:
  fixes a b :: nat
  shows "(a + b) * (a + b) = a * a + 2 * a * b + b * b"
proof -
  have "(a + b) * (a + b) = a * (a + b) + b * (a + b)" by (simp add: distrib_right)
  also have "... = a * a + a * b + b * a + b * b" by (simp add: distrib_left)
  also have "... = a * a + 2 * a * b + b * b" by simp
  finally show ?thesis .
qed`,
    ),
    hints: ['`...` refers to the right-hand side of the previous line.', 'The steps follow from distributivity: `simp add: distrib_left distrib_right`, or `algebra_simps`.', '`finally show ?thesis .` closes the chain.'],
    required: ['calc_example'],
  },
  {
    id: 'isar-exists',
    title: 'Existential witnesses',
    difficulty: 'medium',
    topic: 'Structured proofs',
    description: 'Use `obtain` to get a witness from an existential assumption, and provide a witness for the conclusion.',
    starter: thy(
      'Exists',
      `lemma ex_double:
  assumes "∃k. n = 2 * k"
  shows "∃m. n + 2 = 2 * m"
proof -
  from assms obtain k where "n = 2 * k" sorry
  hence "n + 2 = 2 * (k + 1)" sorry
  thus ?thesis sorry
qed`,
    ),
    solution: thy(
      'Exists',
      `lemma ex_double:
  assumes "∃k. n = 2 * k"
  shows "∃m. n + 2 = 2 * m"
proof -
  from assms obtain k where "n = 2 * k" by blast
  hence "n + 2 = 2 * (k + 1)" by simp
  thus ?thesis by blast
qed`,
    ),
    hints: ['`obtain ... by blast` (or `by auto`).', 'The final step: the witness is `k + 1`, and `blast` finds it from the previous fact.'],
    required: ['ex_double'],
  },
  // ---------------- Inductive predicates ----------------
  {
    id: 'ev-induct',
    title: 'Even numbers (inductive)',
    difficulty: 'medium',
    topic: 'Inductive predicates',
    description: 'The inductive predicate `ev` characterises even numbers. Prove that it agrees with the recursive `evn` in one direction using rule induction.',
    starter: thy(
      'Ev',
      `inductive ev :: "nat ⇒ bool" where
  ev0: "ev 0"
| evSS: "ev n ⟹ ev (Suc (Suc n))"

fun evn :: "nat ⇒ bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma ev_evn: "ev m ⟹ evn m"
  sorry

lemma ev_four: "ev 4"
  sorry`,
    ),
    solution: thy(
      'Ev',
      `inductive ev :: "nat ⇒ bool" where
  ev0: "ev 0"
| evSS: "ev n ⟹ ev (Suc (Suc n))"

fun evn :: "nat ⇒ bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma ev_evn: "ev m ⟹ evn m"
  by (induction rule: ev.induct) auto

lemma ev_four: "ev 4"
  apply (rule evSS)
  apply (rule evSS)
  apply (rule ev0)
  done`,
    ),
    hints: ['Rule induction: `apply (induction rule: ev.induct)`.', '`4` is `Suc (Suc (Suc (Suc 0)))`, so apply `evSS` twice and then `ev0`.'],
    required: ['ev_evn', 'ev_four'],
  },
  {
    id: 'evn-ev',
    title: 'Even numbers: the other direction',
    difficulty: 'hard',
    topic: 'Inductive predicates',
    description: 'Prove `evn n ⟹ ev n`. Here rule induction on `ev` is useless (we do not have `ev n` yet!) — use computation induction on `evn` instead.',
    starter: thy(
      'EvnEv',
      `inductive ev :: "nat ⇒ bool" where
  ev0: "ev 0"
| evSS: "ev n ⟹ ev (Suc (Suc n))"

fun evn :: "nat ⇒ bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma evn_ev: "evn n ⟹ ev n"
  sorry`,
    ),
    solution: thy(
      'EvnEv',
      `inductive ev :: "nat ⇒ bool" where
  ev0: "ev 0"
| evSS: "ev n ⟹ ev (Suc (Suc n))"

fun evn :: "nat ⇒ bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma evn_ev: "evn n ⟹ ev n"
  by (induction n rule: evn.induct) (simp_all add: ev0 evSS)`,
    ),
    hints: ['`induction n rule: evn.induct` gives one case per equation of `evn`.', 'Close the cases with `simp_all add: ev0 evSS`.'],
    required: ['evn_ev'],
  },
  {
    id: 'star',
    title: 'Reflexive transitive closure',
    difficulty: 'hard',
    topic: 'Inductive predicates',
    description: 'Define the reflexive transitive closure of a fixed relation `r` on natural numbers and prove that it is transitive.',
    starter: thy(
      'Star',
      `consts r :: "nat ⇒ nat ⇒ bool"

inductive star :: "nat ⇒ nat ⇒ bool" where
  refl: "star x x"
| step: "r x y ⟹ star y z ⟹ star x z"

lemma star_trans: "star x y ⟹ star y z ⟹ star x z"
  sorry`,
    ),
    solution: thy(
      'Star',
      `consts r :: "nat ⇒ nat ⇒ bool"

inductive star :: "nat ⇒ nat ⇒ bool" where
  refl: "star x x"
| step: "r x y ⟹ star y z ⟹ star x z"

lemma star_trans: "star x y ⟹ star y z ⟹ star x z"
  apply (induction rule: star.induct)
   apply assumption
  apply (rule step)
   apply assumption
  apply simp
  done`,
    ),
    hints: ['Rule induction on the first premise `star x y`.', 'In the `step` case, apply the `step` rule and use the induction hypothesis.', 'Alternatively: `by (induction rule: star.induct) (auto intro: step)`.'],
    required: ['star_trans'],
  },
  // ---------------- Sets ----------------
  {
    id: 'set-basics',
    title: 'Set algebra',
    difficulty: 'easy',
    topic: 'Sets',
    description: 'Prove some basic set identities. `blast` is the tool of choice for set theory.',
    starter: thy(
      'SetBasics',
      `lemma inter_union: "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)"
  sorry

lemma subset_trans': "A ⊆ B ⟹ B ⊆ C ⟹ A ⊆ C"
  sorry`,
    ),
    solution: thy(
      'SetBasics',
      `lemma inter_union: "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)"
  by blast

lemma subset_trans': "A ⊆ B ⟹ B ⊆ C ⟹ A ⊆ C"
  by blast`,
    ),
    hints: ['`by blast` for both.'],
    required: ['inter_union', "subset_trans'"],
  },
  {
    id: 'set-list',
    title: 'Elements of a list',
    difficulty: 'medium',
    topic: 'Sets',
    description: 'Prove that the elements of a reversed list are the same as those of the original list, using your own `elems` function.',
    starter: thy(
      'SetList',
      `fun elems :: "'a list ⇒ 'a set" where
  "elems [] = {}"
| "elems (x # xs) = {x} ∪ elems xs"

lemma elems_app: "elems (xs @ ys) = elems xs ∪ elems ys"
  sorry

lemma elems_rev: "elems (rev xs) = elems xs"
  sorry`,
    ),
    solution: thy(
      'SetList',
      `fun elems :: "'a list ⇒ 'a set" where
  "elems [] = {}"
| "elems (x # xs) = {x} ∪ elems xs"

lemma elems_app: "elems (xs @ ys) = elems xs ∪ elems ys"
  by (induction xs) auto

lemma elems_rev: "elems (rev xs) = elems xs"
  by (induction xs) (auto simp add: elems_app)`,
    ),
    hints: ['Induction on `xs` for both; `auto` handles the set reasoning.'],
    required: ['elems_app', 'elems_rev'],
  },
];
