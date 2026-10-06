theory Features imports Main begin

type_synonym point = "nat × nat"

definition swap :: "point ⇒ point" where
  "swap p = (snd p, fst p)"

lemma "swap (swap p) = p" by (simp add: swap_def)

definition sq :: "nat ⇒ nat" where "sq n = n * n"
lemma "sq 3 = 9" by (simp add: sq_def)
lemma "sq (a + b) = sq a + 2 * a * b + sq b" unfolding sq_def by algebra

primrec len :: "'a list ⇒ nat" where
  "len [] = 0"
| "len (x # xs) = 1 + len xs"
lemma "len xs = length xs" by (induct xs) simp_all

fun fib :: "nat ⇒ nat" where
  "fib 0 = 0"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"
value "fib 10"
lemma "fib (Suc n) > 0 ∨ n = 0" oops
lemma fib_pos: "0 < fib (Suc n)" by (induction n rule: fib.induct) auto

fun lookup :: "('a × 'b) list ⇒ 'a ⇒ 'b option" where
  "lookup [] k = None"
| "lookup ((a, b) # ps) k = (if a = k then Some b else lookup ps k)"
value "lookup [(1::nat, True), (2, False)] 2"

fun sumpairs :: "(nat × nat) list ⇒ nat" where
  "sumpairs [] = 0"
| "sumpairs ((a, b) # ps) = a + b + sumpairs ps"

value "let x = (3::nat) in x * x"
value "(λ(a, b). a + b) (2::nat, 3)"
value "case Some (3::nat) of None ⇒ 0 | Some n ⇒ n + 1"

lemma "(case xs of [] ⇒ 0 | y # ys ⇒ length xs) = length xs"
  by (cases xs) auto

lemma "∀x ∈ set [1, 2, 3 :: nat]. x > 0" by simp

lemma "max a b ≥ (a::nat)" by simp
lemma "min a b ≤ (a::nat)" by arith

lemma "(n::nat) > 0 ⟹ n - 1 + 1 = n" by simp

lemma "(x::int) ≤ x * x ∨ True" by simp
lemma "¬ (∃n::nat. n < 0)" by simp

lemma "xs ≠ [] ⟹ length xs > 0" by (cases xs) auto

lemma
  fixes xs :: "nat list"
  assumes "sorted xs" "x ∈ set xs"
  shows "x ≥ hd xs"
  using assms by (induction xs) auto

lemma "map (λx. x + 1) [1, 2, 3] = [2, 3, (4::nat)]" by simp

lemma "rev [a, b] = [b, a]" by simp

lemma "length (concat [[a], [b, c]]) = 3" by simp

lemma "foldr (+) [1, 2, 3] (0::nat) = 6" by simp

lemma "A ⟹ B ⟹ A ∧ B"
  apply (intro conjI)
   apply assumption+
  done

lemma "P x ⟹ ∃y. P y" by (rule exI)

lemma "(∀x. P x) ⟹ P a" by (erule allE)

lemma "P ∧ Q ⟹ Q"
  apply (drule conjunct2)
  apply assumption
  done

lemma "⟦ x = y; y = z ⟧ ⟹ x = z" by (rule trans)

lemma "a = b ⟹ f a = f b" by simp

lemma assumes "x = 2" shows "x + x = (4::nat)" using assms by simp

lemma "length [x ← xs. P x] ≤ length xs" by simp
value "[x * 2. x ← [1, 2, 3::nat]]"
lemma "True" by simp

end
