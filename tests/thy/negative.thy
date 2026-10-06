theory Negative imports Main begin
lemma "rev xs = xs" by simp
lemma "rev xs = xs" by auto
lemma "(x::nat) + 1 = x" by simp
lemma "∃x. ∀y. x = y" by blast
lemma "∃x::nat. ∀y. x = y" by auto
lemma "P ∨ Q ⟹ P" by auto
lemma "P ∨ Q ⟹ P" by blast
lemma "length xs = length ys" by auto
lemma "(x::nat) - 1 + 1 = x" by arith
lemma "(x::nat) - 1 + 1 = x" by simp
lemma "(a::nat) * b = a + b" by simp
lemma "xs @ ys = ys @ xs" by (induction xs) auto
lemma "(∀x. ∃y. P x y) ⟹ ∃y. ∀x. P x y" by blast
lemma "(∀x. ∃y. P x y) ⟹ ∃y. ∀x. P x y" by auto
lemma "(∀x. ∃y. P x y) ⟹ ∃y. ∀x. P x y" by metis
lemma "(x::int) * x > 0" by simp
lemma "(x::int) * x > 0" by arith
lemma "A ⊆ B ⟹ B ⊆ A" by blast
lemma "map f xs = xs" by simp
lemma "sorted xs" by simp
lemma "distinct xs" by auto
lemma "(n::nat) div 2 * 2 = n" by simp
lemma "(n::nat) div 2 * 2 = n" by arith
lemma "False" by auto
lemma "x = y" by force
lemma "f x = f y" by fastforce
lemma "Suc n = n" by simp
lemma "take n xs = xs" by auto
lemma "(n::nat) < m ⟹ n + 1 < m" by arith
lemma "hd (xs @ ys) = hd xs" by simp
lemma "length [x ← xs. undefined_thing +] ≤ 0"
  apply simp
  done
lemma "(1::nat) = 2" by simp
end
