theory Variants imports Main begin

consts r :: "nat ⇒ nat ⇒ bool"
inductive star :: "nat ⇒ nat ⇒ bool" where
  refl: "star x x"
| step: "r x y ⟹ star y z ⟹ star x z"

lemma star_trans: "star x y ⟹ star y z ⟹ star x z"
  by (induction rule: star.induct) (auto intro: step)

lemma star_trans2: "star x y ⟹ star y z ⟹ star x z"
proof (induction rule: star.induct)
  case (refl x)
  then show ?case .
next
  case (step x y z')
  then show ?case by (metis star.step)
qed

lemma "A ∧ B ⟶ B ∧ A" by blast
lemma "A ∧ B ⟶ B ∧ A" by auto
lemma "A ∧ B ⟶ B ∧ A"
proof
  assume "A ∧ B"
  then show "B ∧ A" by simp
qed
lemma "A ∨ B ⟶ B ∨ A" by auto
lemma "(∃x. ∀y. P x y) ⟶ (∀y. ∃x. P x y)" by blast
lemma "(∃x. ∀y. P x y) ⟶ (∀y. ∃x. P x y)" by auto

fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"
lemma add_0_right: "add m 0 = m" by (induct m) simp_all
lemma add_Suc_right[simp]: "add m (Suc n) = Suc (add m n)"
  apply (induct m)
  apply simp
  apply simp
  done
lemma "add m n = add n m"
  apply (induct m)
   apply (simp add: add_0_right)
  apply simp
  done
lemma add_comm2: "add m n = add n m"
proof (induction m)
  case 0
  then show ?case by (simp add: add_0_right)
next
  case (Suc m)
  then show ?case by simp
qed

lemma "(a + b) * (a + b) = a * a + 2 * a * b + b * (b::nat)" by (simp add: algebra_simps)
lemma "(a + b) * (a + b) = a * a + 2 * a * b + b * (b::nat)" by algebra
lemma "(a + b) * (a + b) = a * a + 2 * a * b + b * (b::nat)" by simp

lemma "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)" by auto
lemma "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)" by fast
lemma "x ∈ A ⟹ A ⊆ B ⟹ x ∈ B" by auto

fun itrev :: "'a list ⇒ 'a list ⇒ 'a list" where
  "itrev [] ys = ys"
| "itrev (x # xs) ys = itrev xs (x # ys)"
lemma "itrev xs ys = rev xs @ ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by simp
qed
lemma "itrev xs ys = rev xs @ ys"
  apply (induct xs arbitrary: ys)
   apply simp_all
  done

lemma "∃n::nat. n * n = 16" by (rule exI[where x = 4]) simp
lemma "∃n::nat. n + 3 = 5" by (rule_tac x = 2 in exI) simp
lemma "∃xs. length xs = 2" by (rule exI[of _ "[a, b]"]) simp

lemma "∀x::nat. x < x + 1" by simp
lemma "(n::nat) mod 2 = 0 ∨ n mod 2 = 1" by arith
lemma "(n::nat) ≠ 0 ⟹ ∃m. n = Suc m" by (cases n) auto
lemma "xs ≠ [] ⟹ hd xs # tl xs = xs" by (cases xs) auto
lemma "length (filter P xs) ≤ length xs" by (induction xs) auto
lemma "rev (map f xs) = map f (rev xs)" by (induction xs) auto
lemma "set (rev xs) = set xs" by simp
lemma "sum_list (replicate n (1::nat)) = n" by (induction n) auto
lemma "take n xs @ drop n xs = xs" by simp
lemma "length (replicate n x) = n" by simp
lemma "distinct [1, 2, 3::nat]" by simp
lemma "[1..<4] = [1, 2, 3]" by simp

end
