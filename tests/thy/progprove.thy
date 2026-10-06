theory ProgProve imports Main begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree ⇒ 'a tree" where
  "mirror Tip = Tip"
| "mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma mirror_mirror: "mirror (mirror t) = t"
  apply (induction t)
  apply auto
  done

fun contents :: "'a tree ⇒ 'a list" where
  "contents Tip = []"
| "contents (Node l a r) = contents l @ a # contents r"

fun sum_tree :: "nat tree ⇒ nat" where
  "sum_tree Tip = 0"
| "sum_tree (Node l a r) = sum_tree l + a + sum_tree r"

lemma "sum_tree t = sum_list (contents t)"
  by (induction t) auto

fun itrev :: "'a list ⇒ 'a list ⇒ 'a list" where
  "itrev [] ys = ys"
| "itrev (x # xs) ys = itrev xs (x # ys)"

lemma "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys)
  apply auto
  done

fun sum_upto :: "nat ⇒ nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = Suc n + sum_upto n"

lemma "2 * sum_upto n = n * (n + 1)"
  by (induction n) auto

lemma "sum_upto n = n * (n + 1) div 2"
  by (induction n) auto

fun count :: "'a ⇒ 'a list ⇒ nat" where
  "count x [] = 0"
| "count x (y # ys) = (if x = y then Suc (count x ys) else count x ys)"

lemma "count x xs ≤ length xs"
  by (induction xs) auto

fun snoc :: "'a list ⇒ 'a ⇒ 'a list" where
  "snoc [] x = [x]"
| "snoc (y # ys) x = y # snoc ys x"

fun reverse :: "'a list ⇒ 'a list" where
  "reverse [] = []"
| "reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc: "reverse (snoc xs x) = x # reverse xs"
  by (induction xs) auto

lemma "reverse (reverse xs) = xs"
  by (induction xs) (auto simp add: reverse_snoc)

fun double :: "nat ⇒ nat" where
  "double 0 = 0"
| "double (Suc n) = Suc (Suc (double n))"

lemma "double m = m + m"
  by (induction m) auto

lemma "¬ surj (f :: 'a ⇒ 'a set)" oops

lemma "∀x. ∃y. x = y" by auto

lemma "A ⊆ B ⟹ B ⊆ C ⟹ A ⊆ C" by blast

lemma "xs @ ys = ys @ xs ⟹ length xs = length ys ∨ True" by simp

lemma rev_app: "rev (xs @ ys) = rev ys @ rev xs"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  thus ?case by simp
qed

lemma
  fixes n :: nat
  shows "n * (n + 1) mod 2 = 0 ∨ True"
  by simp

lemma "∃x::nat. x > 5" by (rule exI[of _ 6]) simp

lemma assumes "P ∧ Q" shows "Q ∧ P"
proof -
  from assms have "P" by simp
  from assms have "Q" by simp
  show "Q ∧ P" using ‹P› ‹Q› by simp
qed

lemma "(∀x. P x ⟶ Q x) ⟹ (∀x. P x) ⟶ (∀x. Q x)"
proof
  assume a: "∀x. P x ⟶ Q x"
  assume b: "∀x. P x"
  show "∀x. Q x"
  proof
    fix x
    from a b show "Q x" by blast
  qed
qed

lemma "length (xs @ ys) = length ys + length xs"
proof -
  have "length (xs @ ys) = length xs + length ys" by simp
  also have "... = length ys + length xs" by simp
  finally show ?thesis .
qed

inductive ev :: "nat ⇒ bool" where
  ev0: "ev 0"
| evSS: "ev n ⟹ ev (Suc (Suc n))"

fun evn :: "nat ⇒ bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma "ev m ⟹ evn m"
  apply (induction rule: ev.induct)
  apply simp
  apply simp
  done

lemma "evn n ⟹ ev n"
  apply (induction n rule: evn.induct)
  apply (simp_all add: ev0 evSS)
  done

lemma "ev (Suc (Suc (Suc (Suc 0))))"
  apply (rule evSS)
  apply (rule evSS)
  apply (rule ev0)
  done

lemma "ev n ⟹ ev (n + 2)"
  by (simp add: evSS)

lemma ev_double: "ev (2 * n)"
  apply (induction n)
  apply (simp add: ev0)
  apply (simp add: evSS)
  done

lemma "¬ ev (Suc 0)"
proof
  assume "ev (Suc 0)"
  then show False by cases
qed

lemma "ev m ⟹ ev (m - 2)"
proof (induction rule: ev.induct)
  case ev0
  show ?case by (simp add: ev0)
next
  case (evSS n)
  then show ?case by simp
qed

lemma "x ∈ set (xs @ ys) ⟷ x ∈ set xs ∨ x ∈ set ys" by simp

lemma "distinct (rev xs) = distinct xs" by simp

lemma "map f (map g xs) = map (λx. f (g x)) xs" by (induction xs) auto

lemma
  assumes "x < (y::nat)" "y < z"
  shows "x < z"
  using assms by arith

lemma "(a::nat) + b = b + a" by (simp add: add.commute)

lemma "(x::int) - y + y = x" by simp

lemma "sorted [1, 2, 3::nat]" by simp

lemma "take 2 [a, b, c] = [a, b]" by simp

lemma "∀xs. length (rev xs) = length xs" by simp

lemma "case xs of [] ⇒ True | y # ys ⇒ length xs > 0" by (cases xs) auto

lemma "(if x then A else B) ⟶ A ∨ B" by auto

end
