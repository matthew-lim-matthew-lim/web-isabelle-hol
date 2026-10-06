// Example theories available from the IDE's "Examples" menu.

export const DEFAULT_THEORY = `theory Scratch
  imports Main
begin

(* Welcome to the Isabelle/HOL IDE.
   Put the cursor on a command to see the proof state in the Output panel.
   Try:  type "==>" and it becomes ⟹ ; type \\forall and pick from the list. *)

fun sum_upto :: "nat ⇒ nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = Suc n + sum_upto n"

value "sum_upto 10"

lemma sum_upto_formula: "2 * sum_upto n = n * (n + 1)"
  apply (induction n)
   apply simp
  apply simp
  done

end
`;

export const EXAMPLES: { name: string; text: string }[] = [
  { name: 'Scratch', text: DEFAULT_THEORY },
  {
    name: 'Lists',
    text: `theory Lists
  imports Main
begin

fun app :: "'a list ⇒ 'a list ⇒ 'a list" where
  "app [] ys = ys"
| "app (x # xs) ys = x # app xs ys"

fun rev2 :: "'a list ⇒ 'a list" where
  "rev2 [] = []"
| "rev2 (x # xs) = app (rev2 xs) [x]"

value "rev2 [True, False]"

lemma app_Nil2 [simp]: "app xs [] = xs"
  by (induction xs) auto

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  by (induction xs) auto

lemma rev_app [simp]: "rev2 (app xs ys) = app (rev2 ys) (rev2 xs)"
  by (induction xs) auto

theorem rev_rev: "rev2 (rev2 xs) = xs"
  by (induction xs) auto

end
`,
  },
  {
    name: 'Trees',
    text: `theory Trees
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree ⇒ 'a tree" where
  "mirror Tip = Tip"
| "mirror (Node l a r) = Node (mirror r) a (mirror l)"

fun contents :: "'a tree ⇒ 'a list" where
  "contents Tip = []"
| "contents (Node l a r) = contents l @ a # contents r"

lemma mirror_mirror: "mirror (mirror t) = t"
proof (induction t)
  case Tip
  show ?case by simp
next
  case (Node l a r)
  thus ?case by simp
qed

lemma contents_mirror: "contents (mirror t) = rev (contents t)"
  by (induction t) auto

end
`,
  },
  {
    name: 'Isar',
    text: `theory IsarDemo
  imports Main
begin

lemma
  assumes "∀x. P x ⟶ Q x" and "P a"
  shows "∃x. Q x"
proof -
  from assms have "Q a" by blast
  thus ?thesis by blast
qed

lemma
  fixes a b :: nat
  shows "(a + b) * (a + b) = a * a + 2 * a * b + b * b"
proof -
  have "(a + b) * (a + b) = a * (a + b) + b * (a + b)" by (simp add: distrib_right)
  also have "... = a * a + a * b + b * a + b * b" by (simp add: distrib_left)
  also have "... = a * a + 2 * a * b + b * b" by simp
  finally show ?thesis .
qed

end
`,
  },
  {
    name: 'Inductive',
    text: `theory EvenOdd
  imports Main
begin

inductive ev :: "nat ⇒ bool" where
  ev0: "ev 0"
| evSS: "ev n ⟹ ev (Suc (Suc n))"

fun evn :: "nat ⇒ bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma ev_evn: "ev m ⟹ evn m"
  by (induction rule: ev.induct) auto

lemma evn_ev: "evn n ⟹ ev n"
  by (induction n rule: evn.induct) (simp_all add: ev0 evSS)

lemma "¬ ev (Suc 0)"
proof
  assume "ev (Suc 0)"
  then show False by cases
qed

end
`,
  },
  {
    name: 'Counterexamples',
    text: `theory Counterexamples
  imports Main
begin

(* quickcheck searches for counterexamples before you try to prove something false *)
lemma "rev xs = xs"
  quickcheck
  oops

lemma "length (xs @ ys) = length xs + length ys"
  quickcheck
  try
  oops

end
`,
  },
];
