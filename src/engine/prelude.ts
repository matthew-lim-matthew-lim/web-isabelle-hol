// The "Main" theory of the web edition: datatypes, functions and the standard lemma library.
// Lemmas here are trusted (proved by "sorry"); tests re-prove many of them with the engine itself.

export const PRELUDE = String.raw`
section ‹Logic›

lemma TrueI: "True" sorry
lemma refl: "t = t" sorry
lemma sym: "s = t ⟹ t = s" sorry
lemma not_sym: "t ≠ s ⟹ s ≠ t" sorry
lemma trans: "⟦r = s; s = t⟧ ⟹ r = t" sorry
lemma subst: "⟦s = t; P s⟧ ⟹ P t" sorry
lemma ssubst: "⟦t = s; P s⟧ ⟹ P t" sorry
lemma arg_cong: "x = y ⟹ f x = f y" sorry
lemma fun_cong: "f = g ⟹ f x = g x" sorry
lemma cong: "⟦f = g; x = y⟧ ⟹ f x = g y" sorry
lemma ext: "(⋀x. f x = g x) ⟹ f = g" sorry
lemma conjI: "⟦P; Q⟧ ⟹ P ∧ Q" sorry
lemma conjE: "⟦P ∧ Q; ⟦P; Q⟧ ⟹ R⟧ ⟹ R" sorry
lemma conjunct1: "P ∧ Q ⟹ P" sorry
lemma conjunct2: "P ∧ Q ⟹ Q" sorry
lemma conjD1: "P ∧ Q ⟹ P" sorry
lemma conjD2: "P ∧ Q ⟹ Q" sorry
lemma disjI1: "P ⟹ P ∨ Q" sorry
lemma disjI2: "Q ⟹ P ∨ Q" sorry
lemma disjE: "⟦P ∨ Q; P ⟹ R; Q ⟹ R⟧ ⟹ R" sorry
lemma disjCI: "(¬ Q ⟹ P) ⟹ P ∨ Q" sorry
lemma impI: "(P ⟹ Q) ⟹ P ⟶ Q" sorry
lemma impE: "⟦P ⟶ Q; P; Q ⟹ R⟧ ⟹ R" sorry
lemma mp: "⟦P ⟶ Q; P⟧ ⟹ Q" sorry
lemma impD: "⟦P ⟶ Q; P⟧ ⟹ Q" sorry
lemma notI: "(P ⟹ False) ⟹ ¬ P" sorry
lemma notE: "⟦¬ P; P⟧ ⟹ R" sorry
lemma notnotD: "¬ ¬ P ⟹ P" sorry
lemma iffI: "⟦P ⟹ Q; Q ⟹ P⟧ ⟹ P = Q" sorry
lemma iffD1: "⟦Q = P; Q⟧ ⟹ P" sorry
lemma iffD2: "⟦P = Q; Q⟧ ⟹ P" sorry
lemma iffE: "⟦P = Q; ⟦P ⟶ Q; Q ⟶ P⟧ ⟹ R⟧ ⟹ R" sorry
lemma FalseE: "False ⟹ P" sorry
lemma False_neq_True: "False = True ⟹ P" sorry
lemma allI: "(⋀x. P x) ⟹ ∀x. P x" sorry
lemma allE: "⟦∀x. P x; P x ⟹ R⟧ ⟹ R" sorry
lemma spec: "∀x. P x ⟹ P x" sorry
lemma exI: "P x ⟹ ∃x. P x" sorry
lemma exE: "⟦∃x. P x; ⋀x. P x ⟹ Q⟧ ⟹ Q" sorry
lemma ex1I: "⟦P a; ⋀x. P x ⟹ x = a⟧ ⟹ ∃!x. P x" sorry
lemma ccontr: "(¬ P ⟹ False) ⟹ P" sorry
lemma classical: "(¬ P ⟹ P) ⟹ P" sorry
lemma excluded_middle: "¬ P ∨ P" sorry
lemma contrapos_nn: "⟦¬ Q; P ⟹ Q⟧ ⟹ ¬ P" sorry
lemma contrapos_pp: "⟦Q; ¬ P ⟹ ¬ Q⟧ ⟹ P" sorry
lemma de_Morgan_conj: "(¬ (P ∧ Q)) = (¬ P ∨ ¬ Q)" sorry
lemma de_Morgan_disj: "(¬ (P ∨ Q)) = (¬ P ∧ ¬ Q)" sorry
lemma if_split: "P (if Q then x else y) = ((Q ⟶ P x) ∧ (¬ Q ⟶ P y))" sorry
lemma if_splits: "P (if Q then x else y) = ((Q ⟶ P x) ∧ (¬ Q ⟶ P y))" sorry
lemma if_split_asm: "P (if Q then x else y) = (¬ (Q ∧ ¬ P x ∨ ¬ Q ∧ ¬ P y))" sorry
lemma if_P: "P ⟹ (if P then x else y) = x" sorry
lemma if_not_P: "¬ P ⟹ (if P then x else y) = y" sorry
lemma Let_def: "Let s f = f s" sorry
lemma id_apply[simp]: "id x = x" sorry
lemma comp_apply[simp]: "(f ∘ g) x = f (g x)" sorry
lemma o_def: "(f ∘ g) = (λx. f (g x))" sorry
lemma comp_def: "(f ∘ g) = (λx. f (g x))" sorry

lemma simp_conj1[simp]: "(P ∧ True) = P" sorry
lemma simp_conj2[simp]: "(True ∧ P) = P" sorry
lemma simp_conj3[simp]: "(P ∧ False) = False" sorry
lemma simp_conj4[simp]: "(False ∧ P) = False" sorry
lemma simp_disj1[simp]: "(P ∨ True) = True" sorry
lemma simp_disj2[simp]: "(True ∨ P) = True" sorry
lemma simp_disj3[simp]: "(P ∨ False) = P" sorry
lemma simp_disj4[simp]: "(False ∨ P) = P" sorry
lemma simp_imp1[simp]: "(P ⟶ True) = True" sorry
lemma simp_imp2[simp]: "(P ⟶ False) = (¬ P)" sorry
lemma simp_imp3[simp]: "(P ⟶ P) = True" sorry
lemma simp_idem1[simp]: "(P ∧ P) = P" sorry
lemma simp_idem2[simp]: "(P ∨ P) = P" sorry
lemma simp_contra1[simp]: "(P ∧ ¬ P) = False" sorry
lemma simp_contra2[simp]: "(¬ P ∧ P) = False" sorry
lemma simp_contra3[simp]: "(P ∨ ¬ P) = True" sorry
lemma simp_contra4[simp]: "(¬ P ∨ P) = True" sorry
lemma not_conj[simp]: "(¬ (P ∧ Q)) = (P ⟶ ¬ Q)" sorry
lemma not_disj[simp]: "(¬ (P ∨ Q)) = (¬ P ∧ ¬ Q)" sorry
lemma not_imp[simp]: "(¬ (P ⟶ Q)) = (P ∧ ¬ Q)" sorry
lemma not_all[simp]: "(¬ (∀x. P x)) = (∃x. ¬ P x)" sorry
lemma not_ex[simp]: "(¬ (∃x. P x)) = (∀x. ¬ P x)" sorry
lemma not_iff: "(P ≠ Q) = (P = (¬ Q))" sorry
lemma imp_conjL[simp]: "((P ∧ Q) ⟶ R) = (P ⟶ (Q ⟶ R))" sorry
lemma imp_disjL: "((P ∨ Q) ⟶ R) = ((P ⟶ R) ∧ (Q ⟶ R))" sorry
lemma all_conj_distrib: "(∀x. P x ∧ Q x) = ((∀x. P x) ∧ (∀x. Q x))" sorry
lemma ex_disj_distrib: "(∃x. P x ∨ Q x) = ((∃x. P x) ∨ (∃x. Q x))" sorry
lemma eq_commute: "(a = b) = (b = a)" sorry
lemma eq_sym_conv: "(a = b) = (b = a)" sorry
lemma conj_comms: "(P ∧ Q) = (Q ∧ P)" sorry
lemma disj_comms: "(P ∨ Q) = (Q ∨ P)" sorry
lemma conj_assoc: "((P ∧ Q) ∧ R) = (P ∧ (Q ∧ R))" sorry
lemma disj_assoc: "((P ∨ Q) ∨ R) = (P ∨ (Q ∨ R))" sorry
lemma if_cancel[simp]: "(if c then x else x) = x" sorry
lemma if_True: "(if True then x else y) = x" sorry
lemma if_False: "(if False then x else y) = y" sorry

section ‹Natural numbers›

lemma nat.induct: "⟦P 0; ⋀n. P n ⟹ P (Suc n)⟧ ⟹ P n" sorry
lemma nat.exhaust: "⟦n = 0 ⟹ Q; ⋀m. n = Suc m ⟹ Q⟧ ⟹ Q" sorry
lemma nat_induct: "⟦P 0; ⋀n. P n ⟹ P (Suc n)⟧ ⟹ P n" sorry
lemma less_induct: "(⋀x. (⋀y. y < x ⟹ P y) ⟹ P x) ⟹ P a" sorry
lemma nat_less_induct: "(⋀n. ∀m. m < n ⟶ P m ⟹ P n) ⟹ P n" sorry
lemma Suc_inject: "Suc x = Suc y ⟹ x = y" sorry
lemma nat.inject: "(Suc x = Suc y) = (x = y)" sorry
lemma Suc_neq_Zero: "Suc m = 0 ⟹ R" sorry
lemma Zero_neq_Suc: "0 = Suc m ⟹ R" sorry
lemma Suc_not_Zero: "Suc m ≠ 0" sorry
lemma Zero_not_Suc: "0 ≠ Suc m" sorry
lemma nat.distinct: "Suc m ≠ 0" sorry
lemma add_0[simp]: "0 + n = (n::nat)" sorry
lemma add_0_right[simp]: "m + 0 = (m::nat)" sorry
lemma add_Suc[simp]: "Suc m + n = Suc (m + n)" sorry
lemma add_Suc_right[simp]: "m + Suc n = Suc (m + n)" sorry
lemma plus_nat.simps: "0 + n = (n::nat)" sorry
lemma mult_0[simp]: "0 * n = (0::nat)" sorry
lemma mult_0_right[simp]: "m * 0 = (0::nat)" sorry
lemma mult_Suc[simp]: "Suc m * n = n + m * n" sorry
lemma mult_Suc_right[simp]: "m * Suc n = m + m * n" sorry
lemma diff_0_eq_0[simp]: "0 - n = (0::nat)" sorry
lemma diff_Suc_Suc[simp]: "Suc m - Suc n = m - n" sorry
lemma diff_self_eq_0[simp]: "m - m = (0::nat)" sorry
lemma diff_add_inverse[simp]: "(n + m) - n = (m::nat)" sorry
lemma diff_add_inverse2[simp]: "(m + n) - n = (m::nat)" sorry
lemma Suc_diff_Suc: "n < m ⟹ Suc (m - Suc n) = m - n" sorry
lemma add_is_0[simp]: "(m + n = (0::nat)) = (m = 0 ∧ n = 0)" sorry
lemma mult_is_0[simp]: "(m * n = (0::nat)) = (m = 0 ∨ n = 0)" sorry
lemma neq0_conv[simp]: "(n ≠ (0::nat)) = (0 < n)" sorry
lemma le_0_eq[simp]: "(n ≤ (0::nat)) = (n = 0)" sorry
lemma not_less0[simp]: "¬ (n < (0::nat))" sorry
lemma less_Suc_eq: "(m < Suc n) = (m < n ∨ m = n)" sorry
lemma less_Suc_eq_le: "(m < Suc n) = (m ≤ n)" sorry
lemma Suc_le_eq: "(Suc m ≤ n) = (m < n)" sorry
lemma Suc_less_eq[simp]: "(Suc m < Suc n) = (m < n)" sorry
lemma Suc_le_mono[simp]: "(Suc n ≤ Suc m) = (n ≤ m)" sorry
lemma zero_less_Suc[simp]: "0 < Suc n" sorry
lemma less_Suc0[simp]: "(n < Suc 0) = (n = 0)" sorry
lemma lessI[simp]: "n < Suc n" sorry
lemma le_refl[simp]: "n ≤ (n::nat)" sorry
lemma less_irrefl: "¬ (n < (n::nat))" sorry
lemma le_SucI: "m ≤ n ⟹ m ≤ Suc n" sorry
lemma Suc_leI: "m < n ⟹ Suc m ≤ n" sorry
lemma Suc_leD: "Suc m ≤ n ⟹ m ≤ n" sorry
lemma less_imp_le: "m < n ⟹ m ≤ (n::nat)" sorry
lemma le_imp_less_Suc: "m ≤ n ⟹ m < Suc n" sorry
lemma le_trans: "⟦i ≤ j; j ≤ k⟧ ⟹ i ≤ (k::nat)" sorry
lemma order_trans: "⟦x ≤ y; y ≤ z⟧ ⟹ x ≤ (z::nat)" sorry
lemma less_trans: "⟦i < j; j < k⟧ ⟹ i < (k::nat)" sorry
lemma le_less_trans: "⟦i ≤ j; j < k⟧ ⟹ i < (k::nat)" sorry
lemma less_le_trans: "⟦i < j; j ≤ k⟧ ⟹ i < (k::nat)" sorry
lemma le_antisym: "⟦m ≤ n; n ≤ m⟧ ⟹ m = (n::nat)" sorry
lemma antisym: "⟦m ≤ n; n ≤ m⟧ ⟹ m = (n::nat)" sorry
lemma linorder_not_less: "(¬ x < y) = (y ≤ (x::nat))" sorry
lemma linorder_not_le: "(¬ x ≤ y) = (y < (x::nat))" sorry
lemma not_less: "(¬ x < y) = (y ≤ (x::nat))" sorry
lemma not_le: "(¬ x ≤ y) = (y < (x::nat))" sorry
lemma nat_less_le: "(m < n) = (m ≤ n ∧ m ≠ (n::nat))" sorry
lemma le_eq_less_or_eq: "(m ≤ n) = (m < n ∨ m = (n::nat))" sorry
lemma linear: "x ≤ y ∨ y ≤ (x::nat)" sorry
lemma le_add1: "n ≤ n + (m::nat)" sorry
lemma le_add2: "n ≤ m + (n::nat)" sorry
lemma add_le_mono: "⟦i ≤ j; k ≤ l⟧ ⟹ i + k ≤ j + (l::nat)" sorry
lemma mult_le_mono: "⟦i ≤ j; k ≤ l⟧ ⟹ i * k ≤ j * (l::nat)" sorry
lemma add.commute: "a + b = b + (a::nat)" sorry
lemma add.assoc: "a + b + c = a + (b + (c::nat))" sorry
lemma add.left_commute: "b + (a + c) = a + (b + (c::nat))" sorry
lemma add_commute: "a + b = b + (a::nat)" sorry
lemma add_assoc: "a + b + c = a + (b + (c::nat))" sorry
lemma mult.commute: "a * b = b * (a::nat)" sorry
lemma mult.assoc: "a * b * c = a * (b * (c::nat))" sorry
lemma mult.left_commute: "b * (a * c) = a * (b * (c::nat))" sorry
lemma mult_commute: "a * b = b * (a::nat)" sorry
lemma distrib_left: "a * (b + c) = a * b + a * (c::nat)" sorry
lemma distrib_right: "(a + b) * c = a * c + b * (c::nat)" sorry
lemma add_mult_distrib: "(m + n) * k = m * k + n * (k::nat)" sorry
lemma add_mult_distrib2: "k * (m + n) = k * m + k * (n::nat)" sorry
lemma diff_mult_distrib: "(m - n) * k = m * k - n * (k::nat)" sorry
lemma mult_2: "2 * z = z + (z::nat)" sorry
lemma mult_2_right: "z * 2 = z + (z::nat)" sorry
lemma Suc_eq_plus1: "Suc n = n + 1" sorry
lemma Suc_eq_plus1_left: "Suc n = 1 + n" sorry
lemma One_nat_def: "1 = Suc 0" sorry
lemma power_0[simp]: "a ^ 0 = (1::nat)" sorry
lemma power_Suc[simp]: "a ^ Suc n = a * a ^ n" sorry
lemma max_def: "max a b = (if a ≤ b then b else a)" sorry
lemma min_def: "min a b = (if a ≤ b then a else b)" sorry
lemma dvd_def: "(b dvd a) = (∃k. a = b * k)" sorry
lemma dvd_refl[simp]: "a dvd (a::nat)" sorry
lemma dvd_trans: "⟦a dvd b; b dvd c⟧ ⟹ a dvd (c::nat)" sorry
lemma mod_less: "m < n ⟹ m mod n = (m::nat)" sorry
lemma div_less: "m < n ⟹ m div n = (0::nat)" sorry
lemma mod_mult_self2[simp]: "(m + n * k) mod n = m mod (n::nat)" sorry
lemma add_mult_div: "(n * m) div n = (m::nat)" sorry
lemmas algebra_simps = add.assoc add.commute add.left_commute mult.assoc mult.commute mult.left_commute distrib_left distrib_right
lemmas ac_simps = add.assoc add.commute add.left_commute mult.assoc mult.commute mult.left_commute
lemmas field_simps = add.assoc add.commute add.left_commute mult.assoc mult.commute mult.left_commute distrib_left distrib_right
lemmas arith_simps = add_0 add_0_right
lemmas less_eq_Suc_le = Suc_le_eq

section ‹Lists, options and pairs›

datatype 'a list = Nil | Cons 'a "'a list"
datatype 'a option = None | Some 'a
datatype ('a, 'b) prod = Pair 'a 'b

fun append :: "'a list ⇒ 'a list ⇒ 'a list" where
  "append [] ys = ys"
| "append (x # xs) ys = x # append xs ys"

lemmas append.simps_alt = append.simps

fun rev :: "'a list ⇒ 'a list" where
  "rev [] = []"
| "rev (x # xs) = rev xs @ [x]"

fun length :: "'a list ⇒ nat" where
  "length [] = 0"
| "length (x # xs) = Suc (length xs)"

fun map :: "('a ⇒ 'b) ⇒ 'a list ⇒ 'b list" where
  "map f [] = []"
| "map f (x # xs) = f x # map f xs"

fun filter :: "('a ⇒ bool) ⇒ 'a list ⇒ 'a list" where
  "filter P [] = []"
| "filter P (x # xs) = (if P x then x # filter P xs else filter P xs)"

fun concat :: "'a list list ⇒ 'a list" where
  "concat [] = []"
| "concat (x # xs) = x @ concat xs"

fun sum_list :: "'a list ⇒ 'a" where
  "sum_list [] = 0"
| "sum_list (x # xs) = x + sum_list xs"

fun prod_list :: "'a list ⇒ 'a" where
  "prod_list [] = 1"
| "prod_list (x # xs) = x * prod_list xs"

fun replicate :: "nat ⇒ 'a ⇒ 'a list" where
  "replicate 0 x = []"
| "replicate (Suc n) x = x # replicate n x"

fun take :: "nat ⇒ 'a list ⇒ 'a list" where
  "take 0 xs = []"
| "take (Suc n) [] = []"
| "take (Suc n) (x # xs) = x # take n xs"

fun drop :: "nat ⇒ 'a list ⇒ 'a list" where
  "drop 0 xs = xs"
| "drop (Suc n) [] = []"
| "drop (Suc n) (x # xs) = drop n xs"

fun hd :: "'a list ⇒ 'a" where
  "hd (x # xs) = x"

fun tl :: "'a list ⇒ 'a list" where
  "tl [] = []"
| "tl (x # xs) = xs"

fun last :: "'a list ⇒ 'a" where
  "last (x # xs) = (if xs = [] then x else last xs)"

fun butlast :: "'a list ⇒ 'a list" where
  "butlast [] = []"
| "butlast (x # xs) = (if xs = [] then [] else x # butlast xs)"

fun nth :: "'a list ⇒ nat ⇒ 'a" where
  "nth (x # xs) 0 = x"
| "nth (x # xs) (Suc n) = nth xs n"

fun set :: "'a list ⇒ 'a set" where
  "set [] = {}"
| "set (x # xs) = insert x (set xs)"

fun zip :: "'a list ⇒ 'b list ⇒ ('a × 'b) list" where
  "zip [] ys = []"
| "zip (x # xs) [] = []"
| "zip (x # xs) (y # ys) = (x, y) # zip xs ys"

fun foldr :: "('a ⇒ 'b ⇒ 'b) ⇒ 'a list ⇒ 'b ⇒ 'b" where
  "foldr f [] a = a"
| "foldr f (x # xs) a = f x (foldr f xs a)"

fun foldl :: "('b ⇒ 'a ⇒ 'b) ⇒ 'b ⇒ 'a list ⇒ 'b" where
  "foldl f a [] = a"
| "foldl f a (x # xs) = foldl f (f a x) xs"

fun fold :: "('a ⇒ 'b ⇒ 'b) ⇒ 'a list ⇒ 'b ⇒ 'b" where
  "fold f [] s = s"
| "fold f (x # xs) s = fold f xs (f x s)"

fun list_all :: "('a ⇒ bool) ⇒ 'a list ⇒ bool" where
  "list_all P [] = True"
| "list_all P (x # xs) = (P x ∧ list_all P xs)"

fun list_ex :: "('a ⇒ bool) ⇒ 'a list ⇒ bool" where
  "list_ex P [] = False"
| "list_ex P (x # xs) = (P x ∨ list_ex P xs)"

fun distinct :: "'a list ⇒ bool" where
  "distinct [] = True"
| "distinct (x # xs) = (x ∉ set xs ∧ distinct xs)"

fun remdups :: "'a list ⇒ 'a list" where
  "remdups [] = []"
| "remdups (x # xs) = (if x ∈ set xs then remdups xs else x # remdups xs)"

fun count_list :: "'a list ⇒ 'a ⇒ nat" where
  "count_list [] y = 0"
| "count_list (x # xs) y = (if x = y then count_list xs y + 1 else count_list xs y)"

fun takeWhile :: "('a ⇒ bool) ⇒ 'a list ⇒ 'a list" where
  "takeWhile P [] = []"
| "takeWhile P (x # xs) = (if P x then x # takeWhile P xs else [])"

fun dropWhile :: "('a ⇒ bool) ⇒ 'a list ⇒ 'a list" where
  "dropWhile P [] = []"
| "dropWhile P (x # xs) = (if P x then dropWhile P xs else x # xs)"

fun upt :: "nat ⇒ nat ⇒ nat list" where
  "upt i 0 = []"
| "upt i (Suc j) = (if i ≤ j then upt i j @ [j] else [])"

fun sorted :: "'a list ⇒ bool" where
  "sorted [] = True"
| "sorted (x # ys) = ((∀y ∈ set ys. x ≤ y) ∧ sorted ys)"

fun insort :: "'a ⇒ 'a list ⇒ 'a list" where
  "insort x [] = [x]"
| "insort x (y # ys) = (if x ≤ y then x # y # ys else y # insort x ys)"

fun sort :: "'a list ⇒ 'a list" where
  "sort [] = []"
| "sort (x # xs) = insort x (sort xs)"

fun list_update :: "'a list ⇒ nat ⇒ 'a ⇒ 'a list" where
  "list_update [] i v = []"
| "list_update (x # xs) i v = (case i of 0 ⇒ v # xs | Suc j ⇒ x # list_update xs j v)"

fun fst :: "'a × 'b ⇒ 'a" where
  "fst (x, y) = x"

fun snd :: "'a × 'b ⇒ 'b" where
  "snd (x, y) = y"

fun the :: "'a option ⇒ 'a" where
  "the (Some x) = x"

fun null :: "'a list ⇒ bool" where
  "null [] = True"
| "null (x # xs) = False"

lemma list.induct: "⟦P []; ⋀x xs. P xs ⟹ P (x # xs)⟧ ⟹ P xs" sorry
lemma list.exhaust: "⟦xs = [] ⟹ Q; ⋀y ys. xs = y # ys ⟹ Q⟧ ⟹ Q" sorry
lemma neq_Nil_conv: "(xs ≠ []) = (∃y ys. xs = y # ys)" sorry
lemma append_Nil[simp]: "[] @ ys = ys" sorry
lemma append_Cons[simp]: "(x # xs) @ ys = x # (xs @ ys)" sorry
lemma append_Nil2[simp]: "xs @ [] = xs" sorry
lemma append_assoc[simp]: "(xs @ ys) @ zs = xs @ (ys @ zs)" sorry
lemma append_is_Nil_conv[simp]: "(xs @ ys = []) = (xs = [] ∧ ys = [])" sorry
lemma Nil_is_append_conv[simp]: "([] = xs @ ys) = (xs = [] ∧ ys = [])" sorry
lemma append_same_eq[simp]: "(xs @ ys = xs @ zs) = (ys = zs)" sorry
lemma append1_eq_conv[simp]: "(xs @ [x] = ys @ [y]) = (xs = ys ∧ x = y)" sorry
lemma append_eq_append_conv2: "(xs @ ys = zs @ ts) = (∃us. xs = zs @ us ∧ us @ ys = ts ∨ xs @ us = zs ∧ ys = us @ ts)" sorry
lemma length_append[simp]: "length (xs @ ys) = length xs + length ys" sorry
lemma length_rev[simp]: "length (rev xs) = length xs" sorry
lemma length_map[simp]: "length (map f xs) = length xs" sorry
lemma length_replicate[simp]: "length (replicate n x) = n" sorry
lemma length_0_conv[simp]: "(length xs = 0) = (xs = [])" sorry
lemma length_greater_0_conv[simp]: "(0 < length xs) = (xs ≠ [])" sorry
lemma length_filter_le[simp]: "length (filter P xs) ≤ length xs" sorry
lemma length_take[simp]: "length (take n xs) = min (length xs) n" sorry
lemma length_drop[simp]: "length (drop n xs) = length xs - n" sorry
lemma length_tl[simp]: "length (tl xs) = length xs - 1" sorry
lemma length_zip[simp]: "length (zip xs ys) = min (length xs) (length ys)" sorry
lemma rev_append[simp]: "rev (xs @ ys) = rev ys @ rev xs" sorry
lemma rev_rev_ident[simp]: "rev (rev xs) = xs" sorry
lemma rev_is_Nil_conv[simp]: "(rev xs = []) = (xs = [])" sorry
lemma rev_map: "rev (map f xs) = map f (rev xs)" sorry
lemma map_append[simp]: "map f (xs @ ys) = map f xs @ map f ys" sorry
lemma map_map[simp]: "map f (map g xs) = map (f ∘ g) xs" sorry
lemma map_ident[simp]: "map (λx. x) xs = xs" sorry
lemma map_id[simp]: "map id xs = xs" sorry
lemma map_rev: "map f (rev xs) = rev (map f xs)" sorry
lemma filter_append[simp]: "filter P (xs @ ys) = filter P xs @ filter P ys" sorry
lemma filter_filter[simp]: "filter P (filter Q xs) = filter (λx. Q x ∧ P x) xs" sorry
lemma rev_filter: "rev (filter P xs) = filter P (rev xs)" sorry
lemma concat_append[simp]: "concat (xs @ ys) = concat xs @ concat ys" sorry
lemma set_append[simp]: "set (xs @ ys) = set xs ∪ set ys" sorry
lemma set_rev[simp]: "set (rev xs) = set xs" sorry
lemma set_map[simp]: "set (map f xs) = f IMAGEOP set xs" sorry
lemma set_filter[simp]: "set (filter P xs) = {x. x ∈ set xs ∧ P x}" sorry
lemma in_set_conv_decomp: "(x ∈ set xs) = (∃ys zs. xs = ys @ x # zs)" sorry
lemma sum_list_append[simp]: "sum_list (xs @ ys) = sum_list xs + sum_list ys" sorry
lemma sum_list_rev[simp]: "sum_list (rev xs) = sum_list xs" sorry
lemma foldr_append[simp]: "foldr f (xs @ ys) a = foldr f xs (foldr f ys a)" sorry
lemma foldl_append[simp]: "foldl f a (xs @ ys) = foldl f (foldl f a xs) ys" sorry
lemma take_append: "take n (xs @ ys) = take n xs @ take (n - length xs) ys" sorry
lemma drop_append: "drop n (xs @ ys) = drop n xs @ drop (n - length xs) ys" sorry
lemma append_take_drop_id[simp]: "take n xs @ drop n xs = xs" sorry
lemma take_0: "take 0 xs = []" sorry
lemma drop_0: "drop 0 xs = xs" sorry
lemma take_Nil[simp]: "take n [] = []" sorry
lemma drop_Nil[simp]: "drop n [] = []" sorry
lemma take_Suc_Cons: "take (Suc n) (x # xs) = x # take n xs" sorry
lemma drop_Suc_Cons: "drop (Suc n) (x # xs) = drop n xs" sorry
lemma nth_Cons_0: "(x # xs) ! 0 = x" sorry
lemma nth_Cons_Suc: "(x # xs) ! Suc n = xs ! n" sorry
lemma nth_append: "(xs @ ys) ! n = (if n < length xs then xs ! n else ys ! (n - length xs))" sorry
lemma hd_append: "hd (xs @ ys) = (if xs = [] then hd ys else hd xs)" sorry
lemma last_snoc[simp]: "last (xs @ [x]) = x" sorry
lemma butlast_snoc[simp]: "butlast (xs @ [x]) = xs" sorry
lemma distinct_append[simp]: "distinct (xs @ ys) = (distinct xs ∧ distinct ys ∧ set xs ∩ set ys = {})" sorry
lemma distinct_rev[simp]: "distinct (rev xs) = distinct xs" sorry
lemma replicate_app_Cons_same: "replicate n x @ x # xs = x # replicate n x @ xs" sorry
lemma rev_replicate[simp]: "rev (replicate n x) = replicate n x" sorry
lemma count_list_append[simp]: "count_list (xs @ ys) x = count_list xs x + count_list ys x" sorry
lemma list_all_iff: "list_all P xs = (∀x ∈ set xs. P x)" sorry
lemma list_ex_iff: "list_ex P xs = (∃x ∈ set xs. P x)" sorry
lemma sorted_append: "sorted (xs @ ys) = (sorted xs ∧ sorted ys ∧ (∀x ∈ set xs. ∀y ∈ set ys. x ≤ y))" sorry
lemma fst_conv[simp]: "fst (a, b) = a" sorry
lemma snd_conv[simp]: "snd (a, b) = b" sorry
lemma prod.inject: "((a, b) = (c, d)) = (a = c ∧ b = d)" sorry
lemma prod.collapse[simp]: "(fst p, snd p) = p" sorry
lemma surjective_pairing: "p = (fst p, snd p)" sorry
lemma prod_eqI: "⟦fst p = fst q; snd p = snd q⟧ ⟹ p = q" sorry
lemma option.inject: "(Some a = Some b) = (a = b)" sorry
lemma list.inject: "(x # xs = y # ys) = (x = y ∧ xs = ys)" sorry
lemma list.distinct: "x # xs ≠ []" sorry

section ‹Sets›

lemma mem_Collect_eq[simp]: "(a ∈ {x. P x}) = P a" sorry
lemma Collect_mem_eq[simp]: "{x. x ∈ A} = A" sorry
lemma insert_iff[simp]: "(a ∈ insert b A) = (a = b ∨ a ∈ A)" sorry
lemma empty_iff[simp]: "(c ∈ {}) = False" sorry
lemma UNIV_I[simp]: "x ∈ UNIV" sorry
lemma Un_iff[simp]: "(c ∈ A ∪ B) = (c ∈ A ∨ c ∈ B)" sorry
lemma Int_iff[simp]: "(c ∈ A ∩ B) = (c ∈ A ∧ c ∈ B)" sorry
lemma Diff_iff[simp]: "(c ∈ A - B) = (c ∈ A ∧ c ∉ B)" sorry
lemma image_iff: "(z ∈ f IMAGEOP A) = (∃x ∈ A. z = f x)" sorry
lemma imageI: "x ∈ A ⟹ f x ∈ f IMAGEOP A" sorry
lemma subsetI: "(⋀x. x ∈ A ⟹ x ∈ B) ⟹ A ⊆ B" sorry
lemma subsetD: "⟦A ⊆ B; c ∈ A⟧ ⟹ c ∈ B" sorry
lemma subset_iff: "(A ⊆ B) = (∀t. t ∈ A ⟶ t ∈ B)" sorry
lemma subset_eq: "(A ⊆ B) = (∀x ∈ A. x ∈ B)" sorry
lemma equalityI: "⟦A ⊆ B; B ⊆ A⟧ ⟹ A = B" sorry
lemma set_eqI: "(⋀x. (x ∈ A) = (x ∈ B)) ⟹ A = B" sorry
lemma set_eq_iff: "(A = B) = (∀x. (x ∈ A) = (x ∈ B))" sorry
lemma subset_refl[simp]: "A ⊆ A" sorry
lemma subset_trans: "⟦A ⊆ B; B ⊆ C⟧ ⟹ A ⊆ C" sorry
lemma UnI1: "c ∈ A ⟹ c ∈ A ∪ B" sorry
lemma UnI2: "c ∈ B ⟹ c ∈ A ∪ B" sorry
lemma UnE: "⟦c ∈ A ∪ B; c ∈ A ⟹ P; c ∈ B ⟹ P⟧ ⟹ P" sorry
lemma IntI: "⟦c ∈ A; c ∈ B⟧ ⟹ c ∈ A ∩ B" sorry
lemma IntD1: "c ∈ A ∩ B ⟹ c ∈ A" sorry
lemma IntD2: "c ∈ A ∩ B ⟹ c ∈ B" sorry
lemma CollectI: "P a ⟹ a ∈ {x. P x}" sorry
lemma CollectD: "a ∈ {x. P x} ⟹ P a" sorry
lemma ballI: "(⋀x. x ∈ A ⟹ P x) ⟹ ∀x ∈ A. P x" sorry
lemma bexI: "⟦P x; x ∈ A⟧ ⟹ ∃x ∈ A. P x" sorry
lemma Un_commute: "A ∪ B = B ∪ A" sorry
lemma Int_commute: "A ∩ B = B ∩ A" sorry
lemma Un_empty_left[simp]: "{} ∪ B = B" sorry
lemma Un_empty_right[simp]: "A ∪ {} = A" sorry
lemma Int_empty_left[simp]: "{} ∩ B = {}" sorry
lemma Int_empty_right[simp]: "A ∩ {} = {}" sorry
lemma Un_insert_left[simp]: "insert a B ∪ C = insert a (B ∪ C)" sorry
lemma image_empty[simp]: "f IMAGEOP {} = {}" sorry
lemma image_insert[simp]: "f IMAGEOP insert a B = insert (f a) (f IMAGEOP B)" sorry
lemma image_Un[simp]: "f IMAGEOP (A ∪ B) = f IMAGEOP A ∪ f IMAGEOP B" sorry
`.replace(/IMAGEOP/g, '`');
