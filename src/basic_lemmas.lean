import data.finset.basic -- for not_eq_or_aux
import algebra.order.sub  -- for tsub_tsub_tsub_cancel_left

import data.finset.nat_antidiagonal -- for 4-fold sums
import ring_theory.ideal.basic -- for 4-fold sums (might not be optimal)


-- The "unused arguments" linter incorrectly flags this (?!)
/- To help distinguish the extreme cases in a finset.range(n+1).sum -/
lemma not_eq_or_aux {n m : ℕ} (hn : n ≠ 0) (hm : m ∈ finset.range(n + 1)) : m ≠ 0 ∨ n - m ≠ 0 :=
begin
  simp only [finset.mem_range, nat.lt_succ_iff] at hm,
  by_contradiction h,
  simp only [not_or_distrib, ne.def, not_not, tsub_eq_zero_iff_le, not_le, not_lt] at h,
  apply hn, rw ← le_zero_iff, rw ← h.1, exact h.2, 
end

lemma tsub_tsub_tsub_cancel_left {α : Type*} [add_comm_semigroup α] [partial_order α]
  [has_exists_add_of_le α] [covariant_class α α has_add.add has_le.le] [has_sub α] 
  [has_ordered_sub α] [contravariant_class α α has_add.add has_le.le] {a b c : α} (hcb : c ≤ b)
  (hab : b ≤ a) : a - c - (a - b) = b - c := 
by rw [tsub_eq_iff_eq_add_of_le (tsub_le_tsub_left hcb a), tsub_add_eq_add_tsub hcb, add_comm, 
  tsub_add_cancel_of_le hab]

lemma nat.self_sub_sub_eq {u v n : ℕ} (huv : v ≤ u) (hun : u ≤ n) :
  n - v - (n - u) = u - v :=
tsub_tsub_tsub_cancel_left huv hun
/- begin
  rw nat.sub_eq_iff_eq_add (tsub_le_tsub_left h n),
  rw ← nat.sub_add_comm h,
  rw add_comm,
  rw nat.sub_add_cancel h', 
end -/

section classical
open_locale classical

lemma function.extend_apply_first {α β γ : Type*} (f : α → β) (g : α → γ) (e' : β → γ)
  (hf : ∀ (a b : α), f a = f b → g a = g b) (a : α) :
  function.extend f g e' (f a) = g a :=
begin
  simp only [function.extend_def, dif_pos, exists_apply_eq_apply],
  apply hf,
  exact (classical.some_spec (exists_apply_eq_apply f a)), 
end

end classical

section four_fold_sums

/- 
lemma rewriting_4_fold_sums {m n u v : ℕ} 
  (h : m + n = u + v) (f : ℕ × ℕ → ℕ) {g : (ℕ × ℕ) × ℕ × ℕ → ℕ}
  (hgf : g = λ x, f(x.fst.fst, x.fst.snd) ) 
  (hf : ∀ (x : ℕ × ℕ), u < x.fst ∨ v < x.snd → f x = 0) :
  (finset.nat.antidiagonal m).sum
    (λ (y : ℕ × ℕ),
       (finset.filter (λ (x : (ℕ × ℕ) × ℕ × ℕ), (λ (x : (ℕ × ℕ) × ℕ × ℕ), x.fst) x = y)
          (finset.filter (λ (x : (ℕ × ℕ) × ℕ × ℕ), x.fst.fst + x.snd.fst = 
            u ∧ x.fst.snd + x.snd.snd = v)
             (finset.nat.antidiagonal m ×ˢ finset.nat.antidiagonal n))).sum g) =
  (finset.nat.antidiagonal m).sum (λ (ij : ℕ × ℕ), f ⟨ij.fst, ij.snd⟩) := 
begin
  apply finset.sum_congr rfl,
  rintros ⟨i,j⟩ hij, simp only [finset.nat.mem_antidiagonal] at hij,
  rw finset.sum_filter, rw finset.sum_filter,
  simp_rw ← ite_and,
  suffices hf' : ∀ (x : (ℕ × ℕ) × ℕ × ℕ),
  ite ((x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v) ∧ x.fst = (i, j))
    (g x) 0 =
  ite ((x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v) ∧ x.fst = (i, j))
    1 0 * (f⟨i, j⟩),
  rw finset.sum_congr rfl (λ x hx, hf' x),
  rw ← finset.sum_mul, 
  by_cases hij' : i ≤ u ∧ j ≤ v, 
  { conv_rhs { rw ← one_mul (f ⟨i, j⟩), }, 
    apply congr_arg2 _ _ rfl,
    rw finset.sum_eq_single (⟨⟨i, j⟩, ⟨u-i, v-j⟩⟩ : (ℕ × ℕ) × ℕ ×ℕ),
    simp only [nat.add_sub_of_le hij'.1, nat.add_sub_of_le hij'.2, eq_self_iff_true, and_self,
      if_true],
    { rintros ⟨⟨x,y⟩, ⟨z,t⟩⟩ hb hb',   rw if_neg, intro hb'',
      simp only [finset.mem_product, finset.nat.mem_antidiagonal] at hb,
      simp only [ne.def, prod.mk.inj_iff, not_and, and_imp] at hb',
      simp only [prod.mk.inj_iff] at hb'',
      specialize hb' hb''.2.1 hb''.2.2,
      rw [hb''.2.1, hb''.2.2] at hb,  
      apply hb', 
      apply nat.add_left_cancel, rw [nat.add_sub_of_le hij'.1, ← hb''.2.1, hb''.1.1], 
      apply nat.add_left_cancel, rw [nat.add_sub_of_le hij'.2, ← hb''.2.2, hb''.1.2], },
    { intro hb, rw if_neg, intro hb', apply hb,
      simp only [eq_self_iff_true, and_true] at hb', 
      simp only [finset.mem_product, finset.nat.mem_antidiagonal],
      apply and.intro hij,
      apply nat.add_left_cancel, rw [h, ← hij], 
      conv_rhs {rw [← hb'.1, ← hb'.2] }, 
      simp only [← add_assoc, add_left_inj], 
      simp only [add_assoc, add_right_inj],
      apply add_comm,  }, },
  { simp only [not_and_distrib, not_le] at hij', 
    rw [hf ⟨i, j⟩ hij', mul_zero], },
  { intro x,
    split_ifs with hx,
    { simp only [one_mul, hgf], rw hx.2, },
    { rw zero_mul, } },
end
-/
lemma rewriting_4_fold_sums {α : Type*} [comm_semiring α] {m n u v : ℕ} 
  (h : m + n = u + v) (f : ℕ × ℕ → α) {g : (ℕ × ℕ) × ℕ × ℕ → α}
  (hgf : g = λ x, f(x.fst.fst, x.fst.snd) ) 
  (hf : ∀ (x : ℕ × ℕ), u < x.fst ∨ v < x.snd → f x = 0) :  
  (finset.filter (λ (x : (ℕ × ℕ) × ℕ × ℕ), x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v)
  (finset.nat.antidiagonal m ×ˢ finset.nat.antidiagonal n)).sum  g
  = (finset.nat.antidiagonal m).sum f := 
begin
  let q := λ (x : (ℕ × ℕ) × ℕ × ℕ), x.fst,
  have hq : ∀ x ∈ finset.filter (λ (x : (ℕ × ℕ) × ℕ × ℕ), x.fst.fst + x.snd.fst = 
    u ∧ x.fst.snd + x.snd.snd = v) (finset.nat.antidiagonal m ×ˢ finset.nat.antidiagonal n), 
  x.fst ∈ finset.nat.antidiagonal m,
  { intro x, simp, intro h', simp [h'], },
  rw ←  finset.sum_fiberwise_of_maps_to hq,
  
  apply finset.sum_congr rfl,
  rintros ⟨i,j⟩ hij, simp only [finset.nat.mem_antidiagonal] at hij,
  rw finset.sum_filter, rw finset.sum_filter,
  simp_rw ← ite_and,
  suffices hf' : ∀ (x : (ℕ × ℕ) × ℕ × ℕ),
  ite ((x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v) ∧ x.fst = (i, j))
    (g x) 0 =
  ite ((x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v) ∧ x.fst = (i, j))
    1 0 * (f⟨i, j⟩),
  rw finset.sum_congr rfl (λ x hx, hf' x),
  rw ← finset.sum_mul, 
  by_cases hij' : i ≤ u ∧ j ≤ v, 
  { conv_rhs { rw ← one_mul (f ⟨i, j⟩), }, 
    apply congr_arg2 _ _ rfl,
    rw finset.sum_eq_single (⟨⟨i, j⟩, ⟨u-i, v-j⟩⟩ : (ℕ × ℕ) × ℕ ×ℕ),
    simp only [nat.add_sub_of_le hij'.1, nat.add_sub_of_le hij'.2, eq_self_iff_true,
      and_self, if_true],
    { rintros ⟨⟨x,y⟩, ⟨z,t⟩⟩ hb hb',   rw if_neg, intro hb'',
      simp only [finset.mem_product, finset.nat.mem_antidiagonal] at hb,
      simp only [ne.def, prod.mk.inj_iff, not_and, and_imp] at hb',
      simp only [prod.mk.inj_iff] at hb'',
      specialize hb' hb''.2.1 hb''.2.2,
      rw [hb''.2.1, hb''.2.2] at hb,  
      apply hb', 
      apply nat.add_left_cancel, rw [nat.add_sub_of_le hij'.1, ← hb''.2.1, hb''.1.1], 
      apply nat.add_left_cancel, rw [nat.add_sub_of_le hij'.2, ← hb''.2.2, hb''.1.2], },
    { intro hb, rw if_neg, intro hb', apply hb,
      simp only [eq_self_iff_true, and_true] at hb', 
      simp only [finset.mem_product, finset.nat.mem_antidiagonal],
      apply and.intro hij,
      apply nat.add_left_cancel, rw [h, ← hij], 
      conv_rhs {rw [← hb'.1, ← hb'.2] }, 
      simp only [← add_assoc, add_left_inj], 
      simp only [add_assoc, add_right_inj],
      apply add_comm,  }, },
  { simp only [not_and_distrib, not_le] at hij', 
    rw [hf ⟨i, j⟩ hij', mul_zero], },
  { intro x,
    split_ifs with hx,
    { simp only [one_mul, hgf], rw hx.2, },
    { rw zero_mul, } },
end

/- TODO : There should be some general rewriting pattern 
for sums indexed by finset.nat_tuple_antidiagonal 
This one would first rewrite to 
(finset.nat_tuple_antidiagonal 4 n).sum (λ x, f(x0, x1, x2, x3)) 
and then one would apply the permutation (13)(24) -/

/-- Rewrites a 4-fold sum from variables (12)(34) to (13)(24) -/
lemma finset.sum_4_rw {α : Type*} [add_comm_monoid α] (f : ℕ × ℕ × ℕ × ℕ → α) (n : ℕ) : 
  finset.sum (finset.range (n + 1)) (λ k, 
    finset.sum (finset.range (k + 1)) (λ a, 
      finset.sum (finset.range (n - k + 1)) (λ c, 
        f(a, k-a,c, n - k - c)))) =
  finset.sum (finset.range (n + 1)) (λ l, 
    finset.sum (finset.range (l + 1)) (λ a, 
      finset.sum (finset.range (n - l + 1)) (λ b, 
        f(a, b, l - a, n - l - b)))) :=
begin
  rw finset.sum_sigma',
  rw finset.sum_sigma',
  rw finset.sum_sigma',
  rw finset.sum_sigma',
  let aux_i : (Σ (i : Σ (i : ℕ), ℕ), ℕ) → (Σ (i : Σ (i : ℕ), ℕ), ℕ) :=
  λ ⟨⟨k, a⟩, c⟩, ⟨⟨a + c, a⟩, k - a⟩,
  have aux_hi : ∀ (a : Σ (i : Σ (i : ℕ), ℕ), ℕ)
    (ha : a ∈ ((finset.range (n + 1)).sigma 
      (λ (x : ℕ), finset.range (x + 1))).sigma
        (λ (a : Σ (i : ℕ), ℕ), finset.range (n - a.fst + 1))),
    (λ (x : Σ (i : Σ (i : ℕ), ℕ), ℕ)
     (hx : x ∈ ((finset.range (n + 1)).sigma 
        (λ (a : ℕ), finset.range (a + 1))).sigma
           (λ (a : Σ (i : ℕ), ℕ), finset.range (n - a.fst + 1))), aux_i x) a ha ∈
    ((finset.range (n + 1)).sigma (λ (a : ℕ), finset.range (a + 1))).sigma
      (λ (x : Σ (i : ℕ), ℕ), finset.range (n - x.fst + 1)),
  { rintros ⟨⟨k, a⟩, c⟩ h,
    simp only [finset.mem_sigma, finset.mem_range, nat.lt_succ_iff] at h,
    simp_rw [aux_i, finset.mem_sigma, finset.mem_range, nat.lt_succ_iff], 
    split, split,
    { apply le_trans (add_le_add h.1.2 h.2) _,
      rw add_comm, rw nat.sub_add_cancel h.1.1, },
    { exact le_self_add, },
    { rw add_comm a c, rw ← nat.sub_sub n c a, 
      simp, rw nat.sub_add_cancel, 
      rw nat.le_sub_iff_right,
      rw nat.le_sub_iff_right at h, rw add_comm k c, exact h.2,
      exact h.1.1,
      apply le_trans h.2, exact nat.sub_le n k,
      rw nat.le_sub_iff_right, 
      rw nat.le_sub_iff_right at h,
      apply nat.le_of_add_le_add_right, 
      rw add_assoc a c _, rw add_comm n _,
      exact add_le_add h.1.2 h.2,
      exact h.1.1,
      apply le_trans h.2 _, apply nat.sub_le, }, },
  rw finset.sum_bij' (λ x hx, aux_i x) aux_hi _ (λ y hy, aux_i y) aux_hi _ _, 
  { rintros ⟨⟨k, a⟩, c⟩ h, 
    simp only [finset.mem_sigma, finset.mem_range, nat.lt_succ_iff] at h,
    apply congr_arg, 
    dsimp [aux_i],
    simp only [prod.mk.inj_iff],
    apply and.intro rfl, 
    apply and.intro rfl,
    split,
    { rw add_comm a c, rw nat.add_sub_cancel, },
    { simp only [nat.sub_sub],
      apply congr_arg2 _ rfl,
      rw [add_comm k c, add_comm a c, add_assoc],
      apply congr_arg2 _ rfl,
      rw add_comm, 
      rw nat.sub_add_cancel h.1.2, }, },
  { rintros ⟨⟨k, a⟩, c⟩ h,
    simp only [finset.mem_sigma, finset.mem_range, nat.lt_succ_iff] at h,
    simp_rw [aux_i],
    simp only [add_tsub_cancel_left, sigma.mk.inj_iff, heq_iff_eq, eq_self_iff_true, and_true], 
    { rw add_comm, rw nat.sub_add_cancel h.1.2, }, },
  { rintros ⟨⟨k, a⟩, c⟩ h,
    simp only [finset.mem_sigma, finset.mem_range, nat.lt_succ_iff] at h,
    simp_rw [aux_i],
    simp only [add_tsub_cancel_left, sigma.mk.inj_iff, heq_iff_eq, eq_self_iff_true, and_true], 
    { rw add_comm, rw nat.sub_add_cancel h.1.2, }, },
end 

end four_fold_sums
