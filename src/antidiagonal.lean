/- antidiagonal with values in more general types 
 inspired by a file of Bhavik Mehta -/

import data.finset.basic
import ring_theory.power_series.basic
import mv_power_series.order

open_locale big_operators

open finset function 

variables {μ : Type*} [canonically_ordered_add_monoid μ] [locally_finite_order μ] 
  [decidable_eq μ]

variables {ι : Type*}  [decidable_eq ι] [decidable_eq (ι → μ)]

variables {σ : Type*} [decidable_eq σ] [decidable_eq (ι → σ →₀ ℕ)]

variables {α : Type*} [comm_semiring α]

namespace finset 

/-- The finset of functions `ι → μ` whose support is contained in `s`
  and whose sum is `n` -/
def cut (s : finset ι) (n : μ) : finset (ι → μ) :=
finset.filter (λ f, s.sum f = n) ((s.pi (λ _, Iic n)).map 
  ⟨λ f i, if h : i ∈ s then f i h else 0, 
    λ f g h, by { ext i hi, simpa only [dif_pos hi] using congr_fun h i, }⟩)

/-- The finset of pairs of elements of `μ` with sum `n` -/
def antidiagonal (n : μ) : finset (μ × μ) := 
finset.filter (λ uv, uv.fst + uv.snd = n) (finset.product (Iic n) (Iic n)) 

lemma mem_antidiagonal (n : μ) (a : μ × μ) : 
  a ∈ antidiagonal n ↔ a.fst + a.snd = n := 
begin
  simp only [antidiagonal, mem_filter, mem_product, mem_Iic, and_iff_right_iff_imp],
  intro h, rw ← h,
  exact ⟨le_self_add, le_add_self⟩,
end

lemma mem_cut (s : finset ι) (n : μ) (f : ι → μ) :
  f ∈ cut s n ↔ s.sum f = n ∧ ∀ i ∉ s, f i = 0 :=
begin
  rw [cut, mem_filter, and_comm, and_congr_right], 
  intro h,
  simp only [mem_map, exists_prop, function.embedding.coe_fn_mk, mem_pi],
  split,
  { rintro ⟨_, _, rfl⟩ _ _,
    simp [dif_neg H] },
  { intro hf,
    refine ⟨λ i hi, f i, λ i hi, _, _⟩,
    { rw [mem_Iic, ← h],
      apply single_le_sum _ hi,
      simp },
    { ext,
      rw [dite_eq_ite, ite_eq_left_iff, eq_comm],
      exact hf x } }
end

lemma _root_.finsupp.antidiagonal_eq_antidiagonal (d : σ →₀ ℕ) : 
  d.antidiagonal = antidiagonal d :=
begin
  ext x,
  rw [finsupp.mem_antidiagonal, mem_antidiagonal],
end

lemma cut_equiv_antidiagonal (n : μ) :
  equiv.finset_congr (equiv.bool_arrow_equiv_prod _) (cut univ n) = antidiagonal n :=
begin
  ext ⟨x₁, x₂⟩,
  simp_rw [equiv.finset_congr_apply, mem_map, equiv.to_embedding, function.embedding.coe_fn_mk,
           ←equiv.eq_symm_apply],
  simp [mem_cut, add_comm, mem_antidiagonal],
end

lemma cut_zero (s : finset ι) :
  cut s (0 : μ) = {0} :=
begin
  ext f,
  rw [mem_cut, mem_singleton, sum_eq_zero_iff, ← forall_and_distrib, funext_iff],
  apply forall_congr,
  intro i, 
  simp only [← or_imp_distrib, em (i ∈ s), forall_true_left, pi.zero_apply],
end

lemma cut_empty (n : μ) :
  cut (∅ : finset ι) n = if (n = 0) then {0} else ∅ := 
begin
  ext f,
  rw mem_cut,
  simp only [sum_empty, not_mem_empty, not_false_iff, forall_true_left],
  split_ifs with hn, 
  simp only [hn, mem_singleton, funext_iff, eq_self_iff_true, true_and, pi.zero_apply],
  simp only [not_mem_empty, iff_false],
  intro h', exact hn h'.1.symm,
end

lemma cut_insert (n : μ) (a : ι) (s : finset ι) (h : a ∉ s) :
  cut (insert a s) n =
  (antidiagonal n).bUnion
    (λ (p : μ × μ), (cut s p.snd).image 
      (λ f, function.update f a p.fst)) :=
begin
  ext f,
  rw [mem_cut, mem_bUnion, sum_insert h],
  split,
  { rintro ⟨rfl, h₁⟩,
    simp only [exists_prop, function.embedding.coe_fn_mk, mem_map,
               mem_antidiagonal, prod.exists],
    use f a, 
    use s.sum f,
    split, refl,
    rw mem_image, 
    use function.update f a 0,
    split,
    { rw [mem_cut s (s.sum f)], 
      split,
      apply finset.sum_congr rfl,
      intros i hi, rw function.update_apply, rw if_neg, intro hia, apply h, rw ← hia, exact hi, 
      intros i hi, rw function.update_apply, split_ifs with hia,
        refl,
        apply h₁, simp only [mem_insert, not_or_distrib], exact ⟨hia, hi⟩, },
    { ext i,
      rw function.update_apply (update f a 0), 
      rw function.update_apply, 
      split_ifs with hia,
        rw hia,
        refl, }, },
  { simp only [mem_insert, mem_antidiagonal, mem_image, exists_prop, prod.exists, forall_exists_index, and_imp, mem_cut],
    rintros d e rfl g hg hg' rfl,
    split,
    { simp only [function.update_same], 
      apply congr_arg2 _ rfl, 
      rw ← hg,
      apply finset.sum_congr rfl,
      intros i hi, rw function.update_noteq _,
      intro hia, apply h, simpa only [hia] using hi, }, 
    { intros i hi, rw not_or_distrib at hi, 
      rw function.update_noteq hi.1, 
      exact hg' i hi.2, } },
end


end finset

-- TODO : move elsewhere

namespace mv_power_series

open finset

/-- The `d`th coefficient of a finite product over `s` of power series 
is the sum of products of coefficients indexed by `cut s d` -/
lemma coeff_prod (s : finset ι) (f : ι → mv_power_series σ α) (d : σ →₀ ℕ) :
  coeff α d (∏ j in s, f j) = ∑ l in cut s d, ∏ i in s, coeff α (l i) (f i) :=
begin
  revert d,
  apply finset.induction_on s,
  { intro d, 
    simp only [prod_empty, cut_empty, coeff_one], 
    split_ifs; simp, },
  intros a s ha ih d,
  rw [cut_insert _ _ _ ha, prod_insert ha, coeff_mul, sum_bUnion],
  { apply finset.sum_congr (finsupp.antidiagonal_eq_antidiagonal d),
    rintros ⟨u, v⟩ huv,
    simp only [mem_antidiagonal] at huv, 
    dsimp, 
    rw [sum_image _],
    simp only [pi.add_apply, function.embedding.coe_fn_mk, prod_insert ha, if_pos rfl, ih,
      mul_sum],
    apply sum_congr rfl,
    { intros k hk, 
      apply congr_arg2 _,
      rw function.update_same, 
      apply finset.prod_congr rfl,
      intros i hi, rw function.update_noteq, 
      intro hi', apply ha, simpa [hi'] using hi, },
    { intros k hk l hl,
      simp only [funext_iff], apply forall_imp,
      intros i h,
      simp only [mem_cut] at hk hl, 
      by_cases hi : i = a, 
      rw [hi, hk.2 a ha, hl.2 a ha],
      simpa only [function.update_noteq hi] using h, }, },
  { simp only [set.pairwise_disjoint, set.pairwise, finset.mem_coe, mem_antidiagonal], 
    rintros ⟨u, v⟩ huv ⟨u', v'⟩ huv' h, 
    dsimp at huv huv', 
    simp only [on_fun_apply],
    rw [disjoint_left],
    intros k hk hl, simp only [mem_image] at hk hl, 
    obtain ⟨k, hk, rfl⟩ := hk,
    obtain ⟨l, hl, hkl⟩ := hl,
    simp only [mem_cut] at hk hl,
    apply h, simp only [prod.mk.inj_iff],
    suffices : u = u', 
    apply and.intro this,
    rw [this, ← huv'] at huv, 
    simpa only [add_right_inj] using huv,
    apply symm,
    simpa only [function.update_same] using funext_iff.mp hkl a, }
end

variable [decidable_eq (ℕ → σ →₀ ℕ)] 

/-- The `d`th coefficient of a finite product over `s` of power series 
is the sum of products of coefficients indexed by `cut s d` -/
lemma coeff_pow 
  (f : mv_power_series σ α) (n : ℕ) (d : σ →₀ ℕ) :
  coeff α d (f ^ n) = ∑ l in cut (finset.range n) d, ∏ i in finset.range n, coeff α (l i) f :=
begin
  suffices : f ^ n = (finset.range n).prod (λ i, f),
  rw [this, coeff_prod],
  rw [finset.prod_const, card_range],
end

/-- Bourbaki, Algèbre, chap. 4, §4, n°2, proposition 3 -/
theorem coeff_eq_zero_of_constant_coeff_nilpotent 
  (f : mv_power_series σ α) (m : ℕ) (hf : (constant_coeff σ α f) ^ m = 0) 
  (d : σ →₀ ℕ) (n : ℕ) (hn : m + degree d ≤ n) :
  coeff α d (f ^ n) = 0 := 
begin
  rw coeff_pow,
  apply sum_eq_zero,
  intros k hk,
  rw mem_cut at hk,
  let s := (range n).filter (λ i, k i = 0),
  suffices hs : s ⊆ range n,
  rw ← prod_sdiff hs,
  convert mul_zero _,
  have hs' : ∀ i ∈ s, coeff α (k i) f = constant_coeff σ α f, 
  { simp only [s, mem_filter], intros i hi, rw hi.2, 
    simp only [coeff_zero_eq_constant_coeff], },
  rw prod_congr rfl hs',
  rw prod_const,
  suffices : m ≤ s.card,
  obtain ⟨m', hm'⟩ := nat.exists_eq_add_of_le this,
  rw [hm', pow_add, hf, zero_mul],
  rw ← nat.add_le_add_iff_right,rw add_comm s.card,
  rw finset.card_sdiff_add_card_eq_card hs, 
  simp only [card_range],
  apply le_trans _ hn,
  simp only [add_comm m, nat.add_le_add_iff_right],
  rw ← hk.1, rw map_sum,
  rw ← sum_sdiff hs,
  have hs' : ∀ i ∈ s, degree (k i) = 0,
  { simp only [s, mem_filter], intros i hi, rw [hi.2, map_zero] },
  rw [sum_eq_zero hs', add_zero],
  convert finset.card_nsmul_le_sum (range n \ s) _ 1 _, 
  simp only [algebra.id.smul_eq_mul, mul_one],
  { simp only [mem_filter, mem_sdiff, mem_range, not_and, and_imp], 
    intros i hi hi', rw ← not_lt, intro h, apply hi' hi, 
    simpa only [nat.lt_one_iff, degree_eq_zero_iff] using h, },
  -- hs 
  apply filter_subset,
end

end mv_power_series

/-  This is a variant that produces finsupp functions. Is it useful?

noncomputable example (s : finset ι) (t : set ↥s) : finset ι :=
 s.filter (λ i, i ∈ (coe : ↥s → ι) '' t)
--  (s.attach.filter (λi, i ∈  t)).map (?subtype.coe)

noncomputable def finsupp_of {ι: Type*} {s : finset ι} (f : s → μ) : ι →₀ μ := {
to_fun := λ i, if h : i ∈ s then f ⟨i, h⟩ else 0,
support := s.filter (λ i, i ∈ (coe : ↥s → ι) '' f.support),
mem_support_to_fun := λ i,
begin
  simp only [set.mem_image, mem_support, ne.def, finset.exists_coe, subtype.coe_mk, exists_and_distrib_right, exists_eq_right,
  mem_filter, dite_eq_right_iff, not_forall, and_iff_right_iff_imp, forall_exists_index],
  intros hx _, exact hx,
end }

/-- finsupp.cut s n is the finset of finitely supported functions with sum n
  whose support is contained in s -/
noncomputable def finsupp.cut {ι : Type*} (s : finset ι) (n : μ) : finset (ι →₀ μ) :=
finset.filter (λ f, f.sum (λ u v, v) = n) ((s.pi (λ _, Iic n)).map 
  ⟨λ f, ({
    to_fun := λ i, if h : i ∈ s then f i h else 0, 
    support := s.filter (λ i, ∃ h : i ∈ s, f i h ≠ 0),
    mem_support_to_fun := λ i, 
    begin
      simp only [ne.def, mem_filter, dite_eq_right_iff, not_forall, and_iff_right_iff_imp, forall_exists_index],
      intros hi _, exact hi,
    end } : ι →₀ μ), 
  λ f g h, 
  begin 
    ext i hi, 
    simp only [ne.def, filter_congr_decidable, funext_iff] at h,
    let hi' := h.2 i, 
    simpa only [dif_pos hi] using h.2 i,
  end ⟩)

lemma finsupp.mem_cut  {ι : Type*} (s : finset ι) (n : μ) (f : ι →₀ μ) :
  f ∈ finsupp.cut s n ↔ f.sum (λ u v, v) = n ∧ ∀ i ∉ s, f i = 0 :=
begin
  rw [finsupp.cut, mem_filter, and_comm, and_congr_right], 
  intro h,
  simp only [mem_map, exists_prop, function.embedding.coe_fn_mk, mem_pi],
  split,
  { rintro ⟨_, _, rfl⟩ _ _,
    simp [dif_neg H] },
  { intro hf,
    refine ⟨λ i hi, f i, λ i hi, _, _⟩,
    { rw [mem_Iic, ← h],
      suffices : f.support ⊆ s,
      rw f.sum_of_support_subset this,
      apply finset.single_le_sum _ hi,
      intros i hi, apply zero_le,
      simp,
      intros i, rw [finsupp.mem_support_iff, not_imp_comm], exact hf i, },
    { ext i,
      simp only [finsupp.coe_mk, dite_eq_ite, ite_eq_left_iff],
      intro hi, rw hf i hi, } }
end
 -/
