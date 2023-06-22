import ring_theory.power_series.basic

namespace mv_power_series


noncomputable theory 

open_locale big_operators 

variables {σ α : Type*} [decidable_eq σ] [semiring α]

lemma exists_coeff_ne_zero_iff_ne_zero (f : mv_power_series σ α) : 
  (∃ (d : σ →₀ ℕ), coeff α d f ≠ 0) ↔ f ≠ 0 :=
begin
  refine not_iff_not.mp _,
  push_neg,
  simp [ext_iff]
end

section weighted_order

/-- The weight of the variables -/
variable (w : σ → ℕ)

include w

variable (f : mv_power_series σ α)

/-- The weight of a monomial -/
def weight : (σ →₀ ℕ) →+ ℕ := 
{ to_fun := λ d, d.sum (λ x y, w x * y),
  map_zero' := by simp, 
  map_add' := λ x y, 
  begin 
    rw finsupp.sum_add_index',
    intro i, rw mul_zero,
    intros i m n, rw mul_add, 
  end }

lemma exists_coeff_ne_zero_of_weight_iff_ne_zero : 
  (∃ (n : ℕ), ∃ (d : σ →₀ ℕ), weight w d = n ∧ coeff α d f ≠ 0) ↔ f ≠ 0 :=
begin
  refine not_iff_not.mp _,
  push_neg,
  split,
  { intro h, ext d, 
    simp only [coeff_zero], 
    refine h _ d rfl, },
  rintros rfl n d hn, simp only [coeff_zero],
end

/-- The weighted order of a mv_power_series -/
def weighted_order (f : mv_power_series σ α) : part_enat :=
begin
  classical,
  exact dite (f = 0) (λ h, ⊤) (λ h, nat.find ((exists_coeff_ne_zero_of_weight_iff_ne_zero w f).mpr h))
end

@[simp]
lemma weighted_order_zero : (0 : mv_power_series σ α).weighted_order w = ⊤ := 
by simp only [weighted_order, dif_pos rfl]

lemma weighted_order_finite_iff_ne_zero : 
  (f.weighted_order w).dom ↔ f ≠ 0 :=
begin
  simp only [weighted_order],
  split,
  { split_ifs with h h; intro H,
    { contrapose! H,
      simpa [←part.eq_none_iff'] },
    { exact h, } },
  { intro h,
    simp [h] }
end

/-- If the order of a formal power series is finite,
then some coefficient of weight the order is nonzero.-/
lemma exists_coeff_ne_zero_of_weighted_order (h : (f.weighted_order w).dom) :
  ∃ (d : σ →₀ ℕ), ↑(weight w d) = f.weighted_order w ∧ coeff α d f ≠ 0 :=
begin
  simp only [weighted_order], 
  simp only [(weighted_order_finite_iff_ne_zero w f).mp h, not_false_iff, ne.def, dif_neg, part_enat.coe_inj],
  generalize_proofs h,
  exact nat.find_spec h,
end

/-- If `d`th coefficient of a formal power series is nonzero,
then the weighted order of the power series is less than or equal to `weight d w`.-/
lemma weighted_order_le (d : σ →₀ ℕ) (h : coeff α d f ≠ 0) :
  f.weighted_order w ≤ weight w d:=
begin
  have := exists.intro d h,
  rw [weighted_order, dif_neg],
  { simp only [part_enat.coe_le_coe, nat.find_le_iff],
    exact ⟨weight w d, le_rfl, d, rfl, h⟩ },
  { exact (f.exists_coeff_ne_zero_of_weight_iff_ne_zero w).mp ⟨weight w d, d, rfl, h⟩ , }
end

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
lemma coeff_of_lt_weighted_order (d : σ →₀ ℕ) (h: ↑(weight w d) < f.weighted_order w) :
  coeff α d f = 0 :=
by { contrapose! h, exact weighted_order_le w f d h }

/-- The `0` power series is the unique power series with infinite order.-/
@[simp] lemma weighted_order_eq_top {f : mv_power_series σ α} :
  f.weighted_order w = ⊤ ↔ f = 0 :=
begin
  split,
  { intro h, ext d, rw [(coeff α d).map_zero, coeff_of_lt_weighted_order w], simp [h] },
  { rintros rfl, exact weighted_order_zero w }
end

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`.-/
lemma nat_le_weighted_order (f : mv_power_series σ α) (n : ℕ) (h : ∀ d, weight w d < n → coeff α d f = 0) :
  ↑n ≤ f.weighted_order w :=
begin
  by_contra H, rw not_le at H,
  have : (f.weighted_order w).dom := part_enat.dom_of_le_coe H.le,
--  rw [← part_enat.coe_get this, part_enat.coe_lt_coe] at H,
  obtain ⟨d, hd, hfd⟩ := exists_coeff_ne_zero_of_weighted_order w f this,
  simp only [← hd, part_enat.coe_lt_coe] at H,
  exact hfd (h d H),
end

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`.-/
lemma le_weighted_order (f : mv_power_series σ α) (n : part_enat) 
  (h : ∀ (d : σ →₀ ℕ) , ↑(weight w d) < n → coeff α d f = 0) :
  n ≤ f.weighted_order w :=
begin
  induction n using part_enat.cases_on,
  { show _ ≤ _, rw [top_le_iff, weighted_order_eq_top],
    ext d, exact h d (part_enat.coe_lt_top _), },
  { apply nat_le_weighted_order, simpa only [part_enat.coe_lt_coe] using h }
end

/-- The order of a formal power series is exactly `n` some coefficient 
of weight `n` is nonzero, 
and the `d`th coefficient is `0` for all `d` such that `weight w d < n`.-/
lemma weighted_order_eq_nat {f : mv_power_series σ α} {n : ℕ} :
  f.weighted_order w = n ↔ (∃ d, weight w d = n ∧ coeff α d f ≠ 0) ∧ (∀ d, weight w d < n → coeff α d f = 0) :=
begin
  rcases eq_or_ne f 0 with rfl|hf,
  { simpa using (part_enat.coe_ne_top _).symm },
  simp only [weighted_order, dif_neg hf, part_enat.coe_inj, nat.find_eq_iff], 
  apply and_congr_right', 
  simp only [not_exists, not_and, not_not],
  simp_rw imp_forall_iff, rw forall_swap,
  apply forall_congr,
  intro d,
  split,
  { intros h hd,
    exact h (weight w d) hd rfl, },
  { intros h m hm hd, rw ← hd at hm, exact h hm, },
end

/- /-- The weighted_order of a formal power series is exactly `n` 
if some coefficient of weight `n` is nonzero,
and the `d`th coefficient is `0` for all `d` such that `weight w d` < n`.-/
lemma order_eq {f : mv_power_series σ α} {n : part_enat} :
  f.weighted_order w = n ↔ (∃ d, (↑(weight w d) = n ∧ coeff α d f ≠ 0)) ∧ (∀ d, ↑(weight w d) < n → coeff α d f = 0) :=
begin
  induction n using part_enat.cases_on,
  { rw weighted_order_eq_top, split,
    { rintro rfl, split,
      { exfalso, 
       -- exact part_enat.coe_ne_top ‹_› ‹_› 
       },
      { exact (coeff _ _).map_zero } },
    { rintro ⟨h₁, h₂⟩, ext i, exact h₂ i (part_enat.coe_lt_top i) } },
  { simpa [part_enat.coe_inj] using order_eq_nat }
end -/

/-- The order of the sum of two formal power series
 is at least the minimum of their orders.-/
lemma le_weighted_order_add (f g : mv_power_series σ α) :
  min (f.weighted_order w) (g.weighted_order w) ≤ (f + g).weighted_order w :=
begin
  refine le_weighted_order w _ _ _,
  simp [coeff_of_lt_weighted_order w] {contextual := tt},
end

private lemma weighted_order_add_of_weighted_order_lt.aux (f g : mv_power_series σ α)
  (H : f.weighted_order w < g.weighted_order w) :
  (f + g).weighted_order w = f.weighted_order w :=
begin
  obtain ⟨n, hn⟩ := part_enat.ne_top_iff.mp (part_enat.ne_top_of_lt H), 
  rw hn at ⊢, 
  rw weighted_order_eq_nat,
  obtain ⟨d, hd, hd'⟩ := ((weighted_order_eq_nat w).mp hn).1,
  split,
  { use d, use hd, 
    rw [hn, ← hd]  at H,
    rw [(coeff _ _).map_add,  coeff_of_lt_weighted_order w g d H, add_zero], 
    exact hd', },
  { intros b hb, 
    suffices : ↑(weight w b) < weighted_order w f,
    rw [(coeff _ _).map_add,
      coeff_of_lt_weighted_order w f b this,
      coeff_of_lt_weighted_order w g b (lt_trans this H),
      add_zero],
    rw [hn, part_enat.coe_lt_coe], exact hb, },
end

/-- The weighted_order of the sum of two formal power series
 is the minimum of their orders if their orders differ.-/
lemma weighted_order_add_of_weighted_order_eq (f g : mv_power_series σ α) (h : f.weighted_order w ≠ g.weighted_order w) :
  weighted_order w (f + g) = weighted_order w f ⊓ weighted_order w g :=
begin
  refine le_antisymm _ (le_weighted_order_add w _ _),
  by_cases H₁ : f.weighted_order w < g.weighted_order w,
  { simp only [le_inf_iff], 
    rw weighted_order_add_of_weighted_order_lt.aux w _ _ H₁, 
    exact ⟨le_rfl, le_of_lt H₁⟩, },
  by_cases H₂ : g.weighted_order w < f.weighted_order w,
  { simp only [add_comm f g, le_inf_iff],
    rw weighted_order_add_of_weighted_order_lt.aux w _ _ H₂, 
    exact ⟨le_of_lt H₂, le_rfl⟩, },
  exfalso, exact h (le_antisymm (not_lt.1 H₂) (not_lt.1 H₁))
end

/-- The weighted_order of the product of two formal power series
 is at least the sum of their orders.-/
lemma weighted_order_mul_ge (f g : mv_power_series σ α) :
  f.weighted_order w + g.weighted_order w ≤ weighted_order w (f * g) :=
begin
  apply le_weighted_order,
  intros d hd, rw [coeff_mul, finset.sum_eq_zero],
  rintros ⟨i,j⟩ hij,
  by_cases hi : ↑(weight w i) < f.weighted_order w,
  { rw [coeff_of_lt_weighted_order w f i hi, zero_mul] },
  by_cases hj : ↑(weight w j) < g.weighted_order w,
  { rw [coeff_of_lt_weighted_order w g j hj, mul_zero] },
  rw not_lt at hi hj, 
  simp only [finsupp.mem_antidiagonal] at hij,
  exfalso,
  apply ne_of_lt (lt_of_lt_of_le hd $ add_le_add hi hj),
  rw [← hij, map_add, nat.cast_add],
end

/-- The weighted_order of the monomial `a*X^d` is infinite if `a = 0` and `weight w d` otherwise.-/
lemma weighted_order_monomial (d : σ →₀ ℕ) (a : α) [decidable (a = 0)] :
  weighted_order w (monomial α d a) = if a = 0 then ⊤ else weight w d :=
begin
  split_ifs with h,
  { rw [h, weighted_order_eq_top, linear_map.map_zero] },
  { rw [weighted_order_eq_nat], split, -- intros i hi,
    { use d, simp only [coeff_monomial_same, eq_self_iff_true, ne.def, true_and], exact h, },
    { intros b hb, rw [coeff_monomial, if_neg], 
      intro h, simpa only [h, lt_self_iff_false] using hb, } }
end

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
lemma weighted_order_monomial_of_ne_zero (d : σ →₀ ℕ) (a : α) (h : a ≠ 0) :
  weighted_order w (monomial α d a) = weight w d :=
by rw [weighted_order_monomial, if_neg h]

/-- If `weight w d` is strictly smaller than the weighted_order of `g`, then the `d`th coefficient of its product
with any other power series is `0`. -/
lemma coeff_mul_of_lt_weighted_order {f g : mv_power_series σ α} {d : σ →₀ ℕ} (h : ↑(weight w d) < g.weighted_order w) :
  coeff α d (f * g) = 0 :=
begin
 -- suffices : coeff α d (f * g) = ∑ p in d.antidiagonal, 0,
  --  rw [this, finset.sum_const_zero],
  rw [coeff_mul],
  apply finset.sum_eq_zero,
  rintros ⟨i, j⟩ hij,
  refine mul_eq_zero_of_right (coeff α i f) _,
  refine coeff_of_lt_weighted_order w g j (lt_of_le_of_lt _ h),
  dsimp,
  simp only [finsupp.mem_antidiagonal] at hij,
  simp only [part_enat.coe_le_coe, ←hij, map_add, le_add_iff_nonneg_left, zero_le'],
end

lemma coeff_mul_one_sub_of_lt_weighted_order {α : Type*} [comm_ring α] {f g : mv_power_series σ α}
  (d : σ →₀ ℕ) (h : ↑(weight w d) < g.weighted_order w) :
  coeff α d (f * (1 - g)) = coeff α d f :=
by simp [coeff_mul_of_lt_weighted_order w h, mul_sub]

lemma coeff_mul_prod_one_sub_of_lt_weighted_order {α ι : Type*} [comm_ring α] (d : σ →₀ ℕ) (s : finset ι)
  (f : mv_power_series σ α) (g : ι → mv_power_series σ α) :
  (∀ i ∈ s, ↑(weight w d) < weighted_order w (g i)) → coeff α d (f * ∏ i in s, (1 - g i)) = coeff α d f :=
begin
  apply finset.induction_on s,
  { simp },
  { intros a s ha ih t,
    simp only [finset.mem_insert, forall_eq_or_imp] at t,
    rw [finset.prod_insert ha, ← mul_assoc, mul_right_comm, coeff_mul_one_sub_of_lt_weighted_order w _ t.1],
    exact ih t.2 },
end

end weighted_order 

section order

variable (f : mv_power_series σ α)

/-- The degree of a monomial -/
def degree : (σ →₀ ℕ) →+ ℕ := weight (λ i, 1)

lemma exists_coeff_ne_zero_of_degree_iff_ne_zero : 
  (∃ (n : ℕ), ∃ (d : σ →₀ ℕ), degree d = n ∧ coeff α d f ≠ 0) ↔ f ≠ 0 := exists_coeff_ne_zero_of_weight_iff_ne_zero (λ i, 1) f

/-- The weighted order of a mv_power_series -/
def order (f : mv_power_series σ α) : part_enat :=
weighted_order (λ i, 1) f

@[simp]
lemma order_zero : (0 : mv_power_series σ α).order = ⊤ := 
weighted_order_zero _

lemma order_finite_iff_ne_zero : 
  (f.order).dom ↔ f ≠ 0 :=
  weighted_order_finite_iff_ne_zero (λ i, 1) f

/-- If the order of a formal power series is finite,
then some coefficient of degree the order is nonzero.-/
lemma exists_coeff_ne_zero_of_order (h : (f.order).dom) :
  ∃ (d : σ →₀ ℕ), ↑(degree d) = f.order ∧ coeff α d f ≠ 0 :=
exists_coeff_ne_zero_of_weighted_order _ f h

/-- If `d`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `degree d`.-/
lemma order_le (d : σ →₀ ℕ) (h : coeff α d f ≠ 0) :f.order ≤ degree d := weighted_order_le _ f d h

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
lemma coeff_of_lt_order (d : σ →₀ ℕ) (h: ↑(degree d) < f.order) :
  coeff α d f = 0 :=
coeff_of_lt_weighted_order _ f d h

/-- The `0` power series is the unique power series with infinite order.-/
@[simp] lemma order_eq_top {f : mv_power_series σ α} :
  f.order = ⊤ ↔ f = 0 :=
weighted_order_eq_top _

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`.-/
lemma nat_le_order (f : mv_power_series σ α) (n : ℕ) (h : ∀ d, degree d < n → coeff α d f = 0) :
  ↑n ≤ f.order :=
nat_le_weighted_order _ f n h

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`.-/
lemma le_order (f : mv_power_series σ α) (n : part_enat) 
  (h : ∀ (d : σ →₀ ℕ) , ↑(degree d) < n → coeff α d f = 0) :
  n ≤ f.order :=
le_weighted_order _ f n h

/-- The order of a formal power series is exactly `n` some coefficient 
of degree `n` is nonzero, 
and the `d`th coefficient is `0` for all `d` such that `degree d < n`.-/
lemma order_eq_nat {f : mv_power_series σ α} {n : ℕ} :
  f.order = n ↔ (∃ d, degree d = n ∧ coeff α d f ≠ 0) ∧ (∀ d, degree d < n → coeff α d f = 0) :=
weighted_order_eq_nat _ 

/-- The order of the sum of two formal power series
 is at least the minimum of their orders.-/
lemma le_order_add (f g : mv_power_series σ α) :
  min (f.order) (g.order) ≤ (f + g).order :=
le_weighted_order_add _ f g 

/-- The order of the sum of two formal power series
 is the minimum of their orders if their orders differ.-/
lemma order_add_of_order_eq (f g : mv_power_series σ α) (h : f.order ≠ g.order) :
 order (f + g) = order f ⊓ order g :=
weighted_order_add_of_weighted_order_eq _ f g h

/-- The order of the product of two formal power series
 is at least the sum of their orders.-/
lemma order_mul_ge (f g : mv_power_series σ α) :
  f.order + g.order ≤ order (f * g) :=
weighted_order_mul_ge _ f g

/-- The order of the monomial `a*X^d` is infinite if `a = 0` and `degree d` otherwise.-/
lemma order_monomial (d : σ →₀ ℕ) (a : α) [decidable (a = 0)] :
  order (monomial α d a) = if a = 0 then ⊤ else degree d :=
weighted_order_monomial _ d a

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
lemma order_monomial_of_ne_zero (d : σ →₀ ℕ) (a : α) (h : a ≠ 0) :
 order (monomial α d a) = degree d :=
weighted_order_monomial_of_ne_zero _ d a h 

/-- If `degree d` is strictly smaller than the order of `g`, then the `d`th coefficient of its product
with any other power series is `0`. -/
lemma coeff_mul_of_lt_order {f g : mv_power_series σ α} {d : σ →₀ ℕ} (h : ↑(degree d) < g.order) :
  coeff α d (f * g) = 0 :=
coeff_mul_of_lt_weighted_order _ h

lemma coeff_mul_one_sub_of_lt_order {α : Type*} [comm_ring α] {f g : mv_power_series σ α}
  (d : σ →₀ ℕ) (h : ↑(degree d) < g.order) :
  coeff α d (f * (1 - g)) = coeff α d f :=
coeff_mul_one_sub_of_lt_weighted_order _ d h


lemma coeff_mul_prod_one_sub_of_lt_order {α ι : Type*} [comm_ring α] (d : σ →₀ ℕ) (s : finset ι)
  (f : mv_power_series σ α) (g : ι → mv_power_series σ α) :
  (∀ i ∈ s, ↑(degree d) < order (g i)) → coeff α d (f * ∏ i in s, (1 - g i)) = coeff α d f :=
coeff_mul_prod_one_sub_of_lt_weighted_order _ d s f g

end order

end mv_power_series
