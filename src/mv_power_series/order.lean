import ring_theory.power_series.basic

namespace mv_power_series


noncomputable theory 

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
  map_add' := λ x y, begin 
  rw finsupp.sum_add_index ,
  sorry,
  end }

lemma exists_coeff_ne_zero_iff_ne_zero' : 
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
  exact dite (f = 0) (λ h, ⊤) (λ h, nat.find ((exists_coeff_ne_zero_iff_ne_zero' w f).mpr h))
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
  { exact (f.exists_coeff_ne_zero_iff_ne_zero' w).mp ⟨weight w d, d, rfl, h⟩ , }
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

#exit

-- TODO 

/-- The order of the monomial `a*X^n` is infinite if `a = 0` and `n` otherwise.-/
lemma weighted_order_monomial (n : ℕ) (a : R) [decidable (a = 0)] :
  order (monomial R n a) = if a = 0 then ⊤ else n :=
begin
  split_ifs with h,
  { rw [h, order_eq_top, linear_map.map_zero] },
  { rw [order_eq], split; intros i hi,
    { rw [part_enat.coe_inj] at hi, rwa [hi, coeff_monomial_same] },
    { rw [part_enat.coe_lt_coe] at hi, rw [coeff_monomial, if_neg], exact ne_of_lt hi } }
end

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
lemma order_monomial_of_ne_zero (n : ℕ) (a : R) (h : a ≠ 0) :
  order (monomial R n a) = n :=
by rw [order_monomial, if_neg h]

/-- If `n` is strictly smaller than the order of `ψ`, then the `n`th coefficient of its product
with any other power series is `0`. -/
lemma coeff_mul_of_lt_order {φ ψ : power_series R} {n : ℕ} (h : ↑n < ψ.order) :
  coeff R n (φ * ψ) = 0 :=
begin
  suffices : coeff R n (φ * ψ) = ∑ p in finset.nat.antidiagonal n, 0,
    rw [this, finset.sum_const_zero],
  rw [coeff_mul],
  apply finset.sum_congr rfl (λ x hx, _),
  refine mul_eq_zero_of_right (coeff R x.fst φ) (coeff_of_lt_order x.snd (lt_of_le_of_lt _ h)),
  rw finset.nat.mem_antidiagonal at hx,
  norm_cast,
  linarith,
end

lemma coeff_mul_one_sub_of_lt_order {R : Type*} [comm_ring R] {φ ψ : power_series R}
  (n : ℕ) (h : ↑n < ψ.order) :
  coeff R n (φ * (1 - ψ)) = coeff R n φ :=
by simp [coeff_mul_of_lt_order h, mul_sub]

lemma coeff_mul_prod_one_sub_of_lt_order {R ι : Type*} [comm_ring R] (k : ℕ) (s : finset ι)
  (φ : power_series R) (f : ι → power_series R) :
  (∀ i ∈ s, ↑k < (f i).order) → coeff R k (φ * ∏ i in s, (1 - f i)) = coeff R k φ :=
begin
  apply finset.induction_on s,
  { simp },
  { intros a s ha ih t,
    simp only [finset.mem_insert, forall_eq_or_imp] at t,
    rw [finset.prod_insert ha, ← mul_assoc, mul_right_comm, coeff_mul_one_sub_of_lt_order _ t.1],
    exact ih t.2 },
end


end order 


end mv_power_series
