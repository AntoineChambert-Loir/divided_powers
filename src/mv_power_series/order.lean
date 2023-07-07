import ring_theory.power_series.basic

namespace mv_power_series


noncomputable theory

open enat with_top

open_locale big_operators 

variables {σ α : Type*} [semiring α]

lemma coeff_apply (f : mv_power_series σ α) (d : σ →₀ ℕ) :
  coeff α d f = f d := rfl

lemma exists_coeff_ne_zero_iff_ne_zero (f : mv_power_series σ α) : 
  (∃ (d : σ →₀ ℕ), coeff α d f ≠ 0) ↔ f ≠ 0 :=
by simp only [ext_iff, ne.def, coeff_zero, not_forall]

section weighted_order

/-- The weight of the variables -/
variable (w : σ → ℕ)

include w

variable (f : mv_power_series σ α)

/-- The weight of a monomial -/
def weight : (σ →₀ ℕ) →+ ℕ := 
{ to_fun := λ d, d.sum (λ x y, w x * y),
  map_zero' := finsupp.sum_zero_index,
  map_add' := λ x y, 
  begin 
    rw finsupp.sum_add_index',
    { intro i, rw mul_zero },
    { intros i m n, rw mul_add }, 
  end }

lemma weight_apply (d : σ →₀ ℕ) : weight w d = d.sum (λ x, has_mul.mul (w x)) := 
by simp only [weight]; refl

lemma le_weight (x : σ) (hx : w x ≠ 0) (d : σ →₀ ℕ): d x ≤ weight w d :=
begin
  classical,
  simp only [weight_apply, finsupp.sum],
  by_cases hxd : x ∈ d.support, 
  { rw finset.sum_eq_add_sum_diff_singleton hxd,
    refine le_trans _ (nat.le_add_right _ _),
    exact nat.le_mul_of_pos_left (zero_lt_iff.mpr hx), },
  simp only [finsupp.mem_support_iff, not_not] at hxd,
  rw hxd, 
  apply zero_le,
end

lemma finite_of_weight_le [finite σ] (hw : ∀ x, w x ≠ 0) (n : ℕ) : 
  { f : σ →₀ ℕ | weight w f ≤ n}.finite :=
begin
  classical,
  let fg := finsupp.antidiagonal (finsupp.equiv_fun_on_finite.symm (function.const σ n)),
  suffices : {f : σ →₀ ℕ | weight w f ≤ n} ⊆ ↑(fg.image (λ uv, uv.fst)),
  apply set.finite.subset _ this,
  apply finset.finite_to_set,
  intros f hf,
  simp only [finset.coe_image, set.mem_image, finset.mem_coe, finsupp.mem_antidiagonal, prod.exists, exists_and_distrib_right,
    exists_eq_right],
  use (finsupp.equiv_fun_on_finite.symm (function.const σ n)) - f,
  ext x,
  simp only [finsupp.coe_add, finsupp.coe_tsub, pi.add_apply, pi.sub_apply, finsupp.equiv_fun_on_finite_symm_apply_to_fun,
  function.const_apply],
  rw add_comm,
  apply nat.sub_add_cancel , 
  apply le_trans (le_weight w x (hw x) f),
  simpa only [set.mem_set_of_eq] using hf,
end

lemma exists_coeff_ne_zero_of_weight_iff_ne_zero : 
  (∃ (n : ℕ), ∃ (d : σ →₀ ℕ), weight w d = n ∧ coeff α d f ≠ 0) ↔ f ≠ 0 :=
begin
  refine not_iff_not.mp _,
  push_neg,
  split,
  { intro h, ext d, 
    exact h _ d rfl, },
  { rintros rfl n d hn, exact coeff_zero _ }, 
end

/-- The weighted order of a mv_power_series -/
def weighted_order (f : mv_power_series σ α) : ℕ∞ :=
begin
  classical,
  exact dite (f = 0) (λ h, ⊤) 
    (λ h, nat.find ((exists_coeff_ne_zero_of_weight_iff_ne_zero w f).mpr h))
end

@[simp] lemma weighted_order_zero : (0 : mv_power_series σ α).weighted_order w = ⊤ := 
by simp only [weighted_order, dif_pos rfl]

lemma weighted_order_finite_iff_ne_zero : 
  ↑(to_nat (f.weighted_order w)) = (f.weighted_order w)  ↔ f ≠ 0 :=
begin
  simp only [weighted_order],
  split,
  { split_ifs with h h; intro H,
    { simp only [to_nat_top, enat.coe_zero, zero_ne_top] at H,
      exfalso; exact H },
    { exact h, } },
  { intro h,
    simp only [h, not_false_iff, dif_neg, to_nat_coe] }
end


/-- If the order of a formal power series `f` is finite,
then some coefficient of weight equal to the order of `f` is nonzero.-/
lemma exists_coeff_ne_zero_of_weighted_order 
  (h : ↑(to_nat (f.weighted_order w)) = (f.weighted_order w)) :
  ∃ (d : σ →₀ ℕ), ↑(weight w d) = f.weighted_order w ∧ coeff α d f ≠ 0 :=
begin
  simp_rw [weighted_order, dif_neg ((weighted_order_finite_iff_ne_zero _ f).mp h), nat.cast_inj],
  generalize_proofs h1,
  exact nat.find_spec h1,
end

/-- If the `d`th coefficient of a formal power series is nonzero,
then the weighted order of the power series is less than or equal to `weight d w`.-/
lemma weighted_order_le {d : σ →₀ ℕ} (h : coeff α d f ≠ 0) :
  f.weighted_order w ≤ weight w d:=
begin
  have := exists.intro d h,
  rw [weighted_order, dif_neg],
  { simp only [with_top.coe_le_coe, nat.find_le_iff],
    exact ⟨weight w d, le_rfl, d, rfl, h⟩ },
  { exact (f.exists_coeff_ne_zero_of_weight_iff_ne_zero w).mp ⟨weight w d, d, rfl, h⟩ , }
end

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
lemma coeff_of_lt_weighted_order {d : σ →₀ ℕ} (h: ↑(weight w d) < f.weighted_order w) :
  coeff α d f = 0 :=
by { contrapose! h, exact weighted_order_le w f h }

/-- The `0` power series is the unique power series with infinite order.-/
@[simp] lemma weighted_order_eq_top_iff {f : mv_power_series σ α} :
  f.weighted_order w = ⊤ ↔ f = 0 :=
begin
  split,
  { intro h, ext d, simp only [(coeff α d).map_zero, coeff_of_lt_weighted_order w, h, 
      with_top.coe_lt_top]},
  { rintros rfl, exact weighted_order_zero w }
end

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`.-/
lemma nat_le_weighted_order {f : mv_power_series σ α} {n : ℕ} 
  (h : ∀ d, weight w d < n → coeff α d f = 0) : ↑n ≤ f.weighted_order w :=
begin
  by_contra H, rw not_le at H,
  have : ↑(to_nat (f.weighted_order w)) = (f.weighted_order w),
  { rw [coe_to_nat_eq_self], exact ne_top_of_lt H, },
  obtain ⟨d, hd, hfd⟩ := exists_coeff_ne_zero_of_weighted_order w f this,
  simp only [← hd, with_top.coe_lt_coe] at H,
  exact hfd (h d H),
end

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`.-/
lemma le_weighted_order {f : mv_power_series σ α} {n : ℕ∞}
  (h : ∀ (d : σ →₀ ℕ) , ↑(weight w d) < n → coeff α d f = 0) :
  n ≤ f.weighted_order w :=
begin
  cases n,
  { rw [none_eq_top, top_le_iff, weighted_order_eq_top_iff],
    ext d, exact h d (coe_lt_top _), },
  { rw some_eq_coe at h ⊢,
    apply nat_le_weighted_order, simpa only [with_top.coe_lt_coe] using h } 
end

/-- The order of a formal power series is exactly `n` if and only if some coefficient of weight `n`
is nonzero, and the `d`th coefficient is `0` for all `d` such that `weight w d < n`.-/
lemma weighted_order_eq_nat {f : mv_power_series σ α} {n : ℕ} : f.weighted_order w = n ↔ 
  (∃ d, weight w d = n ∧ coeff α d f ≠ 0) ∧ (∀ d, weight w d < n → coeff α d f = 0) :=
begin
  rcases eq_or_ne f 0 with rfl|hf,
  { simp only [weighted_order_zero, top_ne_nat, coeff_zero, ne.def, eq_self_iff_true, not_true, 
      and_false, exists_false, false_and] },
  { simp only [weighted_order, dif_neg hf, coe_eq_coe, nat.find_eq_iff], 
    apply and_congr_right', 
    simp only [not_exists, not_and, not_not, imp_forall_iff],
    rw forall_swap,
    apply forall_congr,
    intro d,
    split,
    { intros h hd,
      exact h (weight w d) hd rfl, },
    { intros h m hm hd, rw ← hd at hm, exact h hm, }},
end


/-- The order of the sum of two formal power series is at least the minimum of their orders.-/
lemma le_weighted_order_add (f g : mv_power_series σ α) :
  min (f.weighted_order w) (g.weighted_order w) ≤ (f + g).weighted_order w :=
begin
  refine le_weighted_order w _,
  simp only [coeff_of_lt_weighted_order w, lt_min_iff, map_add, add_zero, eq_self_iff_true, 
    implies_true_iff] {contextual := tt},
end

private lemma weighted_order_add_of_weighted_order_lt.aux {f g : mv_power_series σ α}
  (H : f.weighted_order w < g.weighted_order w) :
  (f + g).weighted_order w = f.weighted_order w :=
begin
  obtain ⟨n, hn⟩ := ne_top_iff_exists.mp (ne_top_of_lt H), 
  rw ← hn at ⊢, 
  rw weighted_order_eq_nat,
  obtain ⟨d, hd, hd'⟩ := ((weighted_order_eq_nat w).mp hn.symm).1,
  split,
  { use d, use hd,
    rw [← hn, ← hd] at H,
    rw [(coeff _ _).map_add,  coeff_of_lt_weighted_order w g H, add_zero], 
    exact hd', },
  { intros b hb, 
    suffices : ↑(weight w b) < weighted_order w f,
    { rw [(coeff _ _).map_add, coeff_of_lt_weighted_order w f this,
      coeff_of_lt_weighted_order w g (lt_trans this H), add_zero] },
    rw [← hn, coe_lt_coe], exact hb },
end

/-- The weighted_order of the sum of two formal power series
 is the minimum of their orders if their orders differ.-/
lemma weighted_order_add_of_weighted_order_eq {f g : mv_power_series σ α}
  (h : f.weighted_order w ≠ g.weighted_order w) :
  weighted_order w (f + g) = weighted_order w f ⊓ weighted_order w g :=
begin
  refine le_antisymm _ (le_weighted_order_add w _ _),
  by_cases H₁ : f.weighted_order w < g.weighted_order w,
  { simp only [le_inf_iff, weighted_order_add_of_weighted_order_lt.aux w H₁], 
    exact ⟨le_rfl, le_of_lt H₁⟩, },
  { by_cases H₂ : g.weighted_order w < f.weighted_order w,
    { simp only [add_comm f g, le_inf_iff, weighted_order_add_of_weighted_order_lt.aux w H₂], 
      exact ⟨le_of_lt H₂, le_rfl⟩, },
    { exact absurd (le_antisymm (not_lt.1 H₂) (not_lt.1 H₁)) h }}
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
  { rw [coeff_of_lt_weighted_order w f hi, zero_mul] },
  { by_cases hj : ↑(weight w j) < g.weighted_order w,
    { rw [coeff_of_lt_weighted_order w g hj, mul_zero] },
    { rw not_lt at hi hj, 
      simp only [finsupp.mem_antidiagonal] at hij,
      exfalso,
      apply ne_of_lt (lt_of_lt_of_le hd $ add_le_add hi hj),
      rw [← hij, map_add, nat.cast_add] }},
end

/-- The weighted_order of the monomial `a*X^d` is infinite if `a = 0` and `weight w d` otherwise.-/
lemma weighted_order_monomial (d : σ →₀ ℕ) (a : α) [decidable (a = 0)] :
  weighted_order w (monomial α d a) = if a = 0 then ⊤ else weight w d :=
begin
  split_ifs with h,
  { rw [h, weighted_order_eq_top_iff, linear_map.map_zero] },
  { rw [weighted_order_eq_nat], 
    split, 
    { use d, simp only [coeff_monomial_same, eq_self_iff_true, ne.def, true_and], exact h, },
    { intros b hb, rw [coeff_monomial, if_neg], 
      intro h, simpa only [h, lt_self_iff_false] using hb, } }
end

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
lemma weighted_order_monomial_of_ne_zero (d : σ →₀ ℕ) (a : α) (h : a ≠ 0) :
  weighted_order w (monomial α d a) = weight w d :=
by rw [weighted_order_monomial, if_neg h]

/-- If `weight w d` is strictly smaller than the weighted_order of `g`, then the `d`th coefficient 
of its product with any other power series is `0`. -/
lemma coeff_mul_of_lt_weighted_order (f : mv_power_series σ α) {g : mv_power_series σ α} 
  {d : σ →₀ ℕ} (h : ↑(weight w d) < g.weighted_order w) : coeff α d (f * g) = 0 :=
begin
  rw [coeff_mul],
  apply finset.sum_eq_zero,
  rintros ⟨i, j⟩ hij,
  refine mul_eq_zero_of_right (coeff α i f) _,
  refine coeff_of_lt_weighted_order w g (lt_of_le_of_lt _ h),
  simp only [finsupp.mem_antidiagonal] at hij,
  simp only [coe_le_coe, ←hij, map_add, le_add_iff_nonneg_left, zero_le'],
end

lemma coeff_mul_one_sub_of_lt_weighted_order {α : Type*} [comm_ring α] {f g : mv_power_series σ α}
  (d : σ →₀ ℕ) (h : ↑(weight w d) < g.weighted_order w) :
  coeff α d (f * (1 - g)) = coeff α d f :=
by simp only [coeff_mul_of_lt_weighted_order w f h, mul_sub, mul_one, _root_.map_sub, sub_zero]

lemma coeff_mul_prod_one_sub_of_lt_weighted_order {α ι : Type*} [comm_ring α] (d : σ →₀ ℕ) 
  (s : finset ι) (f : mv_power_series σ α) (g : ι → mv_power_series σ α) :
  (∀ i ∈ s, ↑(weight w d) < weighted_order w (g i)) → 
    coeff α d (f * ∏ i in s, (1 - g i)) = coeff α d f :=
begin
  apply finset.induction_on s,
  { simp only [implies_true_iff, finset.prod_empty, mul_one, eq_self_iff_true]},
  { intros a s ha ih t,
    simp only [finset.mem_insert, forall_eq_or_imp] at t,
    rw [finset.prod_insert ha, ← mul_assoc, mul_right_comm, 
      coeff_mul_one_sub_of_lt_weighted_order w _ t.1],
    exact ih t.2 },
end

end weighted_order 

section order

variable (f : mv_power_series σ α)

/-- The degree of a monomial -/
def degree : (σ →₀ ℕ) →+ ℕ := weight (λ i, 1)

lemma degree_apply (d : σ →₀ ℕ) : degree d = d.sum (λ x, id) := 
begin
  simp only [degree, weight_apply], 
  apply congr_arg,
  ext x,
  simp only [one_mul, id.def],
 end

lemma le_degree (x : σ) (d : σ →₀ ℕ): d x ≤ degree d :=
begin
  convert le_weight _ x _ d,
  exact ne_zero.ne 1,
end

lemma finite_of_degree_le [finite σ] (n : ℕ) : 
  { f : σ →₀ ℕ | degree f ≤ n}.finite :=
begin
  refine finite_of_weight_le (function.const σ 1) _ n,
  simp only [ne.def, nat.one_ne_zero, not_false_iff, implies_true_iff],
end

lemma exists_coeff_ne_zero_of_degree_iff_ne_zero : 
  (∃ (n : ℕ), ∃ (d : σ →₀ ℕ), degree d = n ∧ coeff α d f ≠ 0) ↔ f ≠ 0 := 
exists_coeff_ne_zero_of_weight_iff_ne_zero (λ i, 1) f

/-- The order of a mv_power_series -/
def order (f : mv_power_series σ α) : ℕ∞ :=
weighted_order (λ i, 1) f

@[simp] lemma order_zero : (0 : mv_power_series σ α).order = ⊤ := 
weighted_order_zero _

lemma order_finite_iff_ne_zero : ↑(to_nat(f.order)) = f.order ↔ f ≠ 0 :=
weighted_order_finite_iff_ne_zero _ f

/-- If the order of a formal power series `f` is finite,
then some coefficient of degree the order of `f` is nonzero.-/
lemma exists_coeff_ne_zero_of_order (h : ↑(to_nat(f.order)) = f.order) :
  ∃ (d : σ →₀ ℕ), ↑(degree d) = f.order ∧ coeff α d f ≠ 0 :=
exists_coeff_ne_zero_of_weighted_order _ f h

/-- If the `d`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `degree d`. -/
lemma order_le (d : σ →₀ ℕ) (h : coeff α d f ≠ 0) : f.order ≤ degree d := weighted_order_le _ f h

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
lemma coeff_of_lt_order (d : σ →₀ ℕ) (h: ↑(degree d) < f.order) : coeff α d f = 0 :=
coeff_of_lt_weighted_order _ f h

/-- The `0` power series is the unique power series with infinite order.-/
@[simp] lemma order_eq_top {f : mv_power_series σ α} : f.order = ⊤ ↔ f = 0 :=
weighted_order_eq_top_iff _

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`.-/
lemma nat_le_order {f : mv_power_series σ α} {n : ℕ} (h : ∀ d, degree d < n → coeff α d f = 0) :
  ↑n ≤ f.order :=
nat_le_weighted_order _ h

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`.-/
lemma le_order {f : mv_power_series σ α} {n : ℕ∞} 
  (h : ∀ (d : σ →₀ ℕ) , ↑(degree d) < n → coeff α d f = 0) : n ≤ f.order :=
le_weighted_order _ h

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
lemma order_add_of_order_eq {f g : mv_power_series σ α} (h : f.order ≠ g.order) :
 order (f + g) = order f ⊓ order g :=
weighted_order_add_of_weighted_order_eq _ h

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
lemma order_monomial_of_ne_zero (d : σ →₀ ℕ) {a : α} (h : a ≠ 0) :
 order (monomial α d a) = degree d :=
weighted_order_monomial_of_ne_zero _ d a h 

/-- If `degree d` is strictly smaller than the order of `g`, then the `d`th coefficient of its 
product with any other power series is `0`. -/
lemma coeff_mul_of_lt_order {f g : mv_power_series σ α} {d : σ →₀ ℕ} (h : ↑(degree d) < g.order) :
  coeff α d (f * g) = 0 :=
coeff_mul_of_lt_weighted_order _ f h

lemma coeff_mul_one_sub_of_lt_order {α : Type*} [comm_ring α] {f g : mv_power_series σ α}
  (d : σ →₀ ℕ) (h : ↑(degree d) < g.order) :
  coeff α d (f * (1 - g)) = coeff α d f :=
coeff_mul_one_sub_of_lt_weighted_order _ d h

lemma coeff_mul_prod_one_sub_of_lt_order {α ι : Type*} [comm_ring α] (d : σ →₀ ℕ) (s : finset ι)
  (f : mv_power_series σ α) (g : ι → mv_power_series σ α) :
  (∀ i ∈ s, ↑(degree d) < order (g i)) → coeff α d (f * ∏ i in s, (1 - g i)) = coeff α d f :=
coeff_mul_prod_one_sub_of_lt_weighted_order _ d s f g

section homogeneous_component

variable (w : σ → ℕ)

/-- Given an `mv_power_series f`, it returns the homogeneous component of degree `p`. -/
def homogeneous_component (p : ℕ) :
  mv_power_series σ α →ₗ[α] mv_power_series σ α :=
{ to_fun := λ f d, ite (weight w d = p) (coeff α d f) (0),
  map_add' := λ f g, 
  begin
    ext d,
    simp only [coeff_apply, pi.add_apply],
    split_ifs,
    refl,
    rw add_zero,
  end,
  map_smul' := λ a f, 
  begin
    ext d,
    simp only [coeff_apply, pi.smul_apply, smul_eq_mul, ring_hom.id_apply, mul_ite, mul_zero], 
  end }

lemma coeff_homogeneous_component (p : ℕ) (d : σ →₀ ℕ) (f : mv_power_series σ α) :
  coeff α d (homogeneous_component w p f) = ite (weight w d = p) (coeff α d f) 0 :=
rfl

end homogeneous_component

end mv_power_series