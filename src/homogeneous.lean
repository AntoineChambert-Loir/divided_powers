import algebra.direct_sum.internal
import algebra.graded_monoid
import data.mv_polynomial.variables

/-!
# Homogeneous polynomials

It is possible to assign weights to the variables of a multivariate polynomial ring, so that 
monomials of the ring then have a weighted degree with respect to the weights of the variables. 

A multivariate polynomial `φ` is homogeneous of weighted degree `n`
if all monomials occuring in `φ` have the same weighted degree `n`.

## Main definitions/lemmas

* `is_homogeneous φ n`: a predicate that asserts that `φ` is homogeneous of weighted degree `n`.


* `homogeneous_submodule σ R n`: the submodule of homogeneous polynomials of weighted degree `n`.
* `homogeneous_component n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneous_component`: every polynomial is the sum of its homogeneous components

-/

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra

universes u v w
variables {R : Type u} {S : Type v} {M : Type w}

namespace mv_polynomial
variables {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section comm_semiring
variables [comm_semiring R] {p q : mv_polynomial σ R} [add_comm_monoid M]


/-! ### `weighted_degrees` -/

/-- The `weighted degree` of the monomial a*∏x_i^s_i is the sum ∑n_i*(wt x_i)  -/
def weighted_degree (w : σ → M) (s : σ →₀ ℕ) /- (a : R) -/ : M :=
finsum (λ (i : σ), (s i) • (w i))

namespace weighted_degree

/-- The `weighted degree` of the product of monomials s * t is  the sum of their
  weighted degrees  -/
lemma mul (w : σ → M) (s t : σ →₀ ℕ) : 
  weighted_degree w (s + t) = weighted_degree w s + weighted_degree w t :=
begin
  simp only [weighted_degree, finsupp.coe_add, pi.add_apply, add_smul],
  exact finsum_add_distrib 
    (finite.subset s.finite_support (function.support_smul_subset_left s w))
    (finite.subset t.finite_support (function.support_smul_subset_left t w))
end

lemma zero (w : σ → M)  : weighted_degree w 0 = 0 :=
by simp only [weighted_degree, finsupp.coe_zero, pi.zero_apply, zero_smul, finsum_zero]

lemma pow (w : σ → M) (s : σ →₀ ℕ) (n : ℕ) :
  weighted_degree w (n • s) = n • weighted_degree w s :=
begin
  induction n with k hk,
  { simp only [zero_smul, zero] },
  { simp only [succ_nsmul, mul, hk] },
end

end weighted_degree

/-- A multivariate polynomial `φ` is homogeneous of weighted degree `m` if all monomials 
  occuring in `φ` have weighted degree `m`. -/
def is_weighted_homogeneous (w : σ → M) (φ : mv_polynomial σ R) (m : M) : Prop := 
∀ ⦃d⦄, coeff d φ ≠ 0 → weighted_degree w d = m 

variable (R)

/-- The submodule of homogeneous `mv_polynomial`s of degree `n`. -/
def weighted_homogeneous_submodule [comm_semiring R] (w : σ → M) (m : M) :
  submodule R (mv_polynomial σ R) :=
{ carrier := { x | x.is_weighted_homogeneous w m },
  smul_mem' := λ r a ha c hc, begin
    rw coeff_smul at hc,
    apply ha,
    intro h,
    apply hc,
    rw h,
    exact smul_zero r,
  end,
  zero_mem' := λ d hd, false.elim (hd $ coeff_zero _),
  add_mem' := λ a b ha hb c hc, begin
    rw coeff_add at hc,
    obtain h|h : coeff c a ≠ 0 ∨ coeff c b ≠ 0,
    { contrapose! hc, simp only [hc, add_zero] },
    { exact ha h },
    { exact hb h },
  end }

variables {R}

@[simp] lemma mem_weighted_homogeneous_submodule (w : σ → M) (m : M) (p : mv_polynomial σ R) :
  p ∈ weighted_homogeneous_submodule R w m ↔ p.is_weighted_homogeneous w m := iff.rfl

variables (R)

/-- While equal, the former has a convenient definitional reduction. -/
lemma weighted_homogeneous_submodule_eq_finsupp_supported (w : σ → M) (m : M) :
  weighted_homogeneous_submodule R w m = 
  finsupp.supported _ R {d | weighted_degree w d = m} :=
begin
  ext,
  rw [finsupp.mem_supported, set.subset_def],
  simp only [finsupp.mem_support_iff, finset.mem_coe],
  refl,
end

variables {R}

lemma weighted_homogeneous_submodule_mul [comm_semiring R] (w : σ → M) (m n : M) :
  weighted_homogeneous_submodule R w m * weighted_homogeneous_submodule R w n ≤ 
    weighted_homogeneous_submodule R w (m + n) :=
begin
  rw submodule.mul_le,
  intros φ hφ ψ hψ c hc,
  rw [coeff_mul] at hc,
  obtain ⟨⟨d, e⟩, hde, H⟩ := finset.exists_ne_zero_of_sum_ne_zero hc,
  have aux : coeff d φ ≠ 0 ∧ coeff e ψ ≠ 0,
  { contrapose! H,
    by_cases h : coeff d φ = 0;
    simp only [*, ne.def, not_false_iff, zero_mul, mul_zero] at * },
  specialize hφ aux.1, specialize hψ aux.2,
  rw finsupp.mem_antidiagonal at hde,
  classical,
  have hd' : d.support ⊆ d.support ∪ e.support := finset.subset_union_left _ _,
  have he' : e.support ⊆ d.support ∪ e.support := finset.subset_union_right _ _,
  rw [← hde, ← hφ, ← hψ, weighted_degree.mul],
end

lemma is_weighted_homogeneous_monomial (w : σ → M) (d : σ →₀ ℕ) (r : R) {m : M} 
  (hm : weighted_degree w d = m) : is_weighted_homogeneous w (monomial d r) m :=
begin
  intros c hc,
  classical,
  rw coeff_monomial at hc,
  split_ifs at hc with h,
  { subst c, exact hm },
  { contradiction }
end

lemma is_weighted_homogeneous_of_total_degree_zero (w : σ → M) {p : mv_polynomial σ R} 
  (hp : p.total_degree = 0) : is_weighted_homogeneous w p 0 :=
begin
  erw [total_degree, finset.sup_eq_bot_iff] at hp,
  -- we have to do this in two steps to stop simp changing bot to zero
  simp_rw [mem_support_iff] at hp,
  --simp only [is_weighted_homogeneous],
  intros d hd,
  simp only [weighted_degree],
  specialize hp d hd,
  apply finsum_eq_zero_of_forall_eq_zero,
  intro e, 
  suffices : d e = 0, simp only [this, zero_smul], 
  by_cases he: e ∈ d.support, 
  { change _ = 0 at hp, 
    simp only [finsupp.sum, finset.sum_eq_zero_iff] at hp, 
    exact hp e he, }, 
  exact finsupp.not_mem_support_iff.mp he, 
end
 
lemma is_weighted_homogeneous_C (w : σ → M) (r : R) :
  is_weighted_homogeneous w (C r : mv_polynomial σ R) 0 :=
is_weighted_homogeneous_monomial _ _ _ (weighted_degree.zero w)

variables (R)

lemma is_weighted_homogeneous_zero (w : σ → M) (m : M) : 
  is_weighted_homogeneous w (0 : mv_polynomial σ R) m :=
(weighted_homogeneous_submodule R w m).zero_mem

lemma is_weighted_homogeneous_one  (w : σ → M) :
  is_weighted_homogeneous w (1 : mv_polynomial σ R) 0 :=
is_weighted_homogeneous_C _ _

variables {σ} (R)

lemma is_weighted_homogeneous_X (w : σ → M) (i : σ) :
  is_weighted_homogeneous w (X i : mv_polynomial σ R) (w i) :=
begin
  apply is_weighted_homogeneous_monomial,
  simp only [weighted_degree, single_smul, one_smul, single_apply, ite_smul, zero_smul],
  rw finsum_eq_single _ i,
  { rw if_pos rfl },
  { intros j hj, rw if_neg hj.symm }
end

#exit


/-
TODO
* create definition for `∑ i in d.support, d i`
* show that `mv_polynomial σ R ≃ₐ[R] ⨁ i, homogeneous_submodule σ R i`
-/

/-- A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`. -/
def is_homogeneous [comm_semiring R] (φ : mv_polynomial σ R) (n : ℕ) :=
∀ ⦃d⦄, coeff d φ ≠ 0 → ∑ i in d.support, d i = n

variables (σ R)

/-- The submodule of homogeneous `mv_polynomial`s of degree `n`. -/
def homogeneous_submodule [comm_semiring R] (n : ℕ) :
  submodule R (mv_polynomial σ R) :=
{ carrier := { x | x.is_homogeneous n },
  smul_mem' := λ r a ha c hc, begin
    rw coeff_smul at hc,
    apply ha,
    intro h,
    apply hc,
    rw h,
    exact smul_zero r,
  end,
  zero_mem' := λ d hd, false.elim (hd $ coeff_zero _),
  add_mem' := λ a b ha hb c hc, begin
    rw coeff_add at hc,
    obtain h|h : coeff c a ≠ 0 ∨ coeff c b ≠ 0,
    { contrapose! hc, simp only [hc, add_zero] },
    { exact ha h },
    { exact hb h }
  end }

variables {σ R}

@[simp] lemma mem_homogeneous_submodule [comm_semiring R] (n : ℕ) (p : mv_polynomial σ R) :
  p ∈ homogeneous_submodule σ R n ↔ p.is_homogeneous n := iff.rfl

variables (σ R)

/-- While equal, the former has a convenient definitional reduction. -/
lemma homogeneous_submodule_eq_finsupp_supported [comm_semiring R] (n : ℕ) :
  homogeneous_submodule σ R n = finsupp.supported _ R {d | ∑ i in d.support, d i = n} :=
begin
  ext,
  rw [finsupp.mem_supported, set.subset_def],
  simp only [finsupp.mem_support_iff, finset.mem_coe],
  refl,
end

variables {σ R}

lemma homogeneous_submodule_mul [comm_semiring R] (m n : ℕ) :
  homogeneous_submodule σ R m * homogeneous_submodule σ R n ≤ homogeneous_submodule σ R (m + n) :=
begin
  rw submodule.mul_le,
  intros φ hφ ψ hψ c hc,
  rw [coeff_mul] at hc,
  obtain ⟨⟨d, e⟩, hde, H⟩ := finset.exists_ne_zero_of_sum_ne_zero hc,
  have aux : coeff d φ ≠ 0 ∧ coeff e ψ ≠ 0,
  { contrapose! H,
    by_cases h : coeff d φ = 0;
    simp only [*, ne.def, not_false_iff, zero_mul, mul_zero] at * },
  specialize hφ aux.1, specialize hψ aux.2,
  rw finsupp.mem_antidiagonal at hde,
  classical,
  have hd' : d.support ⊆ d.support ∪ e.support := finset.subset_union_left _ _,
  have he' : e.support ⊆ d.support ∪ e.support := finset.subset_union_right _ _,
  rw [← hde, ← hφ, ← hψ, finset.sum_subset (finsupp.support_add),
    finset.sum_subset hd', finset.sum_subset he', ← finset.sum_add_distrib],
  { congr },
  all_goals { intros i hi, apply finsupp.not_mem_support_iff.mp },
end

section
variables [comm_semiring R]

variables {σ R}

lemma is_homogeneous_monomial (d : σ →₀ ℕ) (r : R) (n : ℕ) (hn : ∑ i in d.support, d i = n) :
  is_homogeneous (monomial d r) n :=
begin
  intros c hc,
  classical,
  rw coeff_monomial at hc,
  split_ifs at hc with h,
  { subst c, exact hn },
  { contradiction }
end
variables (σ) {R}

lemma is_homogeneous_of_total_degree_zero {p : mv_polynomial σ R} (hp : p.total_degree = 0) :
  is_homogeneous p 0 :=
begin
  erw [total_degree, finset.sup_eq_bot_iff] at hp,
  -- we have to do this in two steps to stop simp changing bot to zero
  simp_rw [mem_support_iff] at hp,
  exact hp,
end

lemma is_homogeneous_C (r : R) :
  is_homogeneous (C r : mv_polynomial σ R) 0 :=
begin
  apply is_homogeneous_monomial,
  simp only [finsupp.zero_apply, finset.sum_const_zero],
end

variables (σ R)

lemma is_homogeneous_zero (n : ℕ) : is_homogeneous (0 : mv_polynomial σ R) n :=
(homogeneous_submodule σ R n).zero_mem

lemma is_homogeneous_one : is_homogeneous (1 : mv_polynomial σ R) 0 :=
is_homogeneous_C _ _

variables {σ} (R)

lemma is_homogeneous_X (i : σ) :
  is_homogeneous (X i : mv_polynomial σ R) 1 :=
begin
  apply is_homogeneous_monomial,
  simp only [finsupp.support_single_ne_zero _ one_ne_zero, finset.sum_singleton],
  exact finsupp.single_eq_same
end

end

--TODO: continue translating to `weighted_homogeneous`

namespace is_homogeneous
variables [comm_semiring R] {φ ψ : mv_polynomial σ R} {m n : ℕ}

lemma coeff_eq_zero (hφ : is_homogeneous φ n) (d : σ →₀ ℕ) (hd : ∑ i in d.support, d i ≠ n) :
  coeff d φ = 0 :=
by { have aux := mt (@hφ d) hd, classical, rwa not_not at aux }

lemma inj_right (hm : is_homogeneous φ m) (hn : is_homogeneous φ n) (hφ : φ ≠ 0) :
  m = n :=
begin
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ,
  rw [← hm hd, ← hn hd]
end

lemma add (hφ : is_homogeneous φ n) (hψ : is_homogeneous ψ n) :
  is_homogeneous (φ + ψ) n :=
(homogeneous_submodule σ R n).add_mem hφ hψ

lemma sum {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ℕ)
  (h : ∀ i ∈ s, is_homogeneous (φ i) n) :
  is_homogeneous (∑ i in s, φ i) n :=
(homogeneous_submodule σ R n).sum_mem h

lemma mul (hφ : is_homogeneous φ m) (hψ : is_homogeneous ψ n) :
  is_homogeneous (φ * ψ) (m + n) :=
homogeneous_submodule_mul m n $ submodule.mul_mem_mul hφ hψ

lemma prod {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ι → ℕ)
  (h : ∀ i ∈ s, is_homogeneous (φ i) (n i)) :
  is_homogeneous (∏ i in s, φ i) (∑ i in s, n i) :=
begin
  classical,
  revert h,
  apply finset.induction_on s,
  { intro, simp only [is_homogeneous_one, finset.sum_empty, finset.prod_empty] },
  { intros i s his IH h,
    simp only [his, finset.prod_insert, finset.sum_insert, not_false_iff],
    apply (h i (finset.mem_insert_self _ _)).mul (IH _),
    intros j hjs,
    exact h j (finset.mem_insert_of_mem hjs) }
end

lemma total_degree (hφ : is_homogeneous φ n) (h : φ ≠ 0) :
  total_degree φ = n :=
begin
  rw total_degree,
  apply le_antisymm,
  { apply finset.sup_le,
    intros d hd,
    rw mem_support_iff at hd,
    rw [finsupp.sum, hφ hd], },
  { obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h,
    simp only [← hφ hd, finsupp.sum],
    replace hd := finsupp.mem_support_iff.mpr hd,
    exact finset.le_sup hd, }
end

/--
The homogeneous submodules form a graded ring. This instance is used by `direct_sum.comm_semiring`
and `direct_sum.algebra`. -/
instance homogeneous_submodule.gcomm_semiring :
  set_like.graded_monoid (homogeneous_submodule σ R) :=
{ one_mem := is_homogeneous_one σ R,
  mul_mem := λ i j xi xj, is_homogeneous.mul}

open_locale direct_sum
noncomputable example : comm_semiring (⨁ i, homogeneous_submodule σ R i) := infer_instance
noncomputable example : algebra R (⨁ i, homogeneous_submodule σ R i) := infer_instance

end is_homogeneous

section
noncomputable theory
open_locale classical
open finset

/-- `homogeneous_component n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneous_component` for the statement that `φ` is equal to the sum
of all its homogeneous components. -/
def homogeneous_component [comm_semiring R] (n : ℕ) :
  mv_polynomial σ R →ₗ[R] mv_polynomial σ R :=
(submodule.subtype _).comp $ finsupp.restrict_dom _ _ {d | ∑ i in d.support, d i = n}

section homogeneous_component
open finset
variables [comm_semiring R] (n : ℕ) (φ ψ : mv_polynomial σ R)

lemma coeff_homogeneous_component (d : σ →₀ ℕ) :
  coeff d (homogeneous_component n φ) = if ∑ i in d.support, d i = n then coeff d φ else 0 :=
by convert finsupp.filter_apply (λ d : σ →₀ ℕ, ∑ i in d.support, d i = n) φ d

lemma homogeneous_component_apply :
  homogeneous_component n φ =
  ∑ d in φ.support.filter (λ d, ∑ i in d.support, d i = n), monomial d (coeff d φ) :=
by convert finsupp.filter_eq_sum (λ d : σ →₀ ℕ, ∑ i in d.support, d i = n) φ

lemma homogeneous_component_is_homogeneous :
  (homogeneous_component n φ).is_homogeneous n :=
begin
  intros d hd,
  contrapose! hd,
  rw [coeff_homogeneous_component, if_neg hd]
end

@[simp]
lemma homogeneous_component_zero : homogeneous_component 0 φ = C (coeff 0 φ) :=
begin
  ext1 d,
  rcases em (d = 0) with (rfl|hd),
  { simp only [coeff_homogeneous_component, sum_eq_zero_iff, finsupp.zero_apply, if_true, coeff_C,
      eq_self_iff_true, forall_true_iff] },
  { rw [coeff_homogeneous_component, if_neg, coeff_C, if_neg (ne.symm hd)],
    simp only [finsupp.ext_iff, finsupp.zero_apply] at hd,
    simp [hd] }
end

@[simp]
lemma homogeneous_component_C_mul (n : ℕ) (r : R) :
  homogeneous_component n (C r * φ) = C r * homogeneous_component n φ :=
by simp only [C_mul', linear_map.map_smul]

lemma homogeneous_component_eq_zero' (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → ∑ i in d.support, d i ≠ n) :
  homogeneous_component n φ = 0 :=
begin
  rw [homogeneous_component_apply, sum_eq_zero],
  intros d hd, rw mem_filter at hd,
  exfalso, exact h _ hd.1 hd.2
end

lemma homogeneous_component_eq_zero (h : φ.total_degree < n) :
  homogeneous_component n φ = 0 :=
begin
  apply homogeneous_component_eq_zero',
  rw [total_degree, finset.sup_lt_iff] at h,
  { intros d hd, exact ne_of_lt (h d hd), },
  { exact lt_of_le_of_lt (nat.zero_le _) h, }
end

lemma sum_homogeneous_component :
  ∑ i in range (φ.total_degree + 1), homogeneous_component i φ = φ :=
begin
  ext1 d,
  suffices : φ.total_degree < d.support.sum d → 0 = coeff d φ,
    by simpa [coeff_sum, coeff_homogeneous_component],
  exact λ h, (coeff_eq_zero_of_total_degree_lt h).symm
end

lemma homogeneous_component_homogeneous_polynomial (m n : ℕ)
  (p : mv_polynomial σ R) (h : p ∈ homogeneous_submodule σ R n) :
  homogeneous_component m p = if m = n then p else 0 :=
begin
  simp only [mem_homogeneous_submodule] at h,
  ext x,
  rw coeff_homogeneous_component,
  by_cases zero_coeff : coeff x p = 0,
  { split_ifs,
    all_goals { simp only [zero_coeff, coeff_zero], }, },
  { rw h zero_coeff,
    simp only [show n = m ↔ m = n, from eq_comm],
    split_ifs with h1,
    { refl },
    { simp only [coeff_zero] } }
end

end homogeneous_component

end

end mv_polynomial
