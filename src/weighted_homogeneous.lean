import algebra.direct_sum.internal
import algebra.graded_monoid
import data.mv_polynomial.variables

-- TODO: fix comments

/-!
# Homogeneous polynomials

It is possible to assign weights (in an arbitrary monoid- to the variables 
of a multivariate polynomial ring, so that monomials of the ring 
then have a weighted degree with respect  to the weights of the variables. 

A multivariate polynomial `φ` is homogeneous of weighted degree `n`
if all monomials occuring in `φ` have the same weighted degree `n`.

## Main definitions/lemmas

* `is_homogeneous φ n`: a predicate that asserts that `φ` is homogeneous 
of weighted degree `n`.

* `homogeneous_submodule σ R n`: the submodule of homogeneous polynomials 
of weighted degree `n`.

* `homogeneous_component n`: the additive morphism that projects polynomials
onto their summand that is homogeneous of degree `n`.

* `sum_homogeneous_component`: every polynomial is the sum of its homogeneous 
components

-/

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra

--universes u v w
--variables {R : Type u} {S : Type v} {M : Type w}

variables {R M : Type*} [comm_semiring R] 

namespace mv_polynomial
variables {σ : Type*}

section add_comm_monoid
variables [add_comm_monoid M]


/-! ### `weighted_degree'` -/


-- I'm renaming this to save `weighted_degree` for the one taking an mv_polynomial as input

-- Redefine `weighted_degree'` as an add_hom, this saves `pow` !
def weighted_degree' (w : σ → M) : (σ →₀ ℕ) →+ M := {
to_fun := λ s, finsum (λ (i : σ), (s i) • (w i)),
map_add' := λ s t, 
begin
  simp only [finsupp.coe_add, pi.add_apply, add_smul], 
  exact finsum_add_distrib
    (finite.subset s.finite_support (function.support_smul_subset_left s w))
    (finite.subset t.finite_support (function.support_smul_subset_left t w)),
    end,
map_zero' := 
  by simp only [finsupp.coe_zero, pi.zero_apply, zero_smul, finsum_zero] }

/-
/-- The `weighted degree'` of the monomial a*∏x_i^s_i is the sum ∑n_i*(wt x_i)  -/
def weighted_degree' (w : σ → M) (s : σ →₀ ℕ) /- (a : R) -/ : M :=
finsum (λ (i : σ), (s i) • (w i))
--∑ i in s.support, (s i) • (w i) --potential alternative def

namespace weighted_degree'

/-- The `weighted degree` of the product of monomials s * t is  the sum of their
  weighted degrees  -/
lemma mul (w : σ → M) (s t : σ →₀ ℕ) : 
  weighted_degree' w (s + t) = weighted_degree' w s + weighted_degree' w t :=
begin
  simp only [weighted_degree', finsupp.coe_add, pi.add_apply, add_smul],
  exact finsum_add_distrib 
    (finite.subset s.finite_support (function.support_smul_subset_left s w))
    (finite.subset t.finite_support (function.support_smul_subset_left t w))
end

lemma zero (w : σ → M)  : weighted_degree' w 0 = 0 :=
by simp only [weighted_degree', finsupp.coe_zero, pi.zero_apply, zero_smul, finsum_zero]

lemma pow (w : σ → M) (s : σ →₀ ℕ) (n : ℕ) :
  weighted_degree' w (n • s) = n • weighted_degree' w s :=
begin
  induction n with k hk,
  { simp only [zero_smul, zero] },
  { simp only [succ_nsmul, mul, hk] },
end

/- def weighted_degree'' [has_Sup M] (w : σ → M) (φ : mv_polynomial σ R) : with_bot M :=
⨆ d ∈ { d | coeff d φ ≠ 0}, ((weighted_degree' w d) : with_bot M)  -/

/- def weighted_degree' (w : σ → M) (φ : mv_polynomial σ R) : with_bot M :=
⨆ ⦃d : σ →₀ ℕ⦄,  if coeff d φ ≠ 0 then ((weighted_degree' w d) : with_bot M) else ⊥ -/

end weighted_degree'
-/

example (w : σ → M) (s : σ →₀ ℕ) (n : ℕ) :
  weighted_degree' w (n • s) = n • weighted_degree' w s :=
map_nsmul (weighted_degree' w) n s

example [has_Sup M]: has_Sup (with_bot M) :=
begin
exact with_bot.has_Sup,
end 

/-- Weighted total degree of a multivariate polynomial -/
def weighted_total_degree [semilattice_sup M] (w : σ → M) (p : mv_polynomial σ R) : with_bot M := 
p.support.sup (λ s, weighted_degree' w s)

/-- A multivariate polynomial `φ` is homogeneous of weighted degree `m` if all monomials 
  occuring in `φ` have weighted degree `m`. -/
def is_weighted_homogeneous (w : σ → M) (φ : mv_polynomial σ R) (m : M) : Prop := 
∀ ⦃d⦄, coeff d φ ≠ 0 → weighted_degree' w d = m 

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
  finsupp.supported _ R {d | weighted_degree' w d = m} :=
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
  rw [← hde, ← hφ, ← hψ, map_add],
end

lemma is_weighted_homogeneous_monomial (w : σ → M) (d : σ →₀ ℕ) (r : R) {m : M} 
  (hm : weighted_degree' w d = m) : is_weighted_homogeneous w (monomial d r) m :=
begin
  intros c hc,
  classical,
  rw coeff_monomial at hc,
  split_ifs at hc with h,
  { subst c, exact hm },
  { contradiction }
end

lemma is_weighted_homogeneous_of_total_degree_zero (w : σ → M) {p : mv_polynomial σ R} 
  (hp : weighted_total_degree w p = 0) : is_weighted_homogeneous w p 0 :=
begin
  erw [total_degree, finset.sup_eq_bot_iff] at hp,
  -- we have to do this in two steps to stop simp changing bot to zero
  simp_rw [mem_support_iff] at hp,
  intros d hd,
  simp only [weighted_degree'],
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
is_weighted_homogeneous_monomial _ _ _ (map_zero _)

variables (R)

lemma is_weighted_homogeneous_zero (w : σ → M) (m : M) : 
  is_weighted_homogeneous w (0 : mv_polynomial σ R) m :=
(weighted_homogeneous_submodule R w m).zero_mem

lemma is_weighted_homogeneous_one (w : σ → M) :
  is_weighted_homogeneous w (1 : mv_polynomial σ R) 0 :=
is_weighted_homogeneous_C _ _

variables {σ} (R)

lemma is_weighted_homogeneous_X (w : σ → M) (i : σ) :
  is_weighted_homogeneous w (X i : mv_polynomial σ R) (w i) :=
begin
  apply is_weighted_homogeneous_monomial,
  simp only [weighted_degree', add_monoid_hom.coe_mk, single_smul, one_smul], 
--  simp only [weighted_degree', single_smul, one_smul, single_apply, ite_smul, zero_smul],
  rw finsum_eq_single _ i,
  { rw single_eq_same, },
  { intros j hj, rw single_eq_of_ne hj.symm, }
end

namespace is_weighted_homogeneous
variables {R} {φ ψ : mv_polynomial σ R} {m n : M}

lemma coeff_eq_zero {w : σ → M} (hφ : is_weighted_homogeneous w φ n) (d : σ →₀ ℕ) 
  (hd : weighted_degree' w d ≠ n) : coeff d φ = 0 :=
by { have aux := mt (@hφ d) hd, classical, rwa not_not at aux }

lemma inj_right {w : σ → M} (hm : is_weighted_homogeneous w φ m)
  (hn : is_weighted_homogeneous w φ n) (hφ : φ ≠ 0) : m = n :=
begin
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ,
  rw [← hm hd, ← hn hd]
end

lemma add {w : σ → M} (hφ : is_weighted_homogeneous w φ n) (hψ : is_weighted_homogeneous w ψ n) :
  is_weighted_homogeneous w (φ + ψ) n :=
(weighted_homogeneous_submodule R w n).add_mem hφ hψ

lemma sum  {ι : Type*} (s : finset ι)  (φ : ι → mv_polynomial σ R) (n : M) {w : σ → M}
  (h : ∀ i ∈ s, is_weighted_homogeneous w (φ i) n) :
  is_weighted_homogeneous w (∑ i in s, φ i) n :=
(weighted_homogeneous_submodule R w n).sum_mem h

lemma mul {w : σ → M} (hφ : is_weighted_homogeneous w φ m) (hψ : is_weighted_homogeneous w ψ n) :
  is_weighted_homogeneous w (φ * ψ) (m + n) :=
weighted_homogeneous_submodule_mul w m n $ submodule.mul_mem_mul hφ hψ

lemma prod {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ι → M) {w : σ → M}
  (h : ∀ i ∈ s, is_weighted_homogeneous w (φ i) (n i)) :
  is_weighted_homogeneous w (∏ i in s, φ i) (∑ i in s, n i) :=
begin
  classical,
  revert h,
  apply finset.induction_on s,
  { intro, simp only [is_weighted_homogeneous_one, finset.sum_empty, finset.prod_empty] },
  { intros i s his IH h,
    simp only [his, finset.prod_insert, finset.sum_insert, not_false_iff],
    apply (h i (finset.mem_insert_self _ _)).mul (IH _),
    intros j hjs,
      exact h j (finset.mem_insert_of_mem hjs) }
end

/-- A non zero weighted homogeneous polynomial of degree n has weighted total degree n -/
lemma weighted_total_degree [semilattice_sup M] {w : σ → M} (hφ : is_weighted_homogeneous w φ n) (h : φ ≠ 0) :
  weighted_total_degree w φ = n :=
begin
  simp only [weighted_total_degree],
  apply le_antisymm,
  { simp only [is_weighted_homogeneous] at hφ,
    simp only [finset.sup_le_iff, mem_support_iff, with_bot.coe_le_coe],
    exact λ d hd, le_of_eq (hφ hd), },
  { obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h,
    simp only [← hφ hd, finsupp.sum],
    replace hd := finsupp.mem_support_iff.mpr hd,
    exact finset.le_sup hd, }
end 

--TODO: decide if these should be instances or defs

/--
The homogeneous submodules form a graded ring. This instance is used by `direct_sum.comm_semiring`
and `direct_sum.algebra`. -/
instance weighted_homogeneous_submodule.gcomm_semiring {w : σ → M} :
  set_like.graded_monoid (weighted_homogeneous_submodule R w) :=
{ one_mem := is_weighted_homogeneous_one R w,
  mul_mem := λ i j xi xj, is_weighted_homogeneous.mul }


open_locale direct_sum
noncomputable example {w : σ → M} : comm_semiring (⨁ i, weighted_homogeneous_submodule R w i) := 
infer_instance
noncomputable example {w : σ → M} : algebra R (⨁ i, weighted_homogeneous_submodule R w i) := 
infer_instance
end is_weighted_homogeneous


section
--noncomputable theory
--open_locale classical
open finset

variables {R}

/-- `weighted_homogeneous_component w n φ` is the part of `φ` that is weighted homogeneous of 
degree `n`, with respect to the weights `w`.
See `sum_weighted_homogeneous_component` for the statement that `φ` is equal to the sum
of all its weighted homogeneous components. -/
def weighted_homogeneous_component (w : σ → M) (n : M) :
  mv_polynomial σ R →ₗ[R] mv_polynomial σ R :=
(submodule.subtype _).comp $ finsupp.restrict_dom _ _ {d | weighted_degree' w d = n}

section weighted_homogeneous_component
open finset
variables {w : σ → M} (n : M) (φ ψ : mv_polynomial σ R)

lemma coeff_weighted_homogeneous_component (d : σ →₀ ℕ) :
  coeff d (weighted_homogeneous_component w n φ) = 
    if weighted_degree' w d = n then coeff d φ else 0 :=
by convert finsupp.filter_apply (λ d : σ →₀ ℕ, weighted_degree' w d = n) φ d

lemma weighted_homogeneous_component_apply :
  weighted_homogeneous_component w n φ =
  ∑ d in φ.support.filter (λ d, weighted_degree' w d = n), monomial d (coeff d φ) :=
by convert finsupp.filter_eq_sum (λ d : σ →₀ ℕ, weighted_degree' w d = n) φ

lemma weighted_homogeneous_component_is_weighted_homogeneous :
  (weighted_homogeneous_component w n φ).is_weighted_homogeneous w n :=
begin
  intros d hd,
  contrapose! hd,
  rw [coeff_weighted_homogeneous_component, if_neg hd]
end

@[simp]
lemma weighted_homogeneous_component_C_mul (n : M) (r : R) :
  weighted_homogeneous_component w n (C r * φ) = C r * weighted_homogeneous_component w n φ :=
by simp only [C_mul', linear_map.map_smul]

lemma weighted_homogeneous_component_eq_zero' (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → 
  weighted_degree' w d ≠ n) : weighted_homogeneous_component w n φ = 0 :=
begin
  rw [weighted_homogeneous_component_apply, sum_eq_zero],
  intros d hd, rw mem_filter at hd,
  exfalso, exact h _ hd.1 hd.2
end

lemma _root_.finset.lt_of_lt_sup (α :Type*) [semilattice_sup α] (ι : Type*)(s : finset ι) (f : ι → α) (a : α)
  (h : finset.sup s (λ i, (f i : with_bot α)) < (a : with_bot α)) : ∀ i ∈ s, f i < a :=
begin
  simp only [lt_iff_le_not_le, finset.sup_le_iff, with_bot.coe_le_coe] at h,
  intros i hi,
  rw lt_iff_le_not_le,
  split,
  exact h.1 i hi, 
  intro h',
  exact h.2 (le_trans (with_bot.coe_le_coe.mpr h') (finset.le_sup hi)), 
end

--TODO: come back after defining weighted_total_degree
lemma weighted_homogeneous_component_eq_zero [semilattice_sup M] (h : weighted_total_degree w φ < n) :
  weighted_homogeneous_component w n φ = 0 :=
begin
  apply weighted_homogeneous_component_eq_zero',
  simp only [weighted_total_degree] at h, 
  intros d hd, 
  rw [weighted_total_degree, finset.sup_lt_iff] at h,
  { intros d hd, exact ne_of_lt (h d hd), },
  { exact lt_of_le_of_lt (nat.zero_le _) h, }
end 

lemma sum_weighted_homogeneous_component :
  ∑ i in range (φ.total_degree + 1), weighted_homogeneous_component w i φ = φ :=
begin
  ext1 d,
  suffices : φ.total_degree < d.support.sum d → 0 = coeff d φ,
    by simpa [coeff_sum, coeff_homogeneous_component],
  exact λ h, (coeff_eq_zero_of_total_degree_lt h).symm
end

lemma weighted_homogeneous_component_weighted_homogeneous_polynomial (m n : M)
  (p : mv_polynomial σ R) (h : p ∈ weighted_homogeneous_submodule R w n) :
  weighted_homogeneous_component w m p = if m = n then p else 0 :=
begin
  simp only [mem_weighted_homogeneous_submodule] at h,
  ext x,
  rw coeff_weighted_homogeneous_component,
  by_cases zero_coeff : coeff x p = 0,
  { split_ifs,
    all_goals { simp only [zero_coeff, coeff_zero], }, },
  { rw h zero_coeff,
    simp only [show n = m ↔ m = n, from eq_comm],
    split_ifs with h1,
    { refl },
    { simp only [coeff_zero] } }
end

end weighted_homogeneous_component

end

end add_comm_monoid

section canonically_ordered_add_monoid

open finset

variables [canonically_ordered_add_monoid M] {w : σ → M} (φ : mv_polynomial σ R)


-- TODO: Q : Can we make this stronger?
@[simp]
lemma weighted_homogeneous_component_zero [no_zero_smul_divisors ℕ M] 
  (hw : ∀ i : σ, w i ≠ 0) : 
  weighted_homogeneous_component w 0 φ = C (coeff 0 φ) :=
begin
  ext1 d,
  rcases em (d = 0) with (rfl|hd),
  { simp only [coeff_weighted_homogeneous_component, weighted_degree',if_pos, add_monoid_hom.coe_mk, finsupp.coe_zero, pi.zero_apply, zero_smul, finsum_zero, coeff_zero_C], },
  { rw [coeff_weighted_homogeneous_component, if_neg, coeff_C, if_neg (ne.symm hd)],
    simp only [weighted_degree', add_monoid_hom.coe_mk],
    have h : function.support (λ (i : σ), d i • w i) ⊆ d.support,
    { erw function.support_smul,
      simp only [fun_support_eq, set.inter_subset_left] },
    rw finsum_eq_sum_of_support_subset _ h,
    simp only [sum_eq_zero_iff, finsupp.mem_support_iff, ne.def, not_forall, exists_prop,
      smul_eq_zero, not_or_distrib, and_self_left],
    simp only [finsupp.ext_iff, finsupp.coe_zero, pi.zero_apply, not_forall] at hd,
    obtain ⟨i, hi⟩ := hd,
    exact ⟨i, hi, hw i⟩,}
end

end canonically_ordered_add_monoid

end mv_polynomial