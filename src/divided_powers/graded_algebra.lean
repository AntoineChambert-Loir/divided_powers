/- Copyright 2022 ACL & MIdFF-/

import algebra.free_algebra
import algebra.ring_quot
import algebra.triv_sq_zero_ext
import algebra.algebra.operations
import linear_algebra.multilinear.basic
import ring_theory.graded_algebra.basic
import ring_theory.tensor_product

import divided_powers.basic
import divided_powers.ideal_add
import ..weighted_homogeneous -- PR #17855

noncomputable theory

section
/- Here, the goal is to define a graded_algebra structure on mv_polynomial with respect to a given degree map… 
For the moment, I am stuck. -/

variables (R : Type*) [semiring R] 
variables (ι : Type*) [decidable_eq ι]
  {M : ι → Type* } [Π (i : ι), add_comm_monoid (M i)] [Π (i : ι), module R (M i)]
variables {N : Type*} [add_comm_monoid N] [module R N]

lemma yala 
  (g : Π (i : ι), N →ₗ[R] M i) 
  (hg : ∀ n, {i | g i n ≠ 0}.finite) 
  (h : Π (i : ι), M i →ₗ[R] N) (n : N) :
  (direct_sum.to_module R ι N h) (direct_sum.mk M (hg n).to_finset (λ i, g i n)) = finsum (λ i, h i (g i n)) :=
begin
  classical,
  suffices : (function.support ((λ (i : ι), (h i) ((g i) n)) ∘ plift.down)).finite, 
  let s := { i | g i n ≠ 0},
  unfold finsum, 
  rw dif_pos this,

  unfold direct_sum.mk,dsimp,
end

example (f : ℕ →+ ℕ) (a : ι →₀ ℕ) :
  f (finsupp.sum a (λ i m, m)) =
  finsupp.sum (finsupp.map_range f (f.map_zero) a) (λ i m, m)
:= 
begin
  rw map_finsupp_sum, 
  rw finsupp.sum_map_range_index, 
  intro i, refl, 
end

example (f : ℕ →+ ℕ) (a : ι → ℕ) (ha : (function.support a).finite):
  f (finsum a) = finsum (λ i, f (a i)) := add_monoid_hom.map_finsum f ha

#check yala


end


/-! 
The divided power algebra of a module -/

open finset mv_polynomial ring_quot

section graded_algebra
/-  The mv_polynomial algebra with a degree, as a graded algebra -/

namespace mv_polynomial

variables {R M : Type*} [comm_semiring R] [add_comm_monoid M] [decidable_eq M]

variables {σ : Type*}
variable (w : σ → M)
#check weighted_degree'
def w_degree : (σ →₀ ℕ) → M := λ p, finsupp.sum p (λ s n, n • (w s))

/- def weighted_degrees' (w : σ → M) (s : finset (σ →₀ ℕ)) : 
finset M := finset.image (weighted_degree' w) s -/

lemma weighted_homogeneous_component_mem (w : σ → M) (φ : mv_polynomial σ R) (m : M) :
  weighted_homogeneous_component w m φ ∈ weighted_homogeneous_submodule R w m :=
begin
  rw mem_weighted_homogeneous_submodule, 
  exact weighted_homogeneous_component_is_weighted_homogeneous m φ, 
end

example (s : finset ℕ) : s = ∅ ↔ s ⊆ ∅ :=
begin
  rw [← finset.bot_eq_empty, eq_bot_iff, le_iff_subset],
end

lemma decompose'_aux (φ : mv_polynomial σ R) (i : M) : 
  ite (i ∈ finset.image (weighted_degree' w) φ.support) ((weighted_homogeneous_component w i) φ) 0 = (weighted_homogeneous_component w i) φ :=
begin
  split_ifs with hi hi, 
  refl,
  apply symm,
  apply weighted_homogeneous_component_eq_zero', 
  simp only [mem_image, mem_support_iff, ne.def, exists_prop, not_exists, not_and] at hi, 
  intros m hm, 
  apply hi m, 
  rw mem_support_iff at hm, 
  exact hm, 
end

variable (R)

/-- The linear map from polynomials to the direct sum of the homogeneous components -/
def decompose' : mv_polynomial σ R →ₗ[R] direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i)) := {
to_fun  := λ φ, direct_sum.mk 
  (λ (i : M), ↥(weighted_homogeneous_submodule R w i))
  (finset.image (weighted_degree' w) φ.support)
  (λ m, ⟨weighted_homogeneous_component w m φ, weighted_homogeneous_component_mem w φ m⟩),
map_add'  := λ φ ψ,
begin
  rw dfinsupp.ext_iff,
  simp only [direct_sum.mk],
  intro i, 
  dsimp,
  rw ← subtype.coe_inj,
  rw submodule.coe_add, 
  simp only [apply_ite coe, subtype.coe_mk, submodule.coe_zero],
  simp only [decompose'_aux], 
  rw [map_add],
end,
map_smul' := 
begin
  intros a φ, 
  rw dfinsupp.ext_iff,
  simp only [direct_sum.mk],
  intro i, 
  dsimp,
  rw ← subtype.coe_inj,
  rw submodule.coe_smul, 
  simp only [apply_ite coe, subtype.coe_mk, submodule.coe_zero],
  simp only [decompose'_aux], rw [map_smul],
end }

#check decompose'

def decompose'_fun : mv_polynomial σ R → direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i)) := λ φ, direct_sum.mk 
  (λ (i : M), ↥(weighted_homogeneous_submodule R w i))
  (finset.image (weighted_degree' w) φ.support)
  (λ m, ⟨weighted_homogeneous_component w m φ, weighted_homogeneous_component_mem w φ m⟩)

lemma decompose'_add' : ∀ (φ ψ : mv_polynomial σ R), decompose'_fun R w (φ + ψ) = decompose'_fun R w φ + decompose'_fun R w ψ :=
begin
  intros φ ψ,
  simp only [decompose'_fun],
  rw dfinsupp.ext_iff,
  simp only [direct_sum.mk],
  intro i, 
  simp only [add_monoid_hom.coe_mk, dfinsupp.mk_apply],
  dsimp, 
  rw ← subtype.coe_inj,
  rw submodule.coe_add, 
  simp only [apply_dite coe, subtype.coe_mk, submodule.coe_zero, dite_eq_ite],
  simp only [decompose'_aux], 
  rw [map_add],
end

lemma decompose'_map_zero' : decompose'_fun R w 0 = 0 := 
begin
  simp only [decompose'_fun],
  rw dfinsupp.ext_iff,
  simp only [direct_sum.mk],
  intro i,
  simp only [mem_image, mem_support_iff, coeff_zero, ne.def, eq_self_iff_true, not_true, is_empty.exists_iff, exists_false,
  not_false_iff, add_monoid_hom.coe_mk, dfinsupp.mk_apply, dif_neg, direct_sum.zero_apply],
end

lemma direct_sum_one_coeffs (i : M) : 
  (((1 : direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i))) i) : mv_polynomial σ R) 
  = ite (i = 0) (1 : mv_polynomial σ R) (0 : mv_polynomial σ R) :=
begin
  conv_lhs { dsimp [has_one.one], }, 
  split_ifs,
  rw h,
  rw direct_sum.of_eq_same,
  refl,
  rw direct_sum.of_eq_of_ne,
  refl,
  exact ne.symm h,
end

lemma decompose'_map_one' : decompose'_fun R w 1 = 1 := 
begin
  classical,
  simp only [decompose'_fun],
  rw dfinsupp.ext_iff,
  simp only [direct_sum.mk],
  intro i,
  simp only [subtype.coe_mk, add_monoid_hom.coe_mk, dfinsupp.mk_apply],
  rw ← subtype.coe_inj,
  simp only [apply_dite coe, subtype.coe_mk, submodule.coe_zero, dite_eq_ite],
  simp only [decompose'_aux], 

  rw direct_sum_one_coeffs, 
  rw weighted_homogeneous_component_weighted_homogeneous_polynomial,
  swap,
  apply is_weighted_homogeneous_one,
  by_cases hi : i = 0,
  rw [if_pos, if_pos], exact hi, exact hi,
  rw [if_neg hi, if_neg], exact hi,
end

lemma decompose'_map_mul' : ∀ (φ ψ : mv_polynomial σ R), decompose'_fun R w (φ * ψ) = decompose'_fun R w φ * decompose'_fun R w ψ :=
begin
sorry,
end

/-- The alg_hom map from polynomials to the direct sum of the homogeneous components -/
def decompose'a : mv_polynomial σ R →ₐ[R] direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i)) := {
to_fun  := λ φ, direct_sum.mk 
  (λ (i : M), ↥(weighted_homogeneous_submodule R w i))
  (finset.image (weighted_degree' w) φ.support)
  (λ m, ⟨weighted_homogeneous_component w m φ, weighted_homogeneous_component_mem w φ m⟩),
map_add'  := decompose'_add' R w, 
/- map_smul' := 
begin
  intros a φ, 
  rw dfinsupp.ext_iff,
  simp only [direct_sum.mk],
  intro i, 
  dsimp,
  rw ← subtype.coe_inj,
  rw submodule.coe_smul, 
  simp only [apply_ite coe, subtype.coe_mk, submodule.coe_zero],
  simp only [decompose'_aux], rw [map_smul],
end, -/
map_mul'  := 
begin
  intros φ ψ,
  rw dfinsupp.ext_iff,
  simp only [direct_sum.mk],
  intro i, 
  -- dsimp,
  rw ← subtype.coe_inj,
  sorry,
  /- 
  rw submodule.coe_mul, 
  simp only [apply_ite coe, subtype.coe_mk, submodule.coe_zero],
  simp only [decompose'_aux], rw [map_mul], -/
end, 
map_one'  := decompose'_map_one' R w, 
map_zero' := decompose'_map_zero' R w,
commutes' := sorry }

/- Better approach : this will work! -/
example : direct_sum.is_internal
  (λ (i : M), (weighted_homogeneous_submodule R w i))
  := 
begin
  classical,
  split,
  { -- injectivity
    intros p q,
    intro hpq,
    rw mv_polynomial.ext_iff  at hpq, 
    ext, 
    specialize hpq m, 
  rw [← direct_sum.sum_support_of _ p, ← direct_sum.sum_support_of _ q ] at hpq, 
  simp only [map_sum, direct_sum.coe_add_monoid_hom_of, mv_polynomial.coeff_sum] at hpq,
  by_cases hi : weighted_degree' w m = i,
  rw [finset.sum_eq_single i, finset.sum_eq_single i] at hpq, 
  exact hpq, 
  }
end


def graded_polynomial_algebra : graded_algebra 
(λ (m : M), weighted_homogeneous_submodule R w m) := graded_algebra.of_alg_hom (λ (m : M), weighted_homogeneous_submodule R w m) (decompose'a R w) (sorry) (sorry) 


end mv_polynomial

end graded_algebra