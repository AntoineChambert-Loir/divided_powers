/- Copyright 2022 ACL & MIdFF-/

import algebra.module.graded_module

section direct_sum

universes u v w 
variables {ι : Type v} [decidable_eq ι]

section mk

variables {β : ι → Type w} [Π (i : ι), add_comm_monoid (β i)]

lemma direct_sum.mk_apply_of_mem {s : finset ι} {f : Π (i : (↑s : set ι)), β i.val}
  {n : ι} (hn : n ∈ s):
  direct_sum.mk β s f n = f ⟨n, hn⟩ := 
by simp only [direct_sum.mk, add_monoid_hom.coe_mk, dfinsupp.mk_apply, dif_pos hn]

lemma direct_sum.mk_apply_of_not_mem {s : finset ι} {f : Π (i : (↑s : set ι)), β i.val}
  {n : ι} (hn : n ∉ s):
  direct_sum.mk β s f n = 0 := 
by simp only [direct_sum.mk, add_monoid_hom.coe_mk, dfinsupp.mk_apply, dif_neg hn]

end mk

section internal

variables {M : Type w} [decidable_eq M] [add_comm_monoid M] 

lemma direct_sum.coe_add_monoid_hom_eq_dfinsupp_sum  
  {M : Type w} [decidable_eq M] [add_comm_monoid M] 
  (A : ι → add_submonoid M) (x : direct_sum ι (λ i, A i)) :
  direct_sum.coe_add_monoid_hom A x = dfinsupp.sum x (λ i, coe):= 
by simp only [direct_sum.coe_add_monoid_hom, direct_sum.to_add_monoid, 
  dfinsupp.lift_add_hom, add_equiv.coe_mk, dfinsupp.sum_add_hom_apply, 
  add_submonoid_class.coe_subtype]

lemma direct_sum.coe_linear_map_eq_dfinsupp_sum 
  {R : Type u} [semiring R] [module R M] (A : ι → submodule R M) 
  (x : direct_sum ι (λ i, A i)) :
  direct_sum.coe_linear_map A x = dfinsupp.sum x (λ i, coe):= 
by simp only [direct_sum.coe_linear_map, direct_sum.to_module, dfinsupp.lsum, 
  linear_equiv.coe_mk, linear_map.coe_mk, dfinsupp.sum_add_hom_apply, 
  linear_map.to_add_monoid_hom_coe, submodule.coe_subtype]

lemma direct_sum.support_subset (A : ι → add_submonoid M) 
  (x : direct_sum ι (λ i, A i)) :
  function.support  (λ i, (x i : M)) ⊆ ↑(dfinsupp.support x) := 
begin
  intro m,
  rw [function.mem_support, finset.mem_coe, dfinsupp.mem_support_to_fun, not_imp_not],
  intro hm', 
  rw [hm', add_submonoid.coe_zero],
end

lemma direct_sum.support_subset_submodule (R : Type*) [comm_semiring R]
  [module R M] (A : ι → submodule R M) 
  (x : direct_sum ι (λ i, A i)) :
  function.support  (λ i, (x i : M)) ⊆ ↑(dfinsupp.support x) := 
begin
  intro m,
  rw [function.mem_support, finset.mem_coe, dfinsupp.mem_support_to_fun, not_imp_not],
  intro hm', 
  simp only [hm', submodule.coe_zero],
end

lemma direct_sum.finite_support (A : ι → add_submonoid M) 
  (x : direct_sum ι (λ i, A i)) :
  (function.support (λ i, (x i : M))).finite := 
set.finite.subset (dfinsupp.support x : set ι).to_finite (direct_sum.support_subset _ x)

end internal

end direct_sum

section

theorem linear_map.map_finsum {α R S M N : Type*} [semiring R] [semiring S] (σ : R →+* S)
  [add_comm_monoid M] [add_comm_monoid N]  [module R M] [module S N] {f : α → M} (g : M →ₛₗ[σ] N)
  (hf : (function.support f).finite) :
  g (finsum (λ (i : α), f i)) = finsum (λ (i : α), g (f i)) := 
begin
  rw ← linear_map.to_add_monoid_hom_coe,
  exact add_monoid_hom.map_finsum _ hf,
end

end

noncomputable theory

section direct_sum

open direct_sum

/- Given an R-algebra A and a family (ι → submodule R A) of submodules
parameterized by an additive monoid
and statisfying `set_like.graded_monoid M` (essentially, is multiplicative)
such that `direct_sum.is_internal M` (A is the direct sum of the M i),
we endow A with the structure of a graded algebra.
The submodules are the *homogeneous* parts -/


variables (R : Type*) [comm_semiring R] (A : Type*) [comm_semiring A] [algebra R A]
variables (ι : Type*) [decidable_eq ι]

variables (M : ι → submodule R A) [add_monoid ι] [set_like.graded_monoid M]

variables {R A ι M}

-- The following lines were given on Zulip by Adam Topaz

def direct_sum.is_internal.coe_alg_iso (hM : direct_sum.is_internal M) :
  direct_sum ι (λ i, ↥(M i)) ≃ₐ[R] A :=
{ commutes' := λ r, by simp,
  ..(ring_equiv.of_bijective (direct_sum.coe_alg_hom M) hM) }

def direct_sum.is_internal.graded_algebra (hM : direct_sum.is_internal M) :
  graded_algebra M :=
{ decompose' := hM.coe_alg_iso.symm, 
    -- (coe_alg_iso_of_is_internal hM).symm,
  left_inv := hM.coe_alg_iso.symm.left_inv, 
    -- (coe_alg_iso_of_is_internal hM).symm.left_inv,
  right_inv := hM.coe_alg_iso.left_inv, 
  -- (coe_alg_iso_of_is_internal hM).left_inv,
  ..(infer_instance : set_like.graded_monoid M) }

def direct_sum.decomposition.graded_algebra (dM : direct_sum.decomposition M) :
  graded_algebra M :=
{ to_decomposition  := dM,
  ..(infer_instance : set_like.graded_monoid M) }

end direct_sum

#exit


section weighted_homogeneous

/- Here, given a weight `w : σ → M`, where `M` is an additive and commutative monoid, we endow the
  ring of multivariate polynomials `mv_polynomial σ R` with the structure of a graded algebra -/

variables {R : Type*} [comm_semiring R] 
variables {M : Type*} [add_comm_monoid M] [decidable_eq M]
variables {σ : Type*}
variable (w : σ → M)

namespace mv_polynomial

lemma weighted_homogeneous_component_mem (w : σ → M) (φ : mv_polynomial σ R) 
  (m : M) :
  weighted_homogeneous_component R w m φ ∈ weighted_homogeneous_submodule R w m :=
begin
  rw mem_weighted_homogeneous_submodule, 
  exact weighted_homogeneous_component_is_weighted_homogeneous m φ, 
end

/- 
lemma toto (p : Prop) [decidable p] (u v : M) : 
  (ite p u v = u) ↔ (¬ p → u = v) := 
begin
  by_cases hp : p, 
  simp only [hp, if_true, eq_self_iff_true, not_true, is_empty.forall_iff],
  simp only [hp, if_false, not_false_iff, forall_true_left],
  exact comm,
end
 -/

lemma decompose'_aux (φ : mv_polynomial σ R) (i : M) 
  (hi : i ∉ finset.image (weighted_degree' w) φ.support) : 
  weighted_homogeneous_component R w i φ = 0 :=
begin
  apply weighted_homogeneous_component_eq_zero', 
  simp only [finset.mem_image, mem_support_iff, ne.def, exists_prop, not_exists, not_and] at hi, 
  intros m hm, 
  apply hi m, 
  rw mem_support_iff at hm, 
  exact hm, 
end

/- 
lemma decompose'_aux' (φ : mv_polynomial σ R) (i : M) : 
  ite (i ∈ finset.image (weighted_degree' w) φ.support) 
    ((weighted_homogeneous_component R w i) φ) 0 
    = (weighted_homogeneous_component R w i) φ :=
begin
  split_ifs with hi hi,
  refl,
  rw decompose'_aux w φ i hi, 
end -/

variable (R)
def decompose'_fun := λ (φ : mv_polynomial σ R), direct_sum.mk 
  (λ (i : M), ↥(weighted_homogeneous_submodule R w i))
  (finset.image (weighted_degree' w) φ.support)
  (λ m, ⟨weighted_homogeneous_component R w m φ, weighted_homogeneous_component_mem w φ m⟩)

lemma decompose'_fun_apply (φ : mv_polynomial σ R) (m : M):
  (decompose'_fun R w φ m : mv_polynomial σ R) = 
  weighted_homogeneous_component R w m φ := 
begin
  rw decompose'_fun,
  by_cases hm :  m ∈ finset.image (weighted_degree' w) φ.support,
  simp only [direct_sum.mk_apply_of_mem hm, subtype.coe_mk], 
  rw [direct_sum.mk_apply_of_not_mem hm, submodule.coe_zero, decompose'_aux w φ m hm],
end

instance [decidable_eq σ] [decidable_eq R] :
  Π (i : M) (x : ↥(weighted_homogeneous_submodule R w i)), decidable (x ≠ 0) :=
begin
  intros m x,
  rw [ne.def, ← set_like.coe_eq_coe], 
  apply_instance,
end

-- Rewrite direct_sum.coe_linear_map
lemma direct_sum.coe_linear_map_eq_support_sum [decidable_eq σ] [decidable_eq R]
  (x : direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i))) :
  ((direct_sum.coe_linear_map (λ (i : M), weighted_homogeneous_submodule R w i)) x) = 
  dfinsupp.sum x  (λ m, coe) :=
begin
  rw direct_sum.coe_linear_map_eq_dfinsupp_sum, 
  -- WEIRD: this is not yet finished
  simp only [dfinsupp.sum],
  apply finset.sum_congr,
  ext m, 
  simp only [dfinsupp.mem_support_iff],
  intros m hm, refl,
end

-- Rewrite direct_sum.coe_add_monoid_hom
lemma direct_sum.coe_add_monoid_hom_eq_support_sum [decidable_eq σ] [decidable_eq R]
  (x : direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i))) :
  ((direct_sum.coe_add_monoid_hom (λ (i : M), weighted_homogeneous_submodule R w i)) x) = 
  dfinsupp.sum x  (λ m, coe) :=
  direct_sum.coe_linear_map_eq_support_sum R w x

-- Variants for finsum
lemma direct_sum.coe_linear_map_eq_finsum [decidable_eq σ] [decidable_eq R]
  (x : direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i))) 
  /- [h_dec : Π (i : M) (x : ↥(weighted_homogeneous_submodule R w i)), decidable (x ≠ 0)]  -/: 
  ((direct_sum.coe_linear_map (λ (i : M), weighted_homogeneous_submodule R w i)) x) = 
  finsum (λ m, x m) :=
begin
  rw [direct_sum.coe_linear_map_eq_support_sum, dfinsupp.sum],
  rw finsum_eq_sum_of_support_subset, 
  -- direct_sum.support_subset ne marche pas…
  intro m, 
  rw [function.mem_support, finset.mem_coe, dfinsupp.mem_support_to_fun, not_imp_not],
  intro hm', 
  rw [hm', submodule.coe_zero],
end

lemma direct_sum.coe_add_monoid_hom_eq_finsum [decidable_eq σ] [decidable_eq R]
  (x : direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i))) 
  /- [h_dec : Π (i : M) (x : ↥(weighted_homogeneous_submodule R w i)), decidable (x ≠ 0)]  -/: 
  ((direct_sum.coe_add_monoid_hom (λ (i : M), weighted_homogeneous_submodule R w i)) x) = 
  finsum (λ m, x m) :=
  direct_sum.coe_linear_map_eq_finsum R w x

-- TODO: move to weighted_homogeneous file
lemma weighted_homogeneous_component_weighted_homogeneous_polynomial' (m : M)
  (x : weighted_homogeneous_submodule R w m) :
  (weighted_homogeneous_component  R w m) ↑x = x :=
by rw [weighted_homogeneous_component_weighted_homogeneous_polynomial m m _ x.prop, if_pos rfl]
 
lemma weighted_homogeneous_component_direct_sum [decidable_eq σ] [decidable_eq R]
  (x : direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i))) (m : M) : 
  (weighted_homogeneous_component R w m) 
    ((direct_sum.coe_linear_map (λ (i : M), weighted_homogeneous_submodule R w i)) x) = x m :=
begin
  rw [direct_sum.coe_linear_map_eq_dfinsupp_sum],
  rw dfinsupp.sum, 
  rw map_sum, 
  rw finset.sum_eq_single m, 
  { rw weighted_homogeneous_component_of_weighted_homogeneous_polynomial_same,
    rw ← mem_weighted_homogeneous_submodule, 
    exact (x m).prop, },
  { intros n hn hmn, 
    rw weighted_homogeneous_component_of_weighted_homogeneous_polynomial_other,
    rw ← mem_weighted_homogeneous_submodule, 
    exact (x n).prop, exact ne.symm hmn, },
  { rw dfinsupp.not_mem_support_iff, 
    intro hm, rw [hm, submodule.coe_zero, map_zero], },
end

def mv_polynomial_weighted_decomposition [decidable_eq σ] [decidable_eq R] : 
  direct_sum.decomposition (weighted_homogeneous_submodule R w) := 
{ decompose'  := decompose'_fun R w,
  left_inv    := λ φ,
  begin
    conv_rhs { rw [← sum_weighted_homogeneous_component w φ], },
    rw ← direct_sum.sum_support_of (λ m, ↥(weighted_homogeneous_submodule R w m))
      (decompose'_fun R w φ),
    simp only [direct_sum.coe_add_monoid_hom_of, mv_polynomial.coeff_sum, map_sum],
    apply congr_arg2,
    { ext m,
      simp only [dfinsupp.mem_support_to_fun, ne.def, set.finite.mem_to_finset,
        function.mem_support, not_iff_not],
      conv_lhs { rw ← subtype.coe_inj },
      rw [decompose'_fun_apply, submodule.coe_zero], },
    { apply funext, intro m, rw decompose'_fun_apply, },
  end,
  right_inv   := λ x,
  begin
    apply dfinsupp.ext, intro m, 
    rw ← subtype.coe_inj, 
    rw decompose'_fun_apply, 
    change (weighted_homogeneous_component R w m) ((direct_sum.coe_linear_map (weighted_homogeneous_submodule R w)) x) = ↑(x m), 
    rw direct_sum.coe_linear_map_eq_dfinsupp_sum, 
    rw dfinsupp.sum,
    rw map_sum, 
    rw finset.sum_eq_single m,
    { rw weighted_homogeneous_component_of_weighted_homogeneous_polynomial_same,
      exact (x m).prop,  },
    { intros n hn hmn, 
      rw weighted_homogeneous_component_of_weighted_homogeneous_polynomial_other,
      exact (x n).prop,
      exact ne.symm hmn, },
    { intro hm, rw dfinsupp.not_mem_support_iff at hm, 
      simp only [hm, submodule.coe_zero, map_zero], },
  end }

/-- mv_polynomial as a graded algebra, for an arbitrary weight -/
def mv_polynomial_weighted_graded_algebra 
  [decidable_eq σ] [decidable_eq R] : 
  graded_algebra (weighted_homogeneous_submodule R w) :=
{ to_decomposition  := mv_polynomial_weighted_decomposition R w,
  to_graded_monoid  := infer_instance, }

end mv_polynomial

end weighted_homogeneous

#exit --Unused draft below


/- import algebra.free_algebra
import algebra.ring_quot
import algebra.triv_sq_zero_ext
import algebra.algebra.operations
import linear_algebra.multilinear.basic
import ring_theory.graded_algebra.basic
import ring_theory.tensor_product

import divided_powers.basic
import divided_powers.ideal_add
import ..weighted_homogeneous -- PR #17855
 -/

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
fintype
lemma decompose'_fun_coe_apply (φ : mv_polynomial σ R) (m : M) : (decompose'_fun R w φ m : mv_polynomial σ R) = weighted_homogeneous_component w m φ := 
begin
  simp only [decompose'_fun],
--   simp only [direct_sum.mk, dfinsupp.mk_apply],
  simp only [direct_sum.mk, subtype.coe_mk, add_monoid_hom.coe_mk, dfinsupp.mk_apply, apply_dite coe, dite_eq_ite],
  exact decompose'_aux w φ m, 
end

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
lemma is_internal_direct_sum_of_weighted_homogeneous_submodules : 
  direct_sum.is_internal (weighted_homogeneous_submodule R w) := 
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
    { suffices this : ∀ (x : direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i))) (c : M), c ≠ i → coeff m ((x c) : mv_polynomial σ R) = 0,
      suffices this' : ∀ (x : direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i))), 
      i ∉ dfinsupp.support x → coeff m ((x i) : mv_polynomial σ R) = 0,
      rw [finset.sum_eq_single i, finset.sum_eq_single i] at hpq, 
      exact hpq,
      exact λ b hb, this q b,
      exact this' q,
      exact λ b hb, this p b,
      exact this' p,
      { intros x hx, 
        simp only [dfinsupp.mem_support_to_fun, not_not] at hx, rw hx, 
        exact mv_polynomial.coeff_zero m, },
      { intros x b hbi,
        apply is_weighted_homogeneous.coeff_eq_zero _ m,
        rw hi,
        exact ne.symm hbi,
        rw ← mem_weighted_homogeneous_submodule,
        exact (x b).prop, } },
    rw is_weighted_homogeneous.coeff_eq_zero (p i).prop m hi,
    rw is_weighted_homogeneous.coeff_eq_zero (q i).prop m hi, },
  { -- surjectivity 
    intro φ,
    use decompose'_fun R w φ,
    conv_lhs { rw ← direct_sum.sum_support_of _ (decompose'_fun R w φ) },
    simp only [map_sum, direct_sum.coe_add_monoid_hom_of],
    simp_rw decompose'_fun_coe_apply, 

    conv_rhs { rw ← sum_weighted_homogeneous_component w φ}, 
    rw finsum_eq_sum _ (weighted_homogeneous_component_finsupp φ),
    apply congr_arg2 _ _ rfl, 
    ext m,
    rw [dfinsupp.mem_support_to_fun, ne.def, set.finite.mem_to_finset, function.mem_support, not_iff_not], 
    conv_lhs { rw [← subtype.coe_inj, decompose'_fun_coe_apply, submodule.coe_zero], } },
end


def graded_polynomial_algebra : graded_algebra 
(weighted_homogeneous_submodule R w) := graded_algebra.of_alg_hom (weighted_homogeneous_submodule R w) (decompose'a R w) (sorry) (sorry) 


end mv_polynomial

end graded_algebra