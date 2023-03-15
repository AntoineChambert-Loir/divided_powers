/- Copyright 2022 ACL & MIdFF-/

import algebra.direct_sum.basic
import ring_theory.graded_algebra.basic
import algebra.direct_sum.decomposition

import algebra.module.graded_module

import ..weighted_homogeneous

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

/- -- Original version

section direct_sum
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

def decompose_fun_of (hM : direct_sum.is_internal M) : 
  A → direct_sum ι (λ (i : ι), ↥(M i)) := (function.bijective_iff_has_inverse.mp hM).some

lemma decompose_fun_of_apply_iff (hM : direct_sum.is_internal M) (a : A) (b : direct_sum ι (λ (i : ι), ↥(M i))) : decompose_fun_of hM a = b ↔
  a = direct_sum.coe_add_monoid_hom M b := 
begin
  have hMl : function.left_inverse (decompose_fun_of hM) ⇑(direct_sum.coe_add_monoid_hom M) := (function.bijective_iff_has_inverse.mp hM).some_spec.1,
  have hMr : function.right_inverse (decompose_fun_of hM) ⇑(direct_sum.coe_add_monoid_hom M) := (function.bijective_iff_has_inverse.mp hM).some_spec.2,
  split,
  { intro hab, rw [← hab, hMr a], },
  { intro hab, rw [hab, hMl b], }
end

def decompose_of (hM : direct_sum.is_internal M) : 
  A →ₐ[R] direct_sum ι (λ (i : ι), ↥(M i)) := {
to_fun    := decompose_fun_of hM, 
map_one'  := 
begin
  rw decompose_fun_of_apply_iff, 
  have : (direct_sum.of (λ (i : ι), ↥(M i)) 0) 1 = 1 := rfl,
  simp only [← this,  direct_sum.coe_add_monoid_hom_of], 
  refl,
end,
map_mul'  := λ a b, 
begin
  classical,
  rw direct_sum.mul_eq_sum_support_ghas_mul,
  rw decompose_fun_of_apply_iff, 
  conv_lhs { rw (decompose_fun_of_apply_iff hM a _).mp rfl,
    rw (decompose_fun_of_apply_iff hM b _).mp rfl,
  rw ← direct_sum.sum_support_of (λ i, ↥(M i)) (decompose_fun_of hM a),  
  rw ← direct_sum.sum_support_of (λ i, ↥(M i)) (decompose_fun_of hM b), },
  rw map_sum, rw map_sum, 
  rw finset.sum_mul_sum, 
  rw map_sum,
  apply congr_arg2, 
  refl,
  ext ⟨i,j⟩,
  simp only [direct_sum.coe_add_monoid_hom_of, set_like.coe_ghas_mul],
end,
map_zero' := by rw [decompose_fun_of_apply_iff, map_zero],
map_add'  := λ a b,
begin
  rw [decompose_fun_of_apply_iff, map_add],
  apply congr_arg2 (+),
  rw ← decompose_fun_of_apply_iff, rw ← decompose_fun_of_apply_iff,   
end,
commutes' := λ r, 
begin
  rw [decompose_fun_of_apply_iff, direct_sum.algebra_map_apply],
  simp only [direct_sum.coe_add_monoid_hom_of, submodule.set_like.coe_galgebra_to_fun],
end }

def graded_algebra_of (hM : direct_sum.is_internal M): graded_algebra M := 
graded_algebra.of_alg_hom M (decompose_of hM) (
  begin
    ext a, 
    simp only [alg_hom.coe_comp, function.comp_app, alg_hom.coe_id, id.def],
    apply symm,
    suffices : a = (direct_sum.coe_add_monoid_hom M) ((decompose_fun_of hM) a),
    exact this, 
    rw ← (decompose_fun_of_apply_iff hM _ _),
  end) (
  begin
    intros i x, 
    suffices : (decompose_fun_of hM) ↑x = _,
    exact this,
    rw decompose_fun_of_apply_iff hM, 
    rw direct_sum.coe_add_monoid_hom_of , 
  end)

 -/



end direct_sum


section weighted_homogeneous

/- Here, given a weight `w : σ → M`, where `M` is an additive and commutative monoid, we endow the ring of multivariate polynomials `mv_polynomial σ R` with the structure of a graded algebra -/

-- This does not work yet, but there are proofs below that (should) do the job, one just needs to put them in correct order

variables {R : Type*} [comm_semiring R] 
variables {M : Type*} [add_comm_monoid M] [decidable_eq M]
variables {σ : Type*}
variable (w : σ → M)

namespace mv_polynomial

lemma weighted_homogeneous_component_mem (w : σ → M) (φ : mv_polynomial σ R) 
  (m : M) :
  weighted_homogeneous_component w m φ ∈ weighted_homogeneous_submodule R w m :=
begin
  rw mem_weighted_homogeneous_submodule, 
  exact weighted_homogeneous_component_is_weighted_homogeneous m φ, 
end

lemma decompose'_aux (φ : mv_polynomial σ R) (i : M) : 
  ite (i ∈ finset.image (weighted_degree' w) φ.support) 
    ((weighted_homogeneous_component w i) φ) 0 
    = (weighted_homogeneous_component w i) φ :=
begin
  split_ifs with hi hi, 
  refl,
  apply symm,
  apply weighted_homogeneous_component_eq_zero', 
  simp only [finset.mem_image, mem_support_iff, ne.def, exists_prop, not_exists, not_and] at hi, 
  intros m hm, 
  apply hi m, 
  rw mem_support_iff at hm, 
  exact hm, 
end

section
universes v w 
lemma direct_sum.mk_dif_pos {ι : Type v} [dec_ι : decidable_eq ι] (β : ι → Type w)
  [Π (i : ι), add_comm_monoid (β i)] {s : finset ι} (f : Π (i : (↑s : set ι)), β i.val)
  {n : ι} (hn : n ∈ s):
  direct_sum.mk β s f n = f ⟨n, hn⟩ := 
by simp only [direct_sum.mk, add_monoid_hom.coe_mk, dfinsupp.mk_apply, dif_pos hn]

lemma direct_sum.mk_dif_neg {ι : Type v} [dec_ι : decidable_eq ι] (β : ι → Type w)
  [Π (i : ι), add_comm_monoid (β i)] {s : finset ι} (f : Π (i : (↑s : set ι)), β i.val)
  {n : ι} (hn : n ∉ s):
  direct_sum.mk β s f n = 0 := 
by simp only [direct_sum.mk, add_monoid_hom.coe_mk, dfinsupp.mk_apply, dif_neg hn]

theorem linear_map.map_finsum {α R S M N : Type*} [semiring R] [semiring S] (σ : R →+* S)
  [add_comm_monoid M] [add_comm_monoid N]  [module R M] [module S N] {f : α → M} (g : M →ₛₗ[σ] N)
  (hf : (function.support f).finite) :
  g (finsum (λ (i : α), f i)) = finsum (λ (i : α), g (f i)) := 
begin
  rw ← linear_map.to_add_monoid_hom_coe,
  exact add_monoid_hom.map_finsum _ hf,
end

end

variable (R)
def decompose'_fun := λ (φ : mv_polynomial σ R), direct_sum.mk 
  (λ (i : M), ↥(weighted_homogeneous_submodule R w i))
  (finset.image (weighted_degree' w) φ.support)
  (λ m, ⟨weighted_homogeneous_component w m φ, weighted_homogeneous_component_mem w φ m⟩)

lemma direct_sum.support_subset
  (x : direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i))) [h_dec : Π (i : M) 
    (x : (λ (i : M), ↥(weighted_homogeneous_submodule R w i)) i), decidable (x ≠ 0)] :
  function.support  (λ (i : M), (x i : mv_polynomial σ R)) ⊆ ↑(dfinsupp.support x) := 
begin
  intros m hm,
  rw [function.mem_support, ne.def, submodule.coe_eq_zero] at hm,
  rw [finset.mem_coe, dfinsupp.mem_support_to_fun, ne.def],
  exact hm, 
end

lemma direct_sum.finite_support
  (x : direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i))) :
  (function.support (λ (i : M), (x i : mv_polynomial σ R))).finite := 
begin
  classical,
  exact set.finite.subset (dfinsupp.support x : set M).to_finite (direct_sum.support_subset R w x),
end

-- Should we use dfinsupp.sum instead of finsum in our weighted_homogeneous file?
lemma direct_sum.coe_add_monoid_hom_eq_finsum
  (x : direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i))) : 
  ((direct_sum.coe_add_monoid_hom (λ (i : M), weighted_homogeneous_submodule R w i)) x) = 
  finsum (λ m, x m) :=
begin
  classical,
  rw [direct_sum.coe_add_monoid_hom, direct_sum.to_add_monoid, dfinsupp.lift_add_hom_apply,
    dfinsupp.sum_add_hom_apply],
  simp_rw [add_submonoid_class.coe_subtype],
  rw [dfinsupp.sum, finsum_eq_sum_of_support_subset _ (direct_sum.support_subset R w x)],
end

-- TODO: move to weighted_homogeneous file
-- I think that we need to make R explicit in weighted_homogeneous_component
lemma weighted_homogeneous_component_weighted_homogeneous_polynomial' (m : M)
  (x : weighted_homogeneous_submodule R w m) :
  (@weighted_homogeneous_component  R M _ _ _ w m) ↑x = x :=
by rw [weighted_homogeneous_component_weighted_homogeneous_polynomial m m _ x.prop, if_pos rfl]
 
lemma weighted_homogeneous_component_direct_sum
  (x : direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i))) (m : M) : 
  (weighted_homogeneous_component w m) 
    ((direct_sum.coe_add_monoid_hom (λ (i : M), weighted_homogeneous_submodule R w i)) x) = x m :=
begin
  rw [direct_sum.coe_add_monoid_hom_eq_finsum,
    linear_map.map_finsum _ _ (direct_sum.finite_support R w x), 
    ← weighted_homogeneous_component_weighted_homogeneous_polynomial'],
  apply finsum_eq_single,
  intros n hn,
  rw [weighted_homogeneous_component_weighted_homogeneous_polynomial m n _ (x n).prop, if_neg],
  exact hn.symm,  -- Weird that I can't combine it with the previous line
end

def mv_polynomial_weighted_decomposition : 
  direct_sum.decomposition (weighted_homogeneous_submodule R w) := 
{ decompose'  := decompose'_fun R w,
  left_inv    := λ φ,
  begin
    classical,
    conv_rhs { rw [← sum_weighted_homogeneous_component w φ, 
      finsum_eq_sum _ (weighted_homogeneous_component_finsupp φ)], },
    rw ← direct_sum.sum_support_of (λ m, ↥(weighted_homogeneous_submodule R w m))
      (decompose'_fun R w φ),
    simp only [direct_sum.coe_add_monoid_hom_of, mv_polynomial.coeff_sum, map_sum],
    apply congr_arg2,
    { ext m,
      simp only [dfinsupp.mem_support_to_fun, ne.def, set.finite.mem_to_finset,
        function.mem_support, not_iff_not],
      conv_lhs { rw ← subtype.coe_inj },
      simp only [decompose'_fun, direct_sum.mk, subtype.coe_mk, add_monoid_hom.coe_mk,
        dfinsupp.mk_apply, apply_dite coe, dite_eq_ite, submodule.coe_zero],
      simp only [decompose'_aux w φ m], },
    { apply funext, intro m,
      simp only [decompose'_fun],
      simp only [direct_sum.mk, subtype.coe_mk, add_monoid_hom.coe_mk, dfinsupp.mk_apply, 
        apply_dite coe, dite_eq_ite, submodule.coe_zero],
      exact decompose'_aux w φ m, },
  end,
  right_inv   := 
  begin
    intro x, 
    set φ := (direct_sum.coe_add_monoid_hom _ x) with hφ_def,
    rw ← hφ_def,
    simp only [decompose'_fun],
    ext m d,
    apply congr_arg,
    rw [set_like.coe_eq_coe],
    by_cases hm : m ∈ finset.image ⇑(weighted_degree' w) φ.support,
    { rw direct_sum.mk_dif_pos _ _ hm,
      simp only [subtype.coe_mk, hφ_def],
      ext,      
      apply congr_arg,
      exact weighted_homogeneous_component_direct_sum _ _ _ _,
    },
    { rw direct_sum.mk_dif_neg _ _ hm,
      simp only [finset.mem_image, mem_support_iff, ne.def, exists_prop, not_exists,
        not_and', not_not] at hm,
      rw [← subtype.coe_inj, submodule.coe_zero, eq_comm, mv_polynomial.eq_zero_iff],
      intros d',
      by_cases hd' : (weighted_degree' w) d' = m,
      { convert hm d' hd' using 1,
        rw [hφ_def, direct_sum.coe_add_monoid_hom, direct_sum.to_add_monoid,
          dfinsupp.lift_add_hom_apply,dfinsupp.sum_add_hom_apply, dfinsupp.sum],
          -- It seems to me that there are some missing rw lemmas for direct_sum
        simp only [add_submonoid_class.coe_subtype],
        have hm' : m ∉ dfinsupp.support x → coeff d' (x m : mv_polynomial σ R) = 0,
        { intros h,
          simp only [dfinsupp.mem_support_to_fun, not_not] at h,
          rw h,
          simp only [submodule.coe_zero, coeff_zero] },
        rw [coeff_sum, finset.sum_eq_single _ _ hm'],
        intros n hn hmn,
        rw [← weighted_homogeneous_component_weighted_homogeneous_polynomial',
           coeff_weighted_homogeneous_component, if_neg],
        rw hd', --weird
        exact hmn.symm },
      { rw [← weighted_homogeneous_component_weighted_homogeneous_polynomial',
          coeff_weighted_homogeneous_component, if_neg],
        exact hd',  /- Same comment as above -/}}, 
  end }

#exit

end mv_polynomial

end weighted_homogeneous


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