/- Copyright 2022 ACL & MIdFF-/

import algebra.free_algebra
import algebra.ring_quot
import algebra.triv_sq_zero_ext
import algebra.algebra.operations
import linear_algebra.multilinear.basic

import ring_theory.graded_algebra.basic
import ring_theory.tensor_product
import data.mv_polynomial.supported

import data.rel



import ..weighted_homogeneous -- Modified version of PR #17855
import ..graded_ring_quot -- Quotients of graded rings
import ..graded_module_quot

noncomputable theory

/-! 
The divided power algebra of a module -/

open finset mv_polynomial ring_quot direct_sum ideal ideal.quotient

theorem ideal.pow_eq_bot {R : Type*} [comm_semiring R] [no_zero_divisors R] {I : ideal R} 
  {n : ℕ} (hn : n ≠ 0) :
  I ^ n = ⊥ ↔ I = ⊥ :=
begin
  induction n with n ih,
  { exfalso, exact hn (eq.refl _) },
  { by_cases hn0 : n = 0,
    { rw [hn0, pow_one] },
    { rw [pow_succ, mul_eq_bot, ih hn0, or_self] }}
end

namespace mv_polynomial

variables {R S σ : Type*} [comm_semiring R] [comm_semiring S] 

@[simp] lemma eval₂_hom.smul (f : R →+* S) (g : σ → S) (r : R) (P : mv_polynomial σ R) :
  eval₂_hom f g (r • P) = f r • eval₂_hom f g P := 
by simp only [smul_eq_C_mul, coe_eval₂_hom, eval₂_mul, eval₂_C, algebra.id.smul_eq_mul]

variables [algebra R S]

variable (R)
/-- `mv_polynomial.eval₂ (algebra_map R S) g` as an `R`-algebra homomorphism. -/
def eval₂_alg_hom  (g : σ → S) :
  mv_polynomial σ R →ₐ[R] S := 
{ commutes' := λ r, by rw [ring_hom.to_fun_eq_coe, coe_eval₂_hom, algebra_map_eq, eval₂_C], 
  .. eval₂_hom (algebra_map R S) g }

variable {R}
lemma eval₂_alg_hom_apply (g : σ → S) (P : mv_polynomial σ R) :
  eval₂_alg_hom R g P = eval₂_hom (algebra_map R S) g P := rfl

@[simp] lemma coe_eval₂_alg_hom (g : σ → S) :
  ⇑(eval₂_alg_hom R g) = eval₂ (algebra_map R S) g := rfl

@[simp] lemma eval₂_alg_hom_X' (g : σ → S) (i : σ) :
  eval₂_alg_hom R g ((X i : mv_polynomial σ R)) = g i := 
eval₂_X (algebra_map R S)  g i

end mv_polynomial

section ideals_and_rel

lemma quotient_mk_eq_of_rel {A : Type*} [comm_ring A] {r : A → A → Prop} {a b : A} (h : r a b) :
  mk (of_rel r) a = mk (of_rel r) b :=
begin
  suffices hinj : function.injective (ring_quot.ring_quot_equiv_ideal_quotient r).inv_fun,
  { apply hinj, exact mk_ring_hom_rel h },
  exact function.injective_iff_has_left_inverse.mpr ⟨(ring_quot_equiv_ideal_quotient r).to_fun,
    (ring_quot_equiv_ideal_quotient r).right_inv⟩,
end

namespace ideal

lemma quotient_mk_eq_ring_quot_apply (R : Type*) [comm_ring R] {A : Type*} [comm_ring A]
  [algebra R A] (r : A → A → Prop) (a : A) :
  mk (of_rel r) a = ring_quot_to_ideal_quotient r (mk_alg_hom R r a) :=
by rw [← ring_quot_to_ideal_quotient_apply r a, ← mk_alg_hom_coe R r];  refl

namespace quotient 

variables {R S : Type*} [comm_ring R] [comm_ring S]

lemma rel_le_ker (I : ideal R) {r : R → R → Prop} (hr : I = of_rel r) (f : R →+* S) 
  (hf : ∀ {a b : R}, r a b → f a = f b) : I ≤ f.ker :=
begin
  rw [hr, of_rel, submodule.span_le],
  rintros x ⟨a, b, hx, hab⟩,
  rw [eq_sub_iff_add_eq.mpr hab, set_like.mem_coe, ring_hom.mem_ker, map_sub, sub_eq_zero, hf hx]
end

/-- Given a binary relation `r` on `R` and a ring homomorphism `f : R →+* S` that is constant on
  each equivalent class of `r`, lift `f` to the quotient by the ideal generated by `r`. -/
def lift_rel  (I : ideal R) {r : R → R → Prop} (hr : I = of_rel r) (f : R →+* S)
  (hf : ∀ (a b : R), r a b → f a = f b) : R ⧸ I →+* S :=
lift I f (rel_le_ker I hr f hf)

end quotient

end ideal

end ideals_and_rel

namespace triv_sq_zero_ext

variables (R M : Type*) [comm_semiring R] [add_comm_monoid M] [module R M] [module Rᵐᵒᵖ M]
  [is_central_scalar R M]

def ker_ideal : ideal (triv_sq_zero_ext R M) := ring_hom.ker (fst_hom R R M)

lemma mem_ker_ideal_iff_inr (x : triv_sq_zero_ext R M) :
  (x ∈ ker_ideal R M ↔ x = inr x.snd) :=
begin
  obtain ⟨r, m⟩ := x,
  simp only [ker_ideal, ring_hom.mem_ker, fst_hom_apply, fst_mk],
  exact ⟨λ hr, by {rw hr, refl}, λ hrm, by rw [← fst_mk r m, hrm, fst_inr]⟩,
end

lemma mem_ker_ideal_iff_exists (x : triv_sq_zero_ext R M) :
  (x ∈ ker_ideal R M ↔ ∃ (m : M), x = inr m) :=
by rw mem_ker_ideal_iff_inr; exact ⟨λ h, ⟨x.snd, h⟩, λ ⟨m, hm⟩, by {rw hm, refl}⟩


lemma square_zero : (ker_ideal R M) ^ 2 = 0 := 
begin
  simp only [pow_two, zero_eq_bot, eq_bot_iff, mul_le, mem_ker_ideal_iff_inr],
  rintros x hx y hy, 
  rw [hx, hy, mem_bot, inr_mul_inr],
end

end triv_sq_zero_ext

open ideal ideal.quotient triv_sq_zero_ext

section graded_algebra

variables {R : Type*} [comm_ring R]
variables {A : Type*} [comm_ring A] [algebra R A]
variables {ι : Type*} [canonically_ordered_add_monoid ι]
variables (𝒜 : ι → submodule R A)

lemma grade_zero_coe_smul (r : R) (x : 𝒜 0) : (↑(r • x) : A) = r • x := rfl 

variables  [decidable_eq ι] [graded_algebra 𝒜]
instance : has_one ↥(𝒜 0) := 
⟨⟨1, (@graded_ring.to_graded_monoid ι A (submodule R A) _ _ _ _ _ 𝒜 _).one_mem⟩⟩

instance : has_mul ↥(𝒜 0) := 
⟨λ x y, ⟨x * y, by convert set_like.mul_mem_graded x.2 y.2; rw [add_zero]⟩⟩

@[simp] lemma grade_zero_coe_mul (x y : 𝒜 0) : (↑(x * y) : A) = x * y := rfl 

@[simp] lemma grade_zero_val_mul (x y : 𝒜 0) : (x * y).val = x.val * y.val := rfl

@[simp] lemma grade_zero_coe_one : (↑(1 : 𝒜 0) : A) = 1 := rfl

lemma one_mem : (1 : A) ∈ 𝒜 0 := set_like.one_mem_graded 𝒜

example : add_comm_monoid (𝒜 0) := infer_instance

example : has_neg (𝒜 0) := add_subgroup_class.has_neg

instance grade_zero_comm_ring : comm_ring ↥(𝒜 0) := { 
  add           := (+),
  zero          := 0,
  neg           := has_neg.neg,
  one           := 1,
  mul           := (*),
  mul_assoc     := λ x y z, by ext; simp only [grade_zero_coe_mul, mul_assoc],
  one_mul       := λ x, by  ext; rw [grade_zero_coe_mul, grade_zero_coe_one, one_mul],
  mul_one       := λ x, by  ext; rw [grade_zero_coe_mul, grade_zero_coe_one, mul_one],
  left_distrib  := λ x y z, by ext; simp only [submodule.coe_add, grade_zero_coe_mul, left_distrib],
  right_distrib := λ x y z, 
    by ext; simp only [submodule.coe_add, grade_zero_coe_mul, right_distrib],
  mul_comm      := λ x y, by ext; simp only [grade_zero_coe_mul, mul_comm],
  ..(infer_instance : add_comm_group (𝒜 0)) }

instance grade_zero_algebra : algebra R ↥(𝒜 0) := algebra.of_module'
  (λ r x, by ext; simp only [grade_zero_coe_mul, grade_zero_coe_smul, grade_zero_coe_one, 
    algebra.smul_mul_assoc, one_mul])
  (λ r x, by ext; simp only [grade_zero_coe_mul, grade_zero_coe_smul, grade_zero_coe_one, 
    algebra.mul_smul_comm, mul_one])

/-- The projection from `A` to the degree `i` component `𝒜 i`, as an `R`-linear map. -/
def proj (i : ι) : A →ₗ[R] (𝒜 i) :=
{ to_fun    := λ a, decompose 𝒜 a i,
  map_add'  := λ a b, by rw [decompose_add, add_apply],
  map_smul' := λ r a, by rw [decompose_smul, dfinsupp.coe_smul, pi.smul_apply, ring_hom.id_apply] }

@[simps] def proj_zero_ring_hom' : A →+* (𝒜 0) :=
{ to_fun := λ a, proj 𝒜 0 a,
  map_one' := begin 
    ext,
    simp only [proj, linear_map.coe_mk, decompose_of_mem_same 𝒜 (one_mem 𝒜),
    grade_zero_coe_one], 
  end,
  map_zero' := by { simp only [proj, decompose_zero, linear_map.coe_mk, zero_apply] },
  map_add' := λ _ _, by { simp only [proj, decompose_add, linear_map.coe_mk, add_apply] },
  map_mul' := λ x y, begin
    ext,
    simp only [proj, linear_map.coe_mk, set_like.coe_eq_coe, grade_zero_coe_mul, 
      ← graded_ring.proj_zero_ring_hom_apply 𝒜, ← _root_.map_mul],
  end }


end graded_algebra

section graded_algebra

variables {R : Type*} [comm_ring R]

def galg_hom.is_homogeneous {ι : Type*} {A : Type*} [comm_ring A] [algebra R A] 
  (𝒜 : ι → submodule R A) {B : Type*} [comm_ring B] [algebra R B] (ℬ : ι → submodule R B)
  (f : A →ₐ[R] B) := 
∀ i a, a ∈ 𝒜 i → f a ∈ ℬ i

lemma finsupp.prod.mem_grade {κ A : Type*} [add_comm_monoid κ] [decidable_eq κ] [comm_ring A] 
  [algebra R A] (𝒜 : κ → submodule R A) [graded_algebra 𝒜] {σ : Type*} (c : σ →₀ ℕ) (f : σ → A) 
  (d : σ → κ ) (hc : ∀ s ∈ c.support, f s ∈ 𝒜 (d s)) : 
  c.prod (λ s e, (f s) ^ e) ∈ 𝒜 (c.sum (λ s e, e • d s)) := 
begin
  classical,
  rw [finsupp.prod, finsupp.sum],
  let p : finset σ → Prop := 
  λ s, s ⊆ c.support → (s.prod (λ i, (f i) ^ c i) ∈ 𝒜 (s.sum (λ i, c i • d i))),
  apply @finset.induction_on σ p _ c.support,
  { exact imp_intro (set_like.one_mem_graded 𝒜) },
  { intros a s ha hs,
    by_cases hs' : (insert a s) ⊆ c.support,  
    { apply imp_intro,
      rw [finset.prod_insert ha, finset.sum_insert ha],
      exact set_like.mul_mem_graded (set_like.pow_mem_graded _ (hc a (hs' (mem_insert_self a s))))
       (hs (subset_trans (subset_insert a s) hs')) },
    { exact not.elim hs' }},
  { exact subset_rfl },
end

def galg_hom.is_homogeneous' {ι κ : Type*} /- [add_comm_monoid ι] [decidable_eq ι] -/
  (A : Type*) [comm_ring A] [algebra R A] (𝒜 : ι → submodule R A) /- [graded_algebra 𝒜] -/
  (B : Type*) [comm_ring B] [algebra R B] (ℬ : κ → submodule R B) /- [graded_algebra ℬ]  -/
  (φ : ι → κ) (f : A →ₐ[R] B) := 
∀ i a, a ∈ 𝒜 i → f a ∈ ℬ (φ i)

lemma foo (σ : Type*) {ι κ : Type*} [add_comm_monoid ι] --[decidable_eq ι]
  [add_comm_monoid κ] [decidable_eq κ]
  (A : Type*) [comm_ring A] [algebra R A] (𝒜 : κ → submodule R A) 
  [graded_algebra 𝒜] (w : σ → ι) (φ : ι →+ κ) (f : σ → A) 
  (h : ∀ s : σ, f s ∈ 𝒜 (φ (w s))) : 
  galg_hom.is_homogeneous' _ (weighted_homogeneous_submodule R w ) _ 𝒜 φ
    (mv_polynomial.aeval f) :=
begin
  intros i p hp,
  simp only [mem_weighted_homogeneous_submodule, is_weighted_homogeneous] at hp,
  rw p.as_sum,
  rw map_sum,
  apply submodule.sum_mem,
  intros c hc,
  rw aeval_monomial,
  rw ← smul_eq_mul, 
  rw algebra_map_smul,
  apply submodule.smul_mem, 
  convert finsupp.prod.mem_grade 𝒜 c f _ (λ s _, h s ),
  rw ← hp (mem_support_iff.mp hc),
  simp only [weighted_degree'],
  rw finsupp.total,
  simp only [finsupp.coe_lsum, finsupp.sum],
  rw map_sum,
  simp only [linear_map.coe_smul_right, linear_map.id_coe, id.def, algebra.id.smul_eq_mul],
  apply congr_arg2 _ rfl,
  ext s,
  rw add_monoid_hom.map_nsmul,
end

end graded_algebra

lemma mv_polynomial.vars_X_subset {R : Type*} {σ : Type*} (n : σ) [comm_semiring R] :
  (X n : mv_polynomial σ R).vars ⊆ {n} := 
begin
  classical,
  intro u,
  rw [X, mem_vars, mem_singleton], 
  rintro ⟨c, hc, hc'⟩,
  by_contradiction h', 
  rw [mem_support_iff, coeff_monomial, ne.def] at hc, 
  by_cases h : finsupp.single n 1 = c,
  { rw [← h, finsupp.mem_support_iff, ne.def, finsupp.single_apply] at hc',
    apply hc', rw if_neg (ne.symm h'), },
  { apply hc, rw if_neg h, },
end

section

open mv_polynomial 

variables {R M : Type*} [comm_ring R]

instance :
  graded_algebra (weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ)) := 
weighted_graded_algebra _ _

variable {R}
def degree (v : (ℕ × M) →₀ ℕ) : ℕ := finsum (λ x, (v x) * x.1)

def is_homogeneous_of_degree (p : mv_polynomial (ℕ × M) R) (n : ℕ) : Prop :=
∀ v ∈ p.support, degree v = n

variable (R)

lemma variable_mem_supported (nm : ℕ × M) (hn : 0 < nm.1) :
  X nm ∈ supported R {nm : ℕ × M | 0 < nm.1} :=
begin
  rw mem_supported,
  refine set.subset.trans (finset.coe_subset.mpr (vars_X_subset nm)) _,
  rw [coe_singleton, set.singleton_subset_iff, set.mem_set_of_eq],
  exact hn,
end

def to_supported : mv_polynomial (ℕ × M) R →ₐ[R] supported R {nm : ℕ × M | 0 < nm.1} :=  
aeval (λ (nm : ℕ × M), dite (0 < nm.1) (λ h, ⟨(X nm), (variable_mem_supported R nm h)⟩) (λ h, 1))

lemma to_supported_is_homogeneous : 
  galg_hom.is_homogeneous' (mv_polynomial (ℕ × M) R)
    (weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ)) (mv_polynomial (ℕ × M) R)
    (weighted_homogeneous_submodule R prod.fst) (id : ℕ → ℕ)
    ((subalgebra.val _).comp (to_supported R)) :=
begin
  classical,
  have h := @foo R _ (ℕ × M) ℕ ℕ _ _ _ (mv_polynomial (ℕ × M) R) _ _
  (weighted_homogeneous_submodule R prod.fst) _ prod.fst (add_monoid_hom.id ℕ)
  ((subalgebra.val _).to_fun.comp (λ (nm : ℕ × M), 
    dite (0 < nm.1) (λ h, ⟨(X nm), (variable_mem_supported R nm h)⟩) (λ h, 1))) _,
  have heq : (aeval ((supported R {nm : ℕ × M | 0 < nm.fst}).val.to_fun ∘ 
    λ (nm : ℕ × M), dite (0 < nm.fst) (λ (h : 0 < nm.fst), ⟨X nm, _⟩) (λ (h : ¬0 < nm.fst), 1))) =
    ((supported R {nm : ℕ × M | 0 < nm.fst}).val.comp (to_supported R)),
  { apply mv_polynomial.alg_hom_ext,
    intros nm,
    simp only [to_supported, alg_hom.to_fun_eq_coe, function.comp_app, alg_hom.coe_comp, aeval_X] },
  rw heq at h,
  exact h,
  { intros nm,
    simp only [mem_weighted_homogeneous_submodule, alg_hom.to_fun_eq_coe, subalgebra.coe_val, 
      function.comp_app, add_monoid_hom.id_apply],
    split_ifs,
    { exact is_weighted_homogeneous_X R _ _, },
    { simp only [not_lt, le_zero_iff] at h,
      rw [h, algebra_map.coe_one],
      exact is_weighted_homogeneous_one R _, }}
end

variable (M)
-- TODO: generalize
lemma eq_finsupp_single_of_degree_one {d : ℕ × M →₀ ℕ} (hd : (weighted_degree' prod.fst) d = 1)
  (hsupp : ∀ (nm : ℕ × M), nm ∈ d.support → 0 < nm.fst) :
  ∃ (m : M), finsupp.single (1, m) 1 = d :=
begin
  classical,
  rw [weighted_degree', finsupp.total_apply, finsupp.sum] at hd,
  have hnm : ∃ (nm : ℕ × M), d nm • nm.fst = 1,
  { by_contra h0,
    rw [not_exists] at h0,
    have hd0 : d.support.sum (λ (a : ℕ × M), d a • a.fst) = 0,
    { rw finset.sum_eq_zero,
      intros nm hnm,
      rw ← nat.lt_one_iff,
      apply lt_of_le_of_ne _ (h0 nm),
      rw ← hd,
      exact finset.single_le_sum (λab hab,  zero_le _ ) hnm },
    rw [hd0] at hd,
    exact zero_ne_one hd, },
  obtain ⟨nm, hnm⟩ := hnm,
  rw ← hnm at hd,
  rw [algebra.id.smul_eq_mul, nat.mul_eq_one_iff] at hnm,
  use nm.snd,
  ext ab,
  rw finsupp.single_apply,
  split_ifs with hab;
  rw [← hnm.2, eq_comm, prod.mk.eta] at hab,
  { rw [hab, hnm.1], },
  { rw eq_comm,
    by_contra hab',
    have hne0 : d ab * ab.fst ≠ 0,
    { exact mul_ne_zero hab' (ne_of_gt (hsupp ab (finsupp.mem_support_iff.mpr hab'))) },
    have hnm_mem : nm ∈ d.support,
    { rw [finsupp.mem_support_iff, hnm.1], exact one_ne_zero },
    simp only [finset.sum_eq_sum_diff_singleton_add hnm_mem, add_left_eq_self, 
      algebra.id.smul_eq_mul, sum_eq_zero_iff, mem_sdiff, finsupp.mem_support_iff, --ne.def, 
      mem_singleton] at hd,
    exact hne0 (hd ab ⟨hab', hab⟩) },
end

#where

end 