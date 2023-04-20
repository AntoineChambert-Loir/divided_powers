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
import ..weighted_homogeneous -- Modified version of PR #17855
import ..graded_ring_quot -- Quotients of graded rings

noncomputable theory

/-! 
The divided power algebra of a module -/

open finset mv_polynomial ring_quot

section ideals_and_rel

lemma mk_quotient_eq_of_rel (R : Type*) [comm_ring R] {A : Type*} [comm_ring A] [algebra R A] {r : A → A → Prop} {a b : A} (h : r a b) :
ideal.quotient.mk (ideal.of_rel r) a = ideal.quotient.mk (ideal.of_rel r) b :=
begin
  suffices : function.injective (ring_quot.ring_quot_equiv_ideal_quotient r).inv_fun,
  apply this, 
  exact mk_ring_hom_rel h,
  rw function.injective_iff_has_left_inverse, 
  use (ring_quot.ring_quot_equiv_ideal_quotient r).to_fun,
  exact (ring_quot.ring_quot_equiv_ideal_quotient r).right_inv,
end

lemma ideal.quotient_mk_eq_ring_quot_apply (R : Type*) [comm_ring R] {A : Type*} [comm_ring A] [algebra R A] (r : A → A → Prop) (a : A) :
  ideal.quotient.mk (ideal.of_rel r) a 
  = ring_quot.ring_quot_to_ideal_quotient r (mk_alg_hom R r a) :=
begin
  rw ← ring_quot.ring_quot_to_ideal_quotient_apply r a,
  rw ← ring_quot.mk_alg_hom_coe R r,
  refl,
end

end ideals_and_rel

section graded_algebra

variables {R : Type*} [comm_ring R] [decidable_eq R] 
variables {A : Type*} [comm_ring A] [algebra R A]
variables {ι : Type*} [decidable_eq ι][add_comm_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]

def galgA : graded_algebra 𝒜 := infer_instance 

def decompose : A → direct_sum ι (λ i, 𝒜 i) := (galgA 𝒜).to_decomposition.decompose' 

example : has_lift_t (𝒜 0) A := infer_instance
--{ lift := λ x, x.val }

instance : has_one ↥(𝒜 0) := ⟨⟨1, (galgA 𝒜).to_graded_monoid.one_mem⟩⟩

instance : has_mul ↥(𝒜 0) := 
{ mul := λ x y, ⟨x * y, 
  begin
    convert set_like.mul_mem_graded x.2 y.2, 
    simp only [add_zero],
  end⟩ }

lemma grade_zero_coe_mul (x y : 𝒜 0) : 
  (↑(x * y) : A) = x * y := rfl 

@[simp] lemma grade_zero_val_mul (x y : 𝒜 0) :
  (x * y).val = x.val * y.val := rfl

lemma grade_zero_coe_smul (r : R) (x : 𝒜 0) : 
  (↑(r • x) : A) = r • x := rfl 

@[simp] lemma grade_zero_coe_one: (↑(1 : 𝒜 0) : A) = 1 := rfl

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
  left_distrib  := λ x y z, 
  by ext; simp only [submodule.coe_add, grade_zero_coe_mul, left_distrib],
  right_distrib := λ x y z, 
    by ext; simp only [submodule.coe_add, grade_zero_coe_mul, right_distrib],
  mul_comm      := λ x y, by ext; simp only [grade_zero_coe_mul, mul_comm],
  ..(infer_instance : add_comm_group (𝒜 0)), }

example : semiring ↥(𝒜 0) := ring.to_semiring

example (a : R) : algebra_map R A a = a • 1 := 
algebra.algebra_map_eq_smul_one a

instance grade_zero_algebra : algebra R ↥(𝒜 0) := algebra.of_module'
(λ r x, begin rw ← subtype.coe_inj, 
simp only [grade_zero_coe_mul, grade_zero_coe_smul, grade_zero_coe_one, algebra.smul_mul_assoc, one_mul], end)
(λ r x, begin rw ← subtype.coe_inj, 
simp only [grade_zero_coe_mul, grade_zero_coe_smul, grade_zero_coe_one, algebra.mul_smul_comm, mul_one],  end)


def proj (i) : A →ₗ[R] (𝒜 i) := {
to_fun := λ a, (direct_sum.decompose 𝒜 a) i,
map_add' := λ a b, by simp only [direct_sum.decompose_add, direct_sum.add_apply],
map_smul' := λ r a, by simp only [direct_sum.decompose_smul, dfinsupp.coe_smul, pi.smul_apply, ring_hom.id_apply], }


end graded_algebra
section

variables (R : Type*) [comm_ring R] [decidable_eq R] 

variables (M : Type*) [decidable_eq M] [add_comm_group M] [module R M]

namespace divided_power_algebra

/-- The type coding the basic relations that will give rise to 
the divided power algebra. 
The class of X (n, a) will be equal to dpow n a, with a ∈ M. --/
inductive rel : mv_polynomial (ℕ × M) R → mv_polynomial (ℕ × M) R → Prop
-- force `ι` to be linear and creates the divided powers
| zero {a : M} : rel (X (0, a)) 1
| smul {r : R} {n : ℕ} {a : M} : rel (X (n, r • a)) (r^n • X (n, a))
| mul {m n : ℕ} {a : M} : rel (X (m, a) * X (n, a)) ((nat.choose (m + n) m) • X (m + n, a))
| add {n : ℕ} {a b : M} : rel (X (n, a+b)) 
  (finset.sum (range (n + 1)) (λ k, (X (k, a) * X (n - k, b))))

/-- The ideal of mv_polynomial (ℕ × M) R generated by rel -/
def relI : ideal (mv_polynomial (ℕ × M) R) := 
ideal.of_rel (rel R M)

end divided_power_algebra

/-- The divided power algebra of a module M is the quotient of the polynomial ring
by the ring relation defined by divided_power_algebra.rel -/
@[derive [inhabited, comm_ring, algebra R]]
def divided_power_algebra' := ring_quot (divided_power_algebra.rel R M)

@[derive [inhabited, comm_ring, algebra R]]
def divided_power_algebra :=
 (mv_polynomial (ℕ × M) R) ⧸ (divided_power_algebra.relI R M)

/- example : divided_power_algebra R M :=
begin
  rw divided_power_algebra,
  refine submodule.quotient.mk _,
end -/

namespace divided_power_algebra

/- Note that also we don't know yet that `divided_power_algebra R M`
has divided powers, it has a kind of universal property for morphisms to a ring with divided_powers -/

/-- The “universal” property of divided_power_algebra -/
def lift (A : Type*) [comm_ring A] [algebra R A]
  (I : ideal A) (hI : divided_powers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) : 
  divided_power_algebra R M →ₐ[R] A :=
begin
  let f : mv_polynomial (ℕ × M) R →ₐ[R] A := { commutes' := λ r, by simp only [ring_hom.to_fun_eq_coe, coe_eval₂_hom, mv_polynomial.algebra_map_eq, mv_polynomial.eval₂_C],
  .. mv_polynomial.eval₂_hom (algebra_map R A) (λ (nm : ℕ × M), hI.dpow nm.1 (φ nm.2)), },
  suffices f_eval_eq : ∀ (n : ℕ) (m : M),
     f (X (n, m)) = hI.dpow n (φ m),
  apply ideal.quotient.liftₐ _ f,  
  suffices : relI R M ≤ ring_hom.ker f, 
  intros x hx,
  rw ← ring_hom.mem_ker, 
  exact this hx,  
  dsimp only [relI, ideal.of_rel], 
  rw submodule.span_le,
  rintros x ⟨a, b, hx, hab⟩,
  rw ← eq_sub_iff_add_eq at hab, rw hab,
  simp only [set_like.mem_coe, ring_hom.mem_ker, map_sub, sub_eq_zero],
  induction hx with m r n m n p m n u v,
  { rw [f_eval_eq, hI.dpow_zero (hφ m), map_one], },
  { simp only [f_eval_eq, map_smul], 
    simp only [← algebra_map_smul A, smul_eq_mul A],
    rw hI.dpow_smul n (hφ m), 
    simp only [map_pow], },
  { simp only [map_mul, map_nsmul, f_eval_eq], 
    rw hI.dpow_mul n p (hφ m), 
    rw nsmul_eq_mul, },
  { simp only [map_sum, f_eval_eq, map_add],
    rw hI.dpow_add n (hφ u) (hφ v), 
    apply congr_arg2 _ rfl,
    ext k,
    simp only [map_mul, f_eval_eq], },
  intros n m,
  simp only [ring_hom.to_fun_eq_coe, coe_eval₂_hom, alg_hom.coe_mk, eval₂_X],
end

lemma lift_eq (A : Type*) [comm_ring A] [algebra R A]
  (I : ideal A) (hI : divided_powers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (n : ℕ) (m : M) :
  lift R M A I hI φ hφ (ideal.quotient.mkₐ R (relI R M) (X (n, m))) = hI.dpow n (φ m) :=
begin
  dsimp only [lift],
  simp only [ring_hom.to_fun_eq_coe, coe_eval₂_hom, ideal.quotient.mkₐ_eq_mk, ideal.quotient.liftₐ_apply,
    ideal.quotient.lift_mk, alg_hom.coe_to_ring_hom, alg_hom.coe_mk, eval₂_X],
end


instance : graded_algebra (weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ)) := weighted_graded_algebra _ _

lemma relI_is_homogeneous : (relI R M).is_homogeneous ((weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ))) :=
begin
  dsimp only [relI, ideal.of_rel],
  apply ideal.is_homogeneous_span,
  rintros x ⟨a, b, h, hx⟩,
  rw ← eq_sub_iff_add_eq at hx, rw hx,
  induction h with n r n m n p m n u v,
  { use 0, 
    refine submodule.sub_mem _ _ _;
    rw [mem_weighted_homogeneous_submodule], 
    apply is_weighted_homogeneous_X, 
    apply is_weighted_homogeneous_one, },
  { use n, 
    refine submodule.sub_mem _ _ _,
    rw [mem_weighted_homogeneous_submodule], 
    apply is_weighted_homogeneous_X, 
    refine submodule.smul_mem _ _ _,
    rw [mem_weighted_homogeneous_submodule], 
    apply is_weighted_homogeneous_X, },
  { use n + p, 
    refine submodule.sub_mem _ _ _,
    rw [mem_weighted_homogeneous_submodule], 
    apply is_weighted_homogeneous.mul;
    apply is_weighted_homogeneous_X, 
    refine nsmul_mem _ _,
    rw [mem_weighted_homogeneous_submodule], 
    apply is_weighted_homogeneous_X, },
  { use n,
    refine submodule.sub_mem _ _ _,
    rw [mem_weighted_homogeneous_submodule], 
    apply is_weighted_homogeneous_X, 
    
    refine submodule.sum_mem _ _,
    intros c hc,
    rw [mem_weighted_homogeneous_submodule], 
    have : n = c + (n - c)
    := (nat.add_sub_of_le (finset.mem_range_succ_iff.mp hc)).symm, 
    nth_rewrite 1 this, 
    apply is_weighted_homogeneous.mul;
    apply is_weighted_homogeneous_X, },
end

/-- The graded submodules of `divided_power_algebra R M` -/
def grade := quot_submodule R (weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ)) (divided_power_algebra.relI R M)

/- 
instance : decidable_eq (mv_polynomial (ℕ × M) R ⧸ relI R M) :=
begin
haveI : Π (a b : mv_polynomial (ℕ × M) R), decidable (ideal.quotient.ring_con (relI R M) a b ),
intros a b,
suffices : (ideal.quotient.ring_con (relI R M)) a b ↔ a - b ∈ (relI R M),
rw this,

apply quotient.decidable_eq,
end -/

-- I can't manage to prove the above instance
open_locale classical


/-- The canonical decomposition of `divided_power_algebra R M` -/
def decomposition := quot_decomposition R 
(weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ)) (divided_power_algebra.relI R M)
(relI_is_homogeneous R M)

end divided_power_algebra

/-- The graded algebra structure on the divided power algebra-/
def divided_power_galgebra : graded_algebra (divided_power_algebra.grade R M) := 
  graded_quot_alg R 
    (weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ)) 
    (divided_power_algebra.relI R M) (divided_power_algebra.relI_is_homogeneous R M)

namespace divided_power_algebra

variable {M}

example (a : mv_polynomial (ℕ × M) R) : ideal.quotient.mkₐ R (relI R M) a = ring_quot.ring_quot_to_ideal_quotient (rel R M) (mk_alg_hom R (rel R M) a) := 
begin
simp only [ideal.quotient.mkₐ_eq_mk],
dsimp only [relI],
rw ideal.quotient_mk_eq_ring_quot_apply R (rel R M),
end

/-- The canonical linear map `M →ₗ[R] divided_power_algebra R M`. -/
def ι : M →ₗ[R] (divided_power_algebra R M) :=
{ to_fun := λ m, (ideal.quotient.mkₐ R _ (X (1, m))),
  map_add' := λ x y, by { 
    rw [← map_add, ideal.quotient.mkₐ_eq_mk],
    dsimp only [relI],
    rw mk_quotient_eq_of_rel R rel.add, 
    simp only [sum_range_succ', sum_range_zero, zero_add, nat.sub_zero,
    nat.sub_self], 
    simp only [map_add, map_mul],
    simp only [mk_quotient_eq_of_rel R rel.zero],
    simp only [map_one, one_mul, mul_one], 
    apply_instance, },
  map_smul' := λ r x, by { 
    rw [← map_smul, ideal.quotient.mkₐ_eq_mk],
    dsimp only [relI],
    rw [mk_quotient_eq_of_rel R rel.smul], 
    simp only [pow_one, ring_hom.id_apply],
    apply_instance, } }

lemma mk_alg_hom_mv_polynomial_ι_eq_ι (m : M) :
  ideal.quotient.mkₐ R (relI R M) (X (1, m)) = ι R m := rfl

variable {R}
def degree (v : (ℕ × M) →₀ ℕ) : ℕ := finsum (λ x, (v x) * x.1)

def is_homogeneous_of_degree (p : mv_polynomial (ℕ × M) R) (n : ℕ) : Prop :=
∀ v ∈ p.support, degree v = n 

variables (R M)

/-- The degree-n submodule of the divided power algebra -/
def grade' (n : ℕ) : submodule R (divided_power_algebra R M) :=
submodule.span R 
  { u : divided_power_algebra R M | ∃ p : mv_polynomial (ℕ × M) R,
    (is_homogeneous_of_degree p n ∧ ideal.quotient.mkₐ R (relI R M) p = u) }

-- instance : module R (direct_sum ℕ (λ (i : ℕ), ↥(grade R M i))) := infer_instance

lemma one_mem : (1 : divided_power_algebra R M) ∈ grade R M 0 := begin
  refine ⟨1, _, rfl⟩,
  simp only [set_like.mem_coe, mem_weighted_homogeneous_submodule, is_weighted_homogeneous_one], 
end

/-
submodule.subset_span ⟨C 1, 
  ⟨λ v hv, 
  begin
    classical,
    suffices hv : v = 0,
    simp only [hv, degree, finsupp.coe_zero, pi.zero_apply, zero_mul, finsum_zero],   
    { apply symm,
      by_contradiction hv', 
      simp only [mem_support_iff, mv_polynomial.coeff_C, if_neg hv'] at hv,
      apply hv, refl,},
  end,
  by simp only [map_one]⟩⟩
-/

/-- degree of a product is sum of degrees -/
lemma mul_mem ⦃i j : ℕ⦄ {gi gj : divided_power_algebra R M} (hi : gi ∈ grade R M i)
  (hj : gj ∈ grade R M j) : gi * gj ∈ grade R M (i + j) :=
(divided_power_galgebra R M).to_graded_monoid.mul_mem hi hj

 /-
  revert gj,
  apply submodule.span_induction hi,
  { intros x hx gj hj,
    apply submodule.span_induction hj,
    { intros y hy,
      obtain ⟨p, hp, rfl⟩ := hx,
      obtain ⟨q, hq, rfl⟩ := hy,
      apply submodule.subset_span,
      use p * q, 
      split,
      intros w hw,
      let hw' := mv_polynomial.support_mul p q hw, 
      simp only [mem_bUnion] at hw', 
      obtain ⟨u, hu, v, hv, huv⟩ := hw', 
      simp only [mem_singleton] at huv, 
      rw [huv, degree, ← hp u hu, ← hq v hv, degree, degree, ← finsum_add_distrib],
      apply finsum_congr, 
      intro x, 
      simp only [finsupp.coe_add, pi.add_apply], 
      rw add_mul, 
      -- finiteness assumptions
      apply set.finite.subset u.support.finite_to_set _, 
      intro i, 
      simp only [function.mem_support, mem_coe, finsupp.mem_support_iff, ne.def],
      intros hui hi, apply hui, rw [hi, zero_mul],
      -- finiteness assumptions
      apply set.finite.subset v.support.finite_to_set _, 
      intro i, 
      simp only [function.mem_support, mem_coe, finsupp.mem_support_iff, ne.def],
      intros hvi hi, apply hvi, rw [hi, zero_mul],
      --
      simp only [map_mul], },
    { rw mul_zero, exact zero_mem _, },
    { intros y z hxy hxz,
      rw left_distrib,
      exact add_mem hxy hxz },
    { intros r y hxy,
      rw mul_smul_comm,
      exact submodule.smul_mem _ r hxy,}},
  { intros gj hj,
    rw zero_mul, exact zero_mem _, },
  { intros x y hx hy gj hj,
    rw right_distrib,
    exact add_mem (hx hj) (hy hj), },
  { intros r x hx gj hj,
    rw smul_mul_assoc,
    exact submodule.smul_mem _ _ (hx hj) },
    -/

/- The initial version 

def grade' (n : ℕ) : submodule R (divided_power_algebra R M) :=
submodule.span R 
  { u : divided_power_algebra R M | ∃ (s : multiset (ℕ × M)) 
    (hs : (s.map (λ x : ℕ × M, x.1)).sum = n),
    (s.map (λ x, mk_alg_hom R (rel R M) (X x))).prod = u }

lemma one_mem' : (1 : divided_power_algebra R M) ∈ grade' R M 0 := 
submodule.subset_span ⟨{(0, 0)}, by rw [multiset.map_singleton, multiset.sum_singleton], 
  by { rw [multiset.map_singleton, multiset.prod_singleton, 
    ← map_one (mk_alg_hom R (rel R M)), mk_alg_hom_rel R rel.zero]}⟩

lemma mul_mem' ⦃i j : ℕ⦄ {gi gj : divided_power_algebra R M} (hi : gi ∈ grade' R M i)
  (hj : gj ∈ grade' R M j) : gi * gj ∈ grade' R M (i + j) :=
begin
  revert gj,
  apply submodule.span_induction hi,
  { intros x hx gj hj,
    apply submodule.span_induction hj,
    { intros y hy,
      obtain ⟨s, hs, rfl⟩ := hx,
      obtain ⟨t, ht, rfl⟩ := hy,
      rw [← multiset.prod_add, ← multiset.map_add],
      apply submodule.subset_span,
      exact ⟨s + t, by rw [multiset.map_add, multiset.sum_add, hs, ht], rfl⟩,},
    { rw mul_zero, exact zero_mem _, },
    { intros y z hxy hxz,
      rw left_distrib,
      exact add_mem hxy hxz },
    { intros r y hxy,
      rw mul_smul_comm,
      exact submodule.smul_mem _ r hxy,}},
  { intros gj hj,
    rw zero_mul, exact zero_mem _, },
  { intros x y hx hy gj hj,
    rw right_distrib,
    exact add_mem (hx hj) (hy hj), },
  { intros r x hx gj hj,
    rw smul_mul_assoc,
    exact submodule.smul_mem _ _ (hx hj) },
end

def f :  R →+ (direct_sum ℕ (λ (i : ℕ), ↥(grade R M i))) := sorry

def decompose'' : ℕ × M → direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)) :=
λ x,  direct_sum.of (λ n, grade R M n) x.1  
  (⟨ring_quot.mk_alg_hom R (rel R M) (X x), submodule.subset_span ⟨{x},
    by rw [multiset.map_singleton, multiset.sum_singleton],
    by rw [multiset.map_singleton, multiset.prod_singleton]⟩⟩ : (grade R M x.1))

-/

/-
/-- Split the class of a polynomial into its components of various degrees -/
def decompose' : mv_polynomial (ℕ × M) R → direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)) := λ p, 
  -- p = p.support.sum (λ (v : ℕ × M →₀ ℕ), ⇑(monomial v) (coeff v p))
  p.support.sum
    (λ (v : ℕ × M →₀ ℕ), 
    direct_sum.of (λ n, grade R M n) 
    (finsum (λ x : ℕ × M, (v x) * x.1))
    (⟨ring_quot.mk_alg_hom R (rel R M) (monomial v (coeff v p)), 
      begin
        apply submodule.subset_span,
        use monomial v (coeff v p), 
        split,
        { intros v' hv', 
          suffices : v' = v, rw [degree, this], 
          rw [← finset.mem_singleton], 
          exact mv_polynomial.support_monomial_subset hv', },
        refl,
     end⟩))

  /- p.support : finset ((ℕ × M) →₀ ℕ)
    si v ∈ p.support, le monôme v est prod ("dpow n m")^(v (n, m))
    son degré est finsum (λ x, x.1 * (v x))
  -- p.coeff : ((ℕ × M) →₀ ℕ) → R
  -- p is a lift of sum (coeff v p) • prod ("dpow n m")^(v (n, m))
  -- dpow n m vit en degré n
  -- (prod ("dpow n m")^(v (n,m))) vit en degré finsum (ℕ × M) (λ x, v x * x.1)
  -/

  /-
  refine p.sum _ ,
  intros s a,
  refine direct_sum.mk (λ n, grade R M n) s.frange (λ m, _),
  obtain ⟨m, hm⟩ := m,
  simp only [mem_coe] at hm,
  rw finsupp.mem_frange at hm,
  
  --exact p.sum (λs a, f a * s.prod (λ n e, decompose'' n ^ e))
  --change add_monoid_algebra R ((ℕ × M)  →₀ ℕ) →+ direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)),
  --refine add_monoid_algebra.lift_nc  _ (decompose'' R M),
  --intro x,
  --apply direct_sum.mk,
  sorry-/

def take_degree (p : mv_polynomial (ℕ ×M) R) (n : ℕ) :
  finset (ℕ × M →₀ ℕ) := 
  p.support.filter (λ v, finsum (λ x : ℕ × M, (v x) * x.1) = n)

lemma decompose'_eq (p: mv_polynomial (ℕ × M) R) (n : ℕ) :
  (decompose' R M p n : divided_power_algebra R M) = 
  ring_quot.mk_alg_hom R (rel R M) 
  ((p.support.filter 
    (λ v : (ℕ × M) →₀ ℕ, finsum (λ x : ℕ × M, (v x) * x.1) = n )).sum 
    (λ v, monomial v (coeff v p))) := 
begin
  classical,
  unfold decompose',
  
  induction p using mv_polynomial.induction_on' with v c p q hp hq,
  { -- case of monomials
    rw finset.sum_eq_single v,
    -- basic equality
    by_cases hn : finsum (λ x : ℕ × M, (v x) * x.1) = n,
    { rw ← hn,
      rw direct_sum.of_eq_same, 
      simp only [subtype.coe_mk], 
      apply congr_arg, 
      rw finset.sum_eq_single v, 
      intros w hw hw', 
      rw finset.mem_filter at hw, 
      rw mv_polynomial.monomial_eq_zero, rw mv_polynomial.coeff_monomial w v c, 
      rw if_neg, intro h, exact hw' h.symm, 
      --
      simp only [filter_true_of_mem, mem_support_iff, coeff_monomial, ne.def, ite_eq_right_iff, not_forall, exists_prop, and_imp,
  forall_eq', eq_self_iff_true, implies_true_iff, if_true, not_not, monomial_eq_zero, imp_self], },
    { rw direct_sum.of_eq_of_ne, 
      simp only [submodule.coe_zero, coeff_monomial], 
      apply symm, convert map_zero _, 
      convert finset.sum_empty, 
      rw finset.eq_empty_iff_forall_not_mem,
      intros w hw, rw finset.mem_filter at hw,  
      apply hn,
      suffices : w = v, rw ← this, exact hw.2,
      rw ← finset.mem_singleton, 
      exact mv_polynomial.support_monomial_subset hw.1, 
      --
      exact hn,  }, 
    -- support condition 
    intros w hw hwv, 
    ext m, 
    rw direct_sum.zero_apply , 
    rw subtype.coe_inj,
    by_cases hm : m = finsum (λ x, w x * x.1),
    { rw hm,
      rw direct_sum.of_eq_same,
      simp only [coeff_monomial, submodule.mk_eq_zero],
      rw if_neg,
      simp only [map_zero],
      { intro h, exact hwv h.symm }, },
    { rw direct_sum.of_eq_of_ne,
      intro h, exact hm h.symm, },

    -- second support condition
    unfold direct_sum.of, 
    simp only [mem_support_iff, not_not, dfinsupp.single_add_hom_apply, dfinsupp.single_eq_zero],
    intro hv, simp_rw hv, 
    simp only [map_zero, submodule.mk_eq_zero], }, 
  sorry
end

lemma not_mem_monomial_support (n : ℕ) (v : ℕ × M →₀ ℕ) (c : R) :
v ∉ ((monomial v) c).support
↔ c = 0  := 
begin
  classical,
rw [mv_polynomial.not_mem_support_iff, mv_polynomial.coeff_monomial], 
simp only [eq_self_iff_true, if_true], 
end


lemma decompose_rel' (a b : mv_polynomial (ℕ × M) R) (hab : ring_quot.rel (rel R M) a b) :
  decompose' R M a = decompose' R M b :=
begin
  induction hab with a b hab a b c h ih a b c h ih a b c h ih,
  { -- rel 
    induction hab with m c n m n p m n m m', 
    { unfold decompose',
    
    
    sorry },
    { sorry },
    { sorry },
    { sorry } },
  { sorry },
  { sorry },
  { sorry },


end
-/

def decompose : divided_power_algebra R M → direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)) :=
(divided_power_galgebra R M).to_decomposition.decompose'

/- graded_algebra (grade R M )-/
instance : graded_algebra (divided_power_algebra.grade R M) := divided_power_galgebra R M

example : algebra R (grade R M 0) := infer_instance

/- NOW WRITTEN ABOVE, IN GENERAL CASE OF GRADED ALGEBRAS 
-- Why doesn't Lean find this instance?
instance : has_lift_t ↥(grade R M 0) (divided_power_algebra R M) := { lift := λ x, x.val }

instance : has_one (grade R M 0) := ⟨⟨1, one_mem R M ⟩⟩

instance : has_mul (grade R M 0) := 
{ mul := λ x y, ⟨x*y, by convert mul_mem R M x.2 y.2⟩ }

@[simp] lemma grade_zero_coe_mul (x y : grade R M 0) :
  (↑(x * y) : divided_power_algebra R M) = (↑x : divided_power_algebra R M) * ↑y := rfl

@[simp] lemma grade_zero_val_mul (x y : grade R M 0) :
  (↑(x * y) : divided_power_algebra  R M) = (↑x) * ↑y := rfl

@[simp] lemma grade_zero_coe_one: (↑(1 : grade R M 0) : divided_power_algebra R M) = 1 := rfl

instance : add_comm_monoid (grade R M 0) := infer_instance

instance : has_neg (grade R M 0) := add_subgroup_class.has_neg

instance : comm_ring (grade R M 0) := 
{ add           := (+),
  zero          := 0,
  neg           := has_neg.neg,
  one           := 1,
  mul           := (*),
  mul_assoc     := λ x y z, by ext; simp only [grade_zero_coe_mul, mul_assoc],
  one_mul       := λ x, by  ext; rw [grade_zero_coe_mul, grade_zero_coe_one, one_mul],
  mul_one       := λ x, by  ext; rw [grade_zero_coe_mul, grade_zero_coe_one, mul_one],
  left_distrib  := λ x y z, 
  by ext; simp only [submodule.coe_add, grade_zero_coe_mul, left_distrib],
  right_distrib := λ x y z, 
    by ext; simp only [submodule.coe_add, grade_zero_coe_mul, right_distrib],
  mul_comm      := λ x y, by ext; simp only [grade_zero_coe_mul, mul_comm],
  ..(infer_instance : add_comm_group (grade R M 0)), }

instance : algebra R (grade R M 0) := 
{ to_fun := λ a, ⟨algebra_map R (divided_power_algebra R M) a, begin use (algebra_map R _ a), split, sorry, refl,  end ⟩, 
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry, 
  commutes' := sorry,
  smul_def' := sorry, } 
  
  
  -/


/- We need the projections (divided_power_algebra R M) → grade R M n ,
more generally for graded algebras -/

instance : add_submonoid_class (submodule R (mv_polynomial (ℕ × M) R ⧸ relI R M)) (divided_power_algebra R M) := submodule.add_submonoid_class

def proj' (n : ℕ) : divided_power_algebra R M →ₗ[R] grade R M n := 
proj (grade R M) n

/- R → grade R M 0 is isomorphism -/
def ring_equiv_degree_zero : ring_equiv R (grade R M 0) := 
{ to_fun    := (proj' R M 0) ∘ (algebra_map R (divided_power_algebra R M)),
  inv_fun   := λ ⟨x, hx⟩, begin
dsimp only [grade, quot_submodule] at hx, 
rw submodule.mem_map at hx, 
let y := hx.some, let hy := hx.some_spec, 
rw mem_weighted_homogeneous_submodule at hy,
  sorry,end,
  left_inv  := sorry,
  right_inv := sorry,
  map_mul'  := sorry,
  map_add'  := sorry }

def proj_0_ring_hom : ring_hom (divided_power_algebra R M) R :=
{ to_fun    := (ring_equiv_degree_zero R M).inv_fun ∘ (proj' R M 0),
  map_one'  := sorry,
  map_mul'  := sorry,
  map_zero' := sorry,
  map_add'  := sorry }


/- ι : M → grade R M 1 is isomorphism -/
def linear_equiv_degree_one : linear_equiv (ring_hom.id R) M (grade R M 1) :=
{ to_fun    := (proj' R M 1) ∘ ι R,
  map_add'  := sorry,
  map_smul' := sorry,
  inv_fun   := sorry,
  left_inv  := sorry,
  right_inv := sorry }

def aug_ideal : ideal (divided_power_algebra R M) := (proj_0_ring_hom R M).ker

section

def is_aug_ideal (R : Type*) [comm_ring R] (I : ideal R) : Prop :=
∃ g : R⧸I →+* R, (ideal.quotient.mk I) ∘ g = id

/- We prove that the augmentation is an augmentation ideal, namely there is a section -/
lemma aug_ideal_is_aug_ideal : is_aug_ideal (divided_power_algebra R M) (aug_ideal R M) :=
sorry


variables (x : M) (n : ℕ)

/-- Lemma 2 of Roby 65. -/
lemma on_dp_algebra_unique (h h' : divided_powers (aug_ideal R M))
  (h1 : ∀ (x : M) (n : ℕ), h.dpow n (ι R x) = submodule.quotient.mk (X (n, x)))
  (h1' : ∀ (x : M) (n : ℕ), h'.dpow n (ι R x) = submodule.quotient.mk (X (n, x))) : 
  h = h' := sorry  

def cond_D : Prop := ∃ (h : divided_powers (aug_ideal R M)), 
  ∀ (x : M) (n : ℕ), h.dpow n (ι R x) = submodule.quotient.mk (X (n, x))

end

end divided_power_algebra

end

section roby
/- Formalization of Roby 1965, section 8 -/

.

open_locale tensor_product

variables (A R S : Type*) [comm_ring A] [comm_ring R] [algebra A R] [comm_ring S] [algebra A S] 
  {I : ideal R} {J : ideal S} (hI : divided_powers I) (hJ : divided_powers J)


def i_1 : R →ₐ R ⊗[A] S := algebra.tensor_product.include_left

def i_2 : S →ₐ R ⊗[A] S := algebra.tensor_product.include_right

variables {R S} (I J)
def K : ideal (R ⊗[A] S) := (I.map (i_1 A R S)) ⊔ (J.map (i_2 A R S))

namespace divided_powers

variables {I J}
/- Lemma 1 : uniqueness of the dp structure on R ⊗ S for I + J -/
lemma on_tensor_product_unique (hK hK' : divided_powers (K A I J))
  (hi_1 : is_pd_morphism hI hK (i_1 A R S)) (hi_1' : is_pd_morphism hI hK' (i_1 A R S))
  (hi_2 : is_pd_morphism hJ hK (i_2 A R S)) (hi_2' : is_pd_morphism hJ hK' (i_2 A R S)) : 
  hK = hK' :=
sorry

def cond_T : Prop :=
∃ hK : divided_powers (K A I J), 
  is_pd_morphism hI hK (i_1 A R S) ∧ is_pd_morphism hJ hK (i_2 A R S)

section free

def cond_T_free [hR_free : module.free A R] [hS_free : module.free A S] : Prop :=
∃ hK : divided_powers (K A I J), 
  is_pd_morphism hI hK (i_1 A R S) ∧ is_pd_morphism hJ hK (i_2 A R S)

def cond_Q (A R : Type*) [comm_ring A] [comm_ring R] [algebra A R]
  {I : ideal R} (hI : divided_powers I) : Prop := 
∃ (T : Type*) [comm_ring T], by exactI ∃ [algebra A T], by exactI ∃ [module.free A T]
  {J : ideal T} (hJ : divided_powers J) (f : pd_morphism hI hJ), 
  function.surjective f.to_ring_hom

end free


end divided_powers

end roby

section divided_power_algebra

/- 
and a divided power structure on that ideal such that
dpow R n (ι R x) = mk_alg_hom R (rel R M) (X (x, n)) 

(x,n) represents dpow n x
dpow m (x,n) should be dpow m (dpow n x) = (mchoose m n) dpow (m*n) x
An element x in divided_power_algebra R M takes the form
mk_alg_hom R (rel R M) (P)
where P is a sum of monomials  a * (m,n)   : m ∈ M, n ∈ ℕ
define
dpow k x = sum products a ^ kᵢ * dpow (mchoose kᵢ nᵢ (mᵢ,nᵢ * kᵢ)) 
where the sum is over functions → ℕ, with sum k
-/

/- Prove that it is unique… -/


/- Introduce notation ?
Here : x ^ [n] = mk_alg_hom R _ (X (x, n))
In general, x ^ [n]  for dpow n x ? 

-/

end divided_power_algebra
