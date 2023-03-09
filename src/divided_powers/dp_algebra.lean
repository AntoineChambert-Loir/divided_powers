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
import ..weighted_homogeneous

noncomputable theory

/-! 
The divided power algebra of a module -/

open finset mv_polynomial ring_quot

variables (R : Type*) [comm_ring R]
variables (M : Type*) [add_comm_group M] [module R M]

namespace divided_power_algebra

/-- The type coding the basic relations that will give rise to 
the divided power algebra. 
The class of X (n, a) will be equal to dpow n a, with a ∈ M. --/
inductive rel : mv_polynomial (ℕ × M) R → mv_polynomial (ℕ × M) R → Prop
-- force `ι` to be linear and creates the divided powers
| zero {a : M} : rel (X (0, a)) 1
| smul {r : R} {n : ℕ} {a : M} : rel (X (n, r • a)) (r^n • X (n, a))
| mul {m n : ℕ} {a : M} : rel (X (m, a) * X (n, a)) ((nat.choose (m + n) n) • X (m + n, a))
| add {n : ℕ} {a b : M} : rel (X (n, a+b)) 
  (finset.sum (range (n + 1)) (λ k, (X (k, a) * X (n - k, b))))

end divided_power_algebra

/-- The divided power algebra of a module M is the quotient of the polynomial ring
by the ring relation defined by divided_power_algebra.rel -/
@[derive [inhabited, comm_ring, algebra R]]
def divided_power_algebra := ring_quot (divided_power_algebra.rel R M)

namespace divided_power_algebra

variable {M}

/-- The canonical linear map `M →ₗ[R] divided_power_algebra R M`. -/
def ι : M →ₗ[R] (divided_power_algebra R M) :=
{ to_fun := λ m, (mk_alg_hom R _ (X (1, m))),
  map_add' := λ x y, by { 
    rw [← map_add, mk_alg_hom_rel R rel.add],
    simp only [sum_range_succ', sum_range_zero, zero_add, nat.sub_zero,
    nat.sub_self], 
    simp only [map_add, map_mul],
    simp only [mk_alg_hom_rel R rel.zero],
    simp only [map_one, one_mul, mul_one], },
  map_smul' := λ r x, by { 
    rw [← map_smul, mk_alg_hom_rel R rel.smul, pow_one, map_smul],
    simp only [ring_hom.id_apply, map_smul], } }

lemma mk_alg_hom_mv_polynomial_ι_eq_ι (m : M) :
  mk_alg_hom R (rel R M) (X (1, m)) = ι R m := rfl


variable {R}
def degree (v : (ℕ × M) →₀ ℕ) : ℕ := finsum (λ x, (v x) * x.1)

def is_homogeneous_of_degree (p : mv_polynomial (ℕ × M) R) (n : ℕ) : Prop :=
∀ v ∈ p.support, degree v = n 

variables (R M)

/-- The degree-n submodule of the divided power algebra -/
def grade (n : ℕ) : submodule R (divided_power_algebra R M) :=
submodule.span R 
  { u : divided_power_algebra R M | ∃ p : mv_polynomial (ℕ × M) R,
    (is_homogeneous_of_degree p n ∧ mk_alg_hom R (rel R M) p = u) }

-- instance : module R (direct_sum ℕ (λ (i : ℕ), ↥(grade R M i))) := infer_instance

lemma one_mem : (1 : divided_power_algebra R M) ∈ grade R M 0 :=
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

/-- degree of a product is sum of degrees -/
lemma mul_mem ⦃i j : ℕ⦄ {gi gj : divided_power_algebra R M} (hi : gi ∈ grade R M i)
  (hj : gj ∈ grade R M j) : gi * gj ∈ grade R M (i + j) :=
begin
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
end

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
    
    
    
    sorry,
     }, 
  sorry
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

def decompose : divided_power_algebra R M → direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)) :=
λ x, quot.lift (decompose' R M) (decompose_rel' R M) (x.1)

/- graded_algebra (grade R M )-/
instance graded : graded_algebra (divided_power_algebra.grade R M) :=
{ one_mem    := one_mem R M,
  mul_mem    := mul_mem R M,
  decompose' := decompose R M, 
  left_inv   := sorry,
  right_inv  := sorry }

instance : has_one (grade R M 0) := ⟨⟨1, one_mem R M ⟩⟩

instance : has_mul (grade R M 0) := 
{ mul := λ x y, ⟨x*y, by convert mul_mem R M x.2 y.2⟩ }

@[simp] lemma grade_zero_coe_mul (x y : grade R M 0) :
  ((x * y : grade R M 0) : divided_power_algebra R M) = (x : divided_power_algebra R M) * y := rfl

@[simp] lemma grade_zero_coe_one: ((1 : grade R M 0) : divided_power_algebra R M) = 1 := rfl


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

instance : algebra R (grade R M 0) := sorry

/- We need the projections (divided_power_algebra R M) → grade R M n ,
more generally for graded algebras -/

def proj' (n : ℕ) : divided_power_algebra R M →ₗ[R] grade R M n := sorry

/- R → grade R M 0 is isomorphism -/
example : ring_equiv R (grade R M 0) := 
{ to_fun    := (proj' R M 0) ∘ (algebra_map R (divided_power_algebra R M)),
  inv_fun   := sorry,
  left_inv  := sorry,
  right_inv := sorry,
  map_mul'  := sorry,
  map_add'  := sorry }

/- ι : M → grade R M 1 is isomorphism -/
example : linear_equiv (ring_hom.id R) M (grade R M 1) :=
{ to_fun    := (proj' R M 1) ∘ ι R,
  map_add'  := sorry,
  map_smul' := sorry,
  inv_fun   := sorry,
  left_inv  := sorry,
  right_inv := sorry }

/- Define the augmentation ideal : (proj' R M 0).ker -/

/- Prove that the augmentation is an augmentation ideal,
namely there is a section -/

end divided_power_algebra

section roby
/- Formalization of Roby 1965, section 8 -/

variables (A S : Type*) [comm_ring A] [algebra A R] [comm_ring S] [algebra A S] (I : ideal R) (J : ideal S)

/- Lemma 1 : uniqueness of the dp structure on R ⊗S for I + J -/
example 

#check @algebra.tensor_product.include_left A _ R _ _ S _ _ 


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
