/- Copyright 2022 ACL @ MIdFF-/

import algebra.free_algebra
import algebra.ring_quot
import algebra.triv_sq_zero_ext
import algebra.algebra.operations
import linear_algebra.multilinear.basic
import ring_theory.graded_algebra.basic

import divided_powers.basic
import divided_powers.ideal_add

noncomputable theory

/-! 
The divided power algebra of a module -/

open finset mv_polynomial ring_quot

variables (R : Type*) [comm_ring R]
variables (M : Type*) [add_comm_group M] [module R M]

namespace divided_power_algebra

-- The class of X (n, a) will be equal to dpow n a, with a ∈ M.
inductive rel : mv_polynomial (ℕ × M) R → mv_polynomial (ℕ × M) R → Prop
-- force `ι` to be linear and creates the divided powers
| zero {a : M} : rel (X (0, a)) 1
| smul {r : R} {n : ℕ} {a : M} : rel (X (n, r • a)) (r^n • X (n, a))
| mul {m n : ℕ} {a : M} : rel (X (m, a) * X (n, a)) ((nat.choose (m + n) n) • X (m + n, a))
| add {n : ℕ} {a b : M} : rel (X (n, a+b)) 
  (finset.sum (range (n + 1)) (λ k, (X (k, a) * X (n - k, b))))

end divided_power_algebra

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

variable (M)
def grade (n : ℕ) : submodule R (divided_power_algebra R M) :=
submodule.span R 
  { u : divided_power_algebra R M | ∃ (s : multiset (ℕ × M)) 
    (hs : (s.map (λ x : ℕ × M, x.1)).sum = n),
    (s.map (λ x, mk_alg_hom R (rel R M) (X x))).prod = u }

lemma one_mem : (1 : divided_power_algebra R M) ∈ grade R M 0 := 
submodule.subset_span ⟨{(0, 0)}, by rw [multiset.map_singleton, multiset.sum_singleton], 
  by { rw [multiset.map_singleton, multiset.prod_singleton, 
    ← map_one (mk_alg_hom R (rel R M)), mk_alg_hom_rel R rel.zero]}⟩

lemma mul_mem ⦃i j : ℕ⦄ {gi gj : divided_power_algebra R M} (hi : gi ∈ grade R M i)
  (hj : gj ∈ grade R M j) : gi * gj ∈ grade R M (i + j) :=
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

instance : module R (direct_sum ℕ (λ (i : ℕ), ↥(grade R M i))) := infer_instance

noncomputable! def decompose'' : ℕ × M → direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)) :=
begin 
  intro x,
  apply direct_sum.of _ x.1 _,
  set y : divided_power_algebra R M := ring_quot.mk_ring_hom (rel R M) (X x),
  use y,
  simp only [grade],
  apply submodule.subset_span,
  --simp only [exists_prop, set.mem_set_of_eq],
  --use multiset.add_singleton_eq_iff,
  use {x},
  sorry
end

noncomputable! def decompose' : mv_polynomial (ℕ × M) R →+ direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)) :=
begin 
  --change add_monoid_algebra R ((ℕ × M)  →₀ ℕ) →+ direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)),
  --refine add_monoid_algebra.lift_nc  _ _,
  --intro x,
  --apply direct_sum.mk,
  sorry
end

#exit

noncomputable! def decompose : divided_power_algebra R M →+ direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)) :=
begin 
  intro x,
  apply quot.lift,
  sorry
end

#exit
/- graded_algebra (grade R M )-/
instance graded : graded_algebra (divided_power_algebra.grade R M) :=
{ one_mem    := one_mem R M,
  mul_mem    := mul_mem R M,
  decompose' := sorry,
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

/- and a divided power structure on that ideal such that
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

end divided_power_algebra

/- Introduce notation ?
Here : x ^ [n] = mk_alg_hom R _ (X (x, n))
In general, x ^ [n]  for dpow n x ? 

-/