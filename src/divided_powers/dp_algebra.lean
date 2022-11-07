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
variables (M : Type*) [add_comm_monoid M] [module R M]

namespace divided_power_algebra

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
  { u : divided_power_algebra R M | ∃ (s : finset (ℕ × M)) (hs : finset.sum s (λ x, x.1) = n),
    finset.prod s (λ x, mk_alg_hom R (rel R M) (X x)) = u }

instance : has_one (grade R M 0) := 
⟨⟨1, submodule.subset_span ⟨{(0, 0)}, by rw [sum_singleton], by
  rw [prod_singleton, ← map_one (mk_alg_hom R (rel R M)), mk_alg_hom_rel R rel.zero]⟩⟩⟩

instance : has_mul (grade R M 0) := 
{ mul := λ x y, ⟨x*y, by sorry⟩ }

@[simp] lemma grade_zero_coe_mul (x y : grade R M 0) :
  ((x * y : grade R M 0) : divided_power_algebra R M) = (x : divided_power_algebra R M) * y := rfl

@[simp] lemma grade_zero_coe_one: ((1 : grade R M 0) : divided_power_algebra R M) = 1 := rfl

end divided_power_algebra

/- graded_algebra (grade R M )-/
instance graded_divided_power_algebra : graded_algebra (divided_power_algebra.grade R M) :=
{ one_mem    := sorry,
  mul_mem    := sorry,
  decompose' := sorry,
  left_inv   := sorry,
  right_inv  := sorry }

namespace divided_power_algebra

instance : module R (grade R M 0) := (grade R M 0).module

instance : has_add (grade R M 0) := infer_instance

instance : comm_ring (grade R M 0) := 
{ add           := (+),
  add_assoc     := add_assoc,
  zero          := 0,
  zero_add      := zero_add,
  add_zero      := add_zero,
  neg           := has_neg.neg,
  add_left_neg  := add_left_neg,
  add_comm      := add_comm,
  one           := 1,
  mul           := (*),
  mul_assoc     := λ x y z, by ext; simp only [grade_zero_coe_mul, mul_assoc],
  one_mul       := λ x, by  ext; rw [grade_zero_coe_mul, grade_zero_coe_one, one_mul],
  mul_one       := λ x, by  ext; rw [grade_zero_coe_mul, grade_zero_coe_one, mul_one],
  left_distrib  := λ x y z, by ext; simp only [submodule.coe_add, grade_zero_coe_mul, left_distrib],
  right_distrib := λ x y z, 
    by ext; simp only [submodule.coe_add, grade_zero_coe_mul, right_distrib],
  mul_comm      := λ x y, by ext; simp only [grade_zero_coe_mul, mul_comm],
  /- ..(grade R M 0).module -- Why isn't this working? -/ }


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