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

open mv_polynomial


variables (R : Type*) [comm_ring R]
variables (M : Type*) [add_comm_monoid M] [module R M]

namespace divided_power_algebra

/- TODO : change to ℕ × M because (x,n) represents dpow n x -/
inductive rel : mv_polynomial (ℕ × M) R → mv_polynomial (ℕ × M) R → Prop
-- force `ι` to be linear and creates the divided powers
| zero {a : M} : rel (X (0, a)) 1
| smul {r : R} {n : ℕ} {a : M} : rel (X (n, r • a)) (r^n • X (n, a))
| mul {m n : ℕ} {a : M} : rel (X (m, a) * X (n, a))
  ((nat.choose (m + n) n) • X (m + n, a))
| add {n : ℕ} {a b : M} : rel (X (n, a+b)) 
  (finset.sum (finset.range (n + 1)) (λ k, (X (k, a) * X (n - k, b))))

end divided_power_algebra

@[derive [inhabited, comm_ring, algebra R]]
def divided_power_algebra:= ring_quot (divided_power_algebra.rel R M)

namespace divided_power_algebra

variable {M}

/--
The canonical linear map `M →ₗ[R] divided_power_algebra R M`.
-/
def ι : M →ₗ[R] (divided_power_algebra R M) :=
{ to_fun := λ m, (ring_quot.mk_alg_hom R _ (X (1, m))),
  map_add' := λ x y, by { 
    rw [←alg_hom.map_add, ring_quot.mk_alg_hom_rel R rel.add],
    simp only [finset.sum_range_succ', finset.sum_range_zero, zero_add, nat.sub_zero,
    nat.sub_self], 
    simp only [alg_hom.map_add, alg_hom.map_mul],
    simp only [ring_quot.mk_alg_hom_rel R rel.zero],
    simp only [alg_hom.map_one, one_mul, mul_one], },
  map_smul' := λ r x, by { 
    rw [← alg_hom.map_smul, ring_quot.mk_alg_hom_rel R rel.smul, pow_one, alg_hom.map_smul],
    simp only [ring_hom.id_apply, alg_hom.map_smul], } }

lemma ring_quot_mk_alg_hom_mv_polynomial_ι_eq_ι (m : M) :
  ring_quot.mk_alg_hom R (rel R M) (X (1, m)) = ι R m := rfl

variable (M)
def grade (n : ℕ) : submodule R (divided_power_algebra R M) :=
submodule.span R 
  { u : divided_power_algebra R M | ∃ (s : finset (ℕ × M)) (hs : finset.sum s (λ x, x.1) = n),
  finset.prod s (λ x, ring_quot.mk_alg_hom R (rel R M) (X x)) = u}

end divided_power_algebra

/- graded_algebra (grade R M )-/
instance graded_divided_power_algebra : graded_algebra (divided_power_algebra.grade R M) := { 
  one_mem := sorry,
  mul_mem := sorry,
  decompose' := sorry,
  left_inv := sorry,
  right_inv := sorry }

namespace divided_power_algebra

instance : comm_ring (grade R M 0) := sorry
instance : algebra R (grade R M 0) := sorry

/- We need the projections (divided_power_algebra R M) → grade R M n ,
more generally for graded algebras -/

def proj' (n : ℕ) : divided_power_algebra R M →ₗ[R] grade R M n := sorry

/- R → grade R M 0 is isomorphism -/
example : ring_equiv R (grade R M 0) := { 
  to_fun := (proj' R M 0) ∘ (algebra_map R (divided_power_algebra R M)),
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry,
  map_mul' := sorry,
  map_add' := sorry }

/- ι : M → grade R M 1 is isomorphism -/
example : linear_equiv (ring_hom.id R) M (grade R M 1) := { 
  to_fun := (proj' R M 1) ∘ ι R,
  map_add' := sorry,
  map_smul' := sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

/- Define the augmentation ideal : (proj' R M 0).ker -/

/- and a divided power structure on that ideal such that
dpow R n (ι R x) = ring_quot.mk_alg_hom R (rel R M) (X (x, n)) 

(x,n) represents dpow n x
dpow m (x,n) should be dpow m (dpow n x) = (mchoose m n) dpow (m*n) x
An element x in divided_power_algebra R M takes the form
ring_quot.mk_alg_hom R (rel R M) (P)
where P is a sum of monomials  a * (m,n)   : m ∈ M, n ∈ ℕ
define
dpow k x = sum products a ^ kᵢ * dpow (mchoose kᵢ nᵢ (mᵢ,nᵢ * kᵢ)) 
where the sum is over functions → ℕ, with sum k
-/

/- Prove that it is unique… -/

end divided_power_algebra

/- Introduce notation ?
Here : x ^ [n] = ring_quot.mk_alg_hom R _ (X (x, n))
In general, x ^ [n]  for dpow n x ? 

-/