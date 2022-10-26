/- Copyright 2022 ACL @ MIdFF-/

import algebra.free_algebra
import algebra.ring_quot
import algebra.triv_sq_zero_ext
import algebra.algebra.operations
import linear_algebra.multilinear.basic

import divided_powers.basic
import divided_powers.ideal_add

/-! 
The divided power algebra of a module -/


variables (R : Type*) [comm_ring R]
variables (M : Type*) [add_comm_monoid M] [module R M]

namespace divided_power_algebra

/-
inductive rel : free_algebra R (M × ℕ) → free_algebra R (M × ℕ) → Prop
-- force `ι` to be linear
| zero {a : M} : 
  rel (free_algebra.ι R (a, 0)) 1
| smul {r : R} {n : ℕ} {a : M} :
  rel (free_algebra.ι R (r • a, n)) (r^n • free_algebra.ι R (a, n))
  --  ((algebra_map R (free_algebra R (M × ℕ)) (r ^ n)) * free_algebra.ι R (a, n))
| mul {m n : ℕ} {a : M} : 
  rel (free_algebra.ι R (a,m) * free_algebra.ι R (a, n))
    (algebra_map R (free_algebra R (M × ℕ)) (nat.choose (m + n) n) * 
      free_algebra.ι R (a, m + n))
| add {n : ℕ} {a b : M} :
  rel (free_algebra.ι R (a+b,n)) (finset.sum (finset.range (n + 1)) (λ k, (free_algebra.ι R (a, k) * free_algebra.ι R (b, n - k))))
-/

inductive rel : mv_polynomial (M × ℕ) R → mv_polynomial (M × ℕ) R → Prop
-- force `ι` to be linear and creates the divided powers
| zero {a : M} : 
  rel (mv_polynomial.X (a, 0)) 1
| smul {r : R} {n : ℕ} {a : M} :
  rel (mv_polynomial.X (r • a, n)) (r^n • mv_polynomial.X (a, n))
| mul {m n : ℕ} {a : M} : 
  rel (mv_polynomial.X (a,m) * mv_polynomial.X (a, n))
    ((nat.choose (m + n) n) • mv_polynomial.X (a, m + n))
| add {n : ℕ} {a b : M} :
  rel (mv_polynomial.X (a+b,n)) 
    (finset.sum (finset.range (n + 1)) (λ k, (mv_polynomial.X (a, k) * mv_polynomial.X (b, n - k))))

end divided_power_algebra

@[derive [inhabited, comm_ring, algebra R]]
def divided_power_algebra:= ring_quot (divided_power_algebra.rel R M)

namespace divided_power_algebra

/- 
example {S : Type*} [comm_ring S] [module S M] : comm_ring (divided_power_algebra S M) :=
ring_quot.comm_ring (rel S M)
 -/

/--
The canonical linear map `M →ₗ[R] divided_power_algebra R M`.
-/
/- 
def ι : M →ₗ[R] (divided_power_algebra R M) :=
{ to_fun := λ m, (ring_quot.mk_alg_hom R _ (free_algebra.ι R (m, 1))),
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
-/

variable {M}
noncomputable
def ι : M →ₗ[R] (divided_power_algebra R M) :=
{ to_fun := λ m, (ring_quot.mk_alg_hom R _ (mv_polynomial.X (m, 1))),
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
  ring_quot.mk_alg_hom R (rel R M) (mv_polynomial.X (m, 1)) = ι R m := rfl

noncomputable
example (s : finset (M × ℕ)) :
  divided_power_algebra R M := 
  finset.prod s ((λ x, ring_quot.mk_alg_hom R (rel R M) (mv_polynomial.X x)))

variable (M)
noncomputable
def toto (n : ℕ ):= λ (s : finset (M × ℕ)) (hs : finset.sum s (λ x, x.2) = n),
  finset.prod s (λ x, ring_quot.mk_alg_hom R (rel R M) (mv_polynomial.X x))

#check toto R M 2

noncomputable
def grade (n : ℕ) : submodule R (divided_power_algebra R M) :=
submodule.span R 
  { u ∈ divided_power_algebra R M | ∃ (s : finset (M × ℕ)) (hs : finset.sum s (λ x, x.2) = n),
  finset.prod s (λ x, ring_quot.mk_alg_hom R (rel R M) (mv_polynomial.X x)) = u}

end divided_power_algebra
