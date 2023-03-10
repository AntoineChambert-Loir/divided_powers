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

def w_degree : (σ →₀ ℕ) → M := λ p, finsupp.sum p (λ s n, n • (w s))

def s_degree (w : σ → M) (s : finset (σ →₀ ℕ)) : 
finset M := finset.image (w_degree w) s

lemma weighted_homogeneous_component_mem (w : σ → M) (φ : mv_polynomial σ R) (m : M) :
  weighted_homogeneous_component w m φ ∈ weighted_homogeneous_submodule R w m :=
begin
  rw mem_weighted_homogeneous_submodule, 
  exact weighted_homogeneous_component_is_weighted_homogeneous m φ, 
end

variable (R)
def decompose' : mv_polynomial σ R → direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i)) := 
λ φ, direct_sum.mk 
  (λ (i : M), ↥(weighted_homogeneous_submodule R w i))
  (s_degree w φ.support)
  (λ m, ⟨weighted_homogeneous_component w m φ, weighted_homogeneous_component_mem w φ m⟩)
#check decompose'

example (w : σ → M) (m : M) : weighted_homogeneous_submodule R w m 
  →+ mv_polynomial σ R := (weighted_homogeneous_submodule R w m).subtype

def yolo := direct_sum.to_module R M (mv_polynomial σ R) (λ (m : M), (weighted_homogeneous_submodule R w m).subtype)

#check yolo

example (φ: mv_polynomial σ R) :
  φ = yolo R w (decompose' R w φ) := 
begin
  unfold yolo,
  unfold decompose', 

end

def decompose'a : mv_polynomial σ R →ₐ[R] direct_sum M (λ (i : M), ↥(weighted_homogeneous_submodule R w i)) := { 
to_fun := λ φ, direct_sum.mk 
  (λ (i : M), ↥(weighted_homogeneous_submodule R w i))
  (s_degree w φ.support)
  (λ m, ⟨weighted_homogeneous_component w m φ, weighted_homogeneous_component_mem w φ m⟩),
map_one' := 
begin

sorry,
end,
map_mul' := sorry,
map_zero' := sorry, 
map_add' := sorry, 
commutes' := sorry, }

example (w : σ → M) (φ : mv_polynomial σ R) (i : M) (m : σ →₀ ℕ) 
  :
   coeff m ((weighted_homogeneous_component w i) φ) = coeff m (φ i)
:= begin
sorry
end


  


#check decompose' R w
def left_inv' : function.left_inverse ⇑(direct_sum.coe_add_monoid_hom (λ (i : M), ↥(weighted_homogeneous_submodule R w i))) (decompose' R w) :=
begin
end

def graded_polynomial_algebra : graded_algebra 
(λ (m : M), weighted_homogeneous_submodule R w m)  := graded_algebra.of_alg_hom (λ (m : M), weighted_homogeneous_submodule R w m) (sorry) (sorry) (sorry) 


end mv_polynomial

end graded_algebra