
import ...for_mathlib.ring_theory.tensor_product
import ring_theory.ideal.quotient_operations
import algebra.algebra.subalgebra.basic
-- import ...generalisation.generalisation_linter



open_locale tensor_product
local notation  M ` ⊗[`:100 R `] `:0 N:100 := tensor_product R M N

/- The goal is to prove lemma 9 in Roby (1965) -/

section ring_hom

lemma ring_hom.ker_eq_ideal_iff  {A B : Type*} [comm_ring A] [comm_ring B] (f : A →+* B) (I : ideal A) :
  f.ker = I ↔ ∃ (h : I ≤ f.ker), function.injective (ideal.quotient.lift I f h) := 
begin
  split,
  { intro hI, use le_of_eq hI.symm,
    apply ring_hom.lift_injective_of_ker_le_ideal, 
    simp only [hI, le_refl], },
  { rintro ⟨hI, h⟩, 
    simp only [ring_hom.injective_iff_ker_eq_bot,
    ideal.ker_quotient_lift f hI,
    ideal.map_eq_bot_iff_le_ker,
    ideal.mk_ker] at h,
    exact le_antisymm h hI, },
end

end ring_hom

variables (R : Type*) [comm_ring R] 
 (S : Type*) [comm_ring S] 

variables (M : Type*) [comm_ring M] [algebra R M] [algebra S M] 
 (N : Type*) [comm_ring N] [algebra R N] [algebra S N]

variables [algebra R S] [is_scalar_tower R S M] [is_scalar_tower R S N] 
-- [tensor_product.compatible_smul R S M N]

open algebra.tensor_product tensor_product

def φ : (M ⊗[R] N) →ₐ[R] (M ⊗[S] N) :=
algebra.tensor_product.product_map (algebra.tensor_product.include_left.restrict_scalars R) (algebra.tensor_product.include_right.restrict_scalars R)

lemma φ_apply (m : M) (n: N) : 
  φ R S M N (m ⊗ₜ[R] n) = m ⊗ₜ[S] n := 
by simp only [φ, product_map_apply_tmul, alg_hom.coe_restrict_scalars', include_left_apply, include_right_apply, tmul_mul_tmul,
  _root_.mul_one, _root_.one_mul]

lemma φ_surjective : function.surjective (φ R S M N) :=
begin
  intro z, 
  apply tensor_product.induction_on z, 
  use 0, simp only [map_zero],
  intros m n, use m ⊗ₜ n, simp only [φ_apply], 
  rintros _ _ ⟨x, rfl⟩ ⟨y, rfl⟩, use x + y, simp only [map_add],
end

def kerφ : ideal (M ⊗[R] N) :=
  ideal.span ((λ (r : S), ((r • (1 : M)) ⊗ₜ[R] (1 : N)) - ((1 : M) ⊗ₜ[R] (r • (1 : N)))) '' ⊤) 

example : N →ₐ[R] M ⊗[R] N :=
include_right

example : N →ₐ[R] M ⊗[R] N := include_right

example : N →ₐ[S] M ⊗[S] N := include_right

def ψ_left' : 
M →ₐ[R] (M ⊗[R] N) ⧸ (kerφ R S M N) := 
  ((ideal.quotient.mkₐ S (kerφ R S M N)).restrict_scalars R).comp 
    (algebra.tensor_product.include_left)

def ψ_left : M →ₐ[S] (M ⊗[R] N) ⧸ (kerφ R S M N) := {
commutes' := λ s,
begin

  simp only [alg_hom.to_fun_eq_coe, alg_hom.coe_comp, alg_hom.coe_restrict_scalars',  function.comp_app, include_left_apply], 
  simp only [algebra.algebra_map_eq_smul_one],
  suffices : (s • (1 : M)) ⊗ₜ[R] (1 : N) = s • 1, 
  rw [this, alg_hom.map_smul, alg_hom.map_one], 
  refl,
end .. ((ideal.quotient.mkₐ S (kerφ R S M N)).restrict_scalars R).comp 
    (algebra.tensor_product.include_left) } -- ψ_left' R S M N }

def ψ_right' : 
N →ₐ[R] (M ⊗[R] N) ⧸ (kerφ R S M N) := 
  (ideal.quotient.mkₐ R (kerφ R S M N)).comp (include_right) 

lemma is_S_linear : is_linear_map S (ψ_right' R S M N) :=
begin
  apply is_linear_map.mk,
  { exact alg_hom.map_add _, }, 
  intros r n, 
  simp [ψ_right', include_right],
  rw ← ideal.quotient.mkₐ_eq_mk S,
  rw ← alg_hom.map_smul, 
  simp only [ideal.quotient.mkₐ_eq_mk],
  apply symm,
  rw ideal.quotient.eq ,
  suffices : r • (1 : M) ⊗ₜ[R] n - (1 : M) ⊗ₜ[R] (r • n) 
    = (r • (1 : M) ⊗ₜ[R] (1 : N) - (1 : M) ⊗ₜ[R] (r • (1 : N))) * ((1 : M) ⊗ₜ[R] n),
  rw this, 
  refine ideal.mul_mem_right ((1 : M) ⊗ₜ[R] n) _ _,
  apply ideal.subset_span,
  use ⟨r, set.mem_univ r, rfl⟩,

  simp only [sub_mul, algebra.smul_mul_assoc, tmul_mul_tmul, comm_ring.one_mul, comm_ring.mul_one],
end

def ψ_right : 
N →ₐ[S] (M ⊗[R] N) ⧸ (kerφ R S M N) := {
to_fun := ψ_right' R S M N, 
map_zero' := (is_S_linear R S M N).map_zero,
map_one' := rfl, 
map_add' := (is_S_linear R S M N).map_add,
map_mul' := alg_hom.map_mul _, 
commutes' := λ r, by simp only [algebra.algebra_map_eq_smul_one, (is_S_linear R S M N).map_smul, alg_hom.map_one] }

def ψ : (M ⊗[S] N) →ₐ[S] (M ⊗[R] N) ⧸ (kerφ R S M N) :=
product_map (ψ_left R S M N) (ψ_right R S M N)

lemma ψ_apply (m : M) (n : N) : ψ R S M N (m ⊗ₜ[S] n) 
  = ideal.quotient.mk _ (m ⊗ₜ[R] n) := 
begin
  simp only [ψ, ψ_left, ψ_right', ψ_right], 
  simp only [alg_hom.coe_comp, ideal.quotient.mkₐ_eq_mk, product_map_apply_tmul, function.comp_app, include_left_apply,
  alg_hom.coe_mk, include_right_apply],
  rw ← ring_hom.map_mul,
  simp only [tmul_mul_tmul, _root_.mul_one, _root_.one_mul],
end

example : (φ R S M N).to_ring_hom.ker = kerφ R S M N :=
begin
  suffices h : kerφ R S M N ≤ ring_hom.ker (φ R S M N).to_ring_hom, 
  rw ring_hom.ker_eq_ideal_iff,
  use h,
  apply function.has_left_inverse.injective , 
--  apply function.bijective.injective,
--  rw function.bijective_iff_has_inverse, 
  use ψ R S M N,
--   split,
  { -- left_inverse
    intro z,
    obtain ⟨y, rfl⟩ := ideal.quotient.mk_surjective z, 
    simp only [alg_hom.to_ring_hom_eq_coe, ideal.quotient.lift_mk, alg_hom.coe_to_ring_hom],

    apply tensor_product.induction_on y,
    simp only [ring_hom.map_zero, alg_hom.map_zero],
    intros m n, simp only [ψ_apply, φ_apply],
    intros x y hx hy, 
    simp only [ring_hom.map_add, alg_hom.map_add, ← ideal.quotient.mkₐ_eq_mk, hx, hy], },
  -- { -- right_inverse  sorry }

  -- h
  simp only [kerφ],
  rw ideal.span_le,
  intros z hz,
  simp only [set.top_eq_univ, set.image_univ, set.mem_range] at hz,
  obtain ⟨r, rfl⟩ := hz,
  simp only [set_like.mem_coe],
  simp only [ring_hom.sub_mem_ker_iff],
  simp only [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom],
  simp only [φ_apply],
  simp only [tensor_product.tmul_smul],
  refl,
end



#exit 

/- Checking 21 declarations (plus 79 automatically generated ones) in the current file with 1 linters -/

/- The `generalisation_linter` linter reports: -/
/- typeclass generalisations may be possible -/
#check @h_aux /- _inst_11: smul_comm_class ↝
 -/
#check @algebra.tensor_product.left_algebra' /- _inst_7: algebra ↝
 -/
#check @algebra.tensor_product.can_ker /- _inst_2: comm_ring ↝ comm_semiring module
_inst_3: comm_ring ↝ distrib_mul_action module ring
_inst_5: algebra ↝ has_smul module
_inst_6: comm_ring ↝ distrib_mul_action module ring
_inst_8: algebra ↝ has_smul module
_inst_9: smul_comm_class ↝
_inst_10: tensor_product.compatible_smul ↝
 -/
#check @algebra.tensor_product.can'_left /- _inst_11: is_scalar_tower ↝ tensor_product.compatible_smul
 -/
#check @algebra.tensor_product.can'_right /- _inst_11: is_scalar_tower ↝ tensor_product.compatible_smul
 -/



/- 
section algebra 

namespace algebra.tensor_product

open algebra.tensor_product

section semiringR 

variables (R : Type*) [comm_semiring R] 
 (R' : Type*) [comm_semiring R'] 

section semiring


variables (M : Type*) [semiring M] [algebra R M] [algebra R' M] 
 (N : Type*) [semiring N] [algebra R N] [algebra R' N] 

section smul_comm 

variables [smul_comm_class R' R M] -- [smul_comm_class R' R N]
-- variables [algebra R R'] [is_scalar_tower R R' M] [is_scalar_tower R R' N]

example : module R (M ⊗[R'] N) := infer_instance
-- tensor_product.left_module

instance left_algebra' : algebra R (M ⊗[R'] N) := 
  algebra.of_module'
  (λ a x, tensor_product.induction_on x
    rfl
    (λ s t, by simp [one_def, tensor_product.smul_tmul'])
    (λ x₁ x₂ h₁ h₂, by simp [mul_add, h₁, h₂]))
  -- Copy pasting worked ?!?!?!?!?
  (λ a x, tensor_product.induction_on x
    rfl
    (λ s t, by simp [one_def, tensor_product.smul_tmul'])
    (λ x₁ x₂ h₁ h₂, by simp [add_mul, h₁, h₂]))


example : algebra R (M ⊗[R] N) := infer_instance 
-- algebra.tensor_product.left_algebra

/- This means that one has two algebra structures on M ⊗[R] N when R = R',
one given by `algebra.tensor_product.left_algebra` 
(implicit parameters R, M and N) 
and the other given by `algebra.tensor_product.left_algebra' R R M N` 
One should thus remove the less general instance from mathlib 
or maybe set : 
`instance algebra' : algebra R (M ⊗[R] N) := left_algebra R R M N `
Nevertheless, they coincide : -/

lemma algebra'_eq_algebra : 
tensor_product.left_algebra' R R M N  = tensor_product.algebra := 
  by { ext, exact rfl,}

example : semiring (M ⊗[R'] N) := infer_instance -- tensor_product.semiring

def include_left' : M →ₐ[R] (M ⊗[R'] N) := {
  to_fun := include_left,
  map_one' := ring_hom.map_one _, -- rfl,
  map_mul' := ring_hom.map_mul _, --  λ x y, by simp only [include_left_apply, tmul_mul_tmul, mul_one],
  map_zero' := ring_hom.map_zero _, -- by simp only [include_left_apply, tensor_product.zero_tmul],
  map_add' := ring_hom.map_add _, -- λ x y, by simp only [include_left_apply, tensor_product.add_tmul],
  commutes' := λ a,
  begin
    simp only [include_left_apply],
    simp only [algebra.algebra_map_eq_smul_one],
    simp only [← tensor_product.smul_tmul'],
    refl,
  end }

end smul_comm

section tensor_product_compatible

variables [smul_comm_class R' R M] 
  -- [smul_comm_class R' R N] 
  [tensor_product.compatible_smul R' R M N]

def include_right' : N →ₐ[R] (M ⊗[R'] N) := {
to_fun := include_right,
map_one' := rfl,
map_mul' := by convert include_right.map_mul, 
map_zero' := by convert include_right.map_zero,
map_add' := by convert include_right.map_add,
commutes' := λ a, by { 
  simp only [include_right_apply,
    algebra.algebra_map_eq_smul_one, tensor_product.tmul_smul], 
  refl,} }

end tensor_product_compatible

end semiring

section comm_semiring 

variables (M : Type*) [comm_semiring M] [algebra R M] [algebra R' M] 
 (N : Type*) [comm_semiring N] [algebra R N] [algebra R' N] 

/- section tensor_product_compatible 

variables [smul_comm_class R' R M] [smul_comm_class R' R N] [tensor_product.compatible_smul R' R M N]
-- variables [algebra R R'] [is_scalar_tower R R' M] [is_scalar_tower R R' N]

open algebra.tensor_product

def include_right' : N →ₐ[R] (M ⊗[R'] N) := {
to_fun := include_right,
map_one' := rfl,
map_mul' := by convert include_right.map_mul, 
map_zero' := by convert include_right.map_zero,
map_add' := by convert include_right.map_add,
commutes' := λ a, by { 
  simp only [include_right_apply,
    algebra.algebra_map_eq_smul_one, tensor_product.tmul_smul], 
  refl,} }

end tensor_product_compatible -/

variables [smul_comm_class R' R M] 
  -- [smul_comm_class R' R N] 
  [tensor_product.compatible_smul R' R M N]

example : algebra R (M ⊗[R'] N) := infer_instance
-- tensor_product.left_algebra' R R' M N

example : semiring (M ⊗[R'] N) := tensor_product.semiring
instance tensor_product.comm_semiring : comm_semiring (M ⊗[R'] N) := {
mul_comm := λ a b, 
  begin
    apply tensor_product.induction_on b, 
    simp only [mul_zero, zero_mul],
    { intros x y,
      apply tensor_product.induction_on a, 
      simp only [zero_mul, mul_zero],
      { intros x' y', simp only [tmul_mul_tmul, mul_comm], },
      { intros x' y' hx' hy', 
        simp only [add_mul, mul_add, hx', hy'], }, },
    { intros x y hx hy, simp only [mul_add, add_mul, hx, hy], },
  end,
  ..tensor_product.semiring,
} -/