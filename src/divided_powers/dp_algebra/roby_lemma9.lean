

import ring_theory.tensor_product
import ring_theory.ideal.quotient_operations
import algebra.algebra.subalgebra.basic

open_locale tensor_product
local notation  M ` ⊗[`:100 R `] `:0 N:100 := tensor_product R M N

/- The goal is to prove lemma 9 in Roby (1965) -/

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

section module

variables (R : Type*) [comm_ring R] 
 (R' : Type*) [comm_ring R'] 
 (M : Type*) [add_comm_group M] [module R M] [module R' M] 
 (N : Type*) [add_comm_group N] [module R N] [module R' N] 

variable [tensor_product.compatible_smul R' R M N]
variables [smul_comm_class R' R M] [smul_comm_class R' R N] 

-- variables [algebra R R'] [is_scalar_tower R R' M] [is_scalar_tower R R' N]

example : module R (M ⊗[R'] N) := infer_instance

example : smul_comm_class R' R M := infer_instance 

def h_aux : M → N →ₗ[R] (M ⊗[R'] N) := λ m, {
  to_fun := λ n, m ⊗ₜ[R'] n, 
  map_add' := tensor_product.tmul_add m, 
  map_smul' := λ r n, by simp only [tensor_product.tmul_smul, ring_hom.id_apply],}

variables (x : M) (y : N)

variables {R R' M N}
lemma h_aux_apply (m : M) (n : N) : h_aux R R' M N m n = m ⊗ₜ[R'] n := rfl

def h : M →ₗ[R] N →ₗ[R] (M ⊗[R'] N) := {
  to_fun := h_aux R R' M N,
  map_add' := λ m m',
  begin 
    ext n, simp only [h_aux_apply, linear_map.add_apply, tensor_product.add_tmul],
  end,
  map_smul' := λ r m, linear_map.ext (λ n, 
  begin
    simp only [h_aux_apply, ring_hom.id_apply, linear_map.smul_apply],
    refl,
  end) }


end module

section algebra


variables (R : Type*) [comm_ring R] 
 (R' : Type*) [comm_ring R'] 
 (M : Type*) [comm_ring M] [algebra R M] [algebra R' M] 
 (N : Type*) [comm_ring N] [algebra R N] [algebra R' N] 

section smul_comm 

variable [smul_comm_class R' R M] 
-- variables [algebra R R'] [is_scalar_tower R R' M] [is_scalar_tower R R' N]

example : module R (M ⊗[R'] N) := infer_instance
-- tensor_product.left_module

instance algebra.tensor_product.left_algebra' : algebra R (M ⊗[R'] N) := 
  algebra.of_module'
  (λ a x, tensor_product.induction_on x
    rfl
    (λ s t, by simp [algebra.tensor_product.one_def, tensor_product.smul_tmul'])
    (λ x₁ x₂ h₁ h₂, by simp [mul_add, h₁, h₂]))
  -- Copy pasting worked ?!?!?!?!?
  (λ a x, tensor_product.induction_on x
    rfl
    (λ s t, by simp [algebra.tensor_product.one_def, tensor_product.smul_tmul'])
    (λ x₁ x₂ h₁ h₂, by simp [add_mul, h₁, h₂]))

-- def algebra.tensor_product.algebra' : algebra R (M ⊗[R] N) := algebra.tensor_product.left_algebra R R M N 

lemma algebra.tensor_product.algebra'_eq_algebra : 
algebra.tensor_product.left_algebra' R R M N 
  = algebra.tensor_product.tensor_product.algebra :=
by { ext, exact rfl,}

example : comm_ring (M ⊗[R'] M) :=  infer_instance

-- instance : algebra R (M ⊗[R] N) := tensor_product.algebra' R R' M N 

def algebra.tensor_product.include_left' : M →ₐ[R] (M ⊗[R'] N) := {
  to_fun := algebra.tensor_product.include_left,
  map_one' := ring_hom.map_one _, -- rfl,
  map_mul' := ring_hom.map_mul _, --  λ x y, by simp only [algebra.tensor_product.include_left_apply, algebra.tensor_product.tmul_mul_tmul, mul_one],
  map_zero' := ring_hom.map_zero _, -- by simp only [algebra.tensor_product.include_left_apply, tensor_product.zero_tmul],
  map_add' := ring_hom.map_add _, -- λ x y, by simp only [algebra.tensor_product.include_left_apply, tensor_product.add_tmul],
  commutes' := λ a,
  begin
    simp only [algebra.tensor_product.include_left_apply],
    simp only [algebra.algebra_map_eq_smul_one],
    simp only [← tensor_product.smul_tmul'],
    refl,
  end }

end smul_comm

section tensor_product_compatible 

variables [smul_comm_class R' R M] [tensor_product.compatible_smul R' R M N]
-- variables [algebra R R'] [is_scalar_tower R R' M] [is_scalar_tower R R' N]

def tensor_product.include_right' : N →ₐ[R] (M ⊗[R'] N) := {
to_fun := algebra.tensor_product.include_right,
map_one' := rfl,
map_mul' := by convert algebra.tensor_product.include_right.map_mul, 
map_zero' := by convert algebra.tensor_product.include_right.map_zero,
map_add' := by convert algebra.tensor_product.include_right.map_add,
commutes' := λ a, by { 
  simp only [algebra.tensor_product.include_right_apply,
    algebra.algebra_map_eq_smul_one, tensor_product.tmul_smul], 
  refl,} }

def tensor_product.can  : (M ⊗[R] N) →ₐ[R] (M ⊗[R'] N) :=
begin
  convert algebra.tensor_product.product_map (tensor_product.include_left' R R' M N) (tensor_product.include_right' R R' M N),
  apply algebra.tensor_product.algebra'_eq_algebra, 
end

/- The following lemma should be straightforward, 
but the `convert` in the definition of `tensor_product.can`
leads to a `cast _` which I can't unfold.   -/
lemma tensor_product.can_apply (m : M) (n: N) : 
  tensor_product.can R R' M N (m ⊗ₜ[R] n) = m ⊗ₜ[R'] n := 
begin
  simp only [tensor_product.can], 
  simp, 
  simp_rw [tensor_product.include_left', tensor_product.include_right', algebra.tensor_product.include_left, algebra.tensor_product.include_right],
  simp only [ring_hom.to_fun_eq_coe, alg_hom.coe_mk],
  simp only [algebra.tensor_product.product_map],
sorry,
end


def tensor_product.can_ker : ideal (M ⊗[R] N) :=
  ideal.span ((λ (r : R'), ((r • (1 : M)) ⊗ₜ[R] (1 : N)) - ((1 : M) ⊗ₜ[R] (r • (1 : N)))) '' ⊤) 


example : N →ₐ[R] M ⊗[R] N :=
begin
  convert @algebra.tensor_product.include_right R _ M _ _ N _ _, 
  apply algebra.tensor_product.algebra'_eq_algebra, 
end

example : N →ₐ[R] M ⊗[R] N :=tensor_product.include_right' R R M N

example : N →ₐ[R'] M ⊗[R'] N :=tensor_product.include_right' R' R' M N

end tensor_product_compatible

section is_scalar_tower

variables [algebra R R'] [is_scalar_tower R R' M] [is_scalar_tower R R' N]

def tensor_product.can'_left : 
M →ₐ[R'] (M ⊗[R] N) ⧸ (tensor_product.can_ker R R' M N) := 
  (ideal.quotient.mkₐ R' (tensor_product.can_ker R R' M N)).comp
    (tensor_product.include_left' R' R M N)

def tensor_product.can'_right : 
N →ₐ[R] (M ⊗[R] N) ⧸ (tensor_product.can_ker R R' M N) := 
  (ideal.quotient.mkₐ R (tensor_product.can_ker R R' M N)).comp
    (tensor_product.include_right' R R M N) 

lemma is_R'_linear : is_linear_map R' (tensor_product.can'_right R R' M N) :=
begin
  apply is_linear_map.mk,
  { exact alg_hom.map_add _, }, 
  intros r n, 
  simp [tensor_product.can'_right, tensor_product.include_right'],
  rw ← ideal.quotient.mkₐ_eq_mk R',
  rw ← alg_hom.map_smul, 
  simp only [ideal.quotient.mkₐ_eq_mk],
  apply symm,
  rw ideal.quotient.eq ,
  simp only [tensor_product.can_ker],
  suffices : r • (1 : M) ⊗ₜ[R] n - (1 : M) ⊗ₜ[R] (r • n) 
    = (r • (1 : M) ⊗ₜ[R] (1 : N) - (1 : M) ⊗ₜ[R] (r • (1 : N))) * ((1 : M) ⊗ₜ[R] n),
  rw this, 
--   suffices : (r • (1 : M) ⊗ₜ[R] (1 : N) - (1 : M) ⊗ₜ[R] (r • (1 : N))) ∈ _, 
  refine ideal.mul_mem_right ((1 : M) ⊗ₜ[R] n) _ _,
  apply ideal.subset_span,
  use ⟨r, set.mem_univ r, rfl⟩,
  simp only [sub_mul, algebra.smul_mul_assoc, algebra.tensor_product.tmul_mul_tmul, one_mul],
end

def tensor_product.can'_right' : 
N →ₐ[R'] (M ⊗[R] N) ⧸ (tensor_product.can_ker R R' M N) := {
to_fun := tensor_product.can'_right R R' M N, 
map_zero' := (is_R'_linear R R' M N).map_zero,
map_one' := rfl, 
map_add' := (is_R'_linear R R' M N).map_add,
map_mul' := alg_hom.map_mul _, 
commutes' := λ r, by simp only [algebra.algebra_map_eq_smul_one, (is_R'_linear R R' M N).map_smul, alg_hom.map_one] }

def tensor_product.can' : 
(M ⊗[R'] N) →ₐ[R'] (M ⊗[R] N) ⧸ (tensor_product.can_ker R R' M N) :=
begin
  convert algebra.tensor_product.product_map 
    (tensor_product.can'_left R R' M N) (tensor_product.can'_right' R R' M N),
  apply algebra.tensor_product.algebra'_eq_algebra, 
end

lemma tensor_product.can'_apply (m : M) (n : N) : 
  tensor_product.can' R R' M N (m ⊗ₜ[R'] n) 
  = ideal.quotient.mk _ (m ⊗ₜ[R] n) := 
begin
  simp only [tensor_product.can'], 
  simp,

sorry
end

example : (tensor_product.can R R' M N).to_ring_hom.ker = (tensor_product.can_ker R R' M N) :=
begin
  suffices h : tensor_product.can_ker R R' M N ≤ ring_hom.ker (tensor_product.can R R' M N).to_ring_hom, 
  rw ring_hom.ker_eq_ideal_iff,
  use h,
  apply function.has_left_inverse.injective , 
--  apply function.bijective.injective,
--  rw function.bijective_iff_has_inverse, 
  use tensor_product.can' R R' M N,
--   split,
  { -- left_inverse
    intro z,
    obtain ⟨y, rfl⟩ := ideal.quotient.mk_surjective z, 
    simp only [alg_hom.to_ring_hom_eq_coe, ideal.quotient.lift_mk, alg_hom.coe_to_ring_hom],

    apply tensor_product.induction_on y,
    simp only [ring_hom.map_zero, alg_hom.map_zero],
    intros m n, simp only [tensor_product.can'_apply, tensor_product.can_apply],
    intros x y hx hy, 
    simp only [ring_hom.map_add, alg_hom.map_add, ← ideal.quotient.mkₐ_eq_mk, hx, hy], },
  -- { -- right_inverse  sorry }

  -- h
  simp only [tensor_product.can_ker],
  rw ideal.span_le,
  intros z hz,
  simp only [set.top_eq_univ, set.image_univ, set.mem_range] at hz,
  obtain ⟨r, rfl⟩ := hz,
  simp only [set_like.mem_coe],
  simp only [ring_hom.sub_mem_ker_iff],
  simp only [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom],
  simp only [tensor_product.can_apply],
  simp only [tensor_product.tmul_smul],
  refl,
end

end is_scalar_tower

end algebra
