import divided_powers.dp_algebra.init
import divided_powers.dp_algebra.misc
import algebra.algebra.operations
import ring_theory.mv_polynomial.basic

import ...for_mathlib.ring_theory.tensor_product

universe u 

open_locale tensor_product 

namespace divided_power_algebra 


def _root_.alg_hom.base_change {A B C R : Type*} [comm_ring A] [comm_ring B] [algebra A B]
  [comm_ring R] [algebra A R] 
  [comm_ring C] [algebra A C] [algebra R C] [is_scalar_tower A R C] 
  (φ : B →ₐ[A] C) :  R ⊗[A] B →ₐ[R] C := 
{ commutes' := λ r, by simp only [algebra.tensor_product.algebra_map_apply, 
    algebra.id.map_eq_id, ring_hom.id_apply, alg_hom.to_fun_eq_coe,
    algebra.tensor_product.product_map_apply_tmul, is_scalar_tower.coe_to_alg_hom', 
    map_one, mul_one], 
  .. algebra.tensor_product.product_map (is_scalar_tower.to_alg_hom A R C) φ, }


noncomputable 
def dp_scalar_extension' (A : Type u) [comm_ring A] (R : Type u) [comm_ring R] [algebra A R]
  (M : Type u) [add_comm_group M] [module A M] [module R M] [is_scalar_tower A R M] :
  R ⊗[A] (divided_power_algebra A M) →ₐ[R] divided_power_algebra R M := 
begin
  apply alg_hom.base_change, 
  apply lift_aux A M (λ nm, dp R nm.1 nm.2),
  { intro m, dsimp only, rw dp_zero, },
  { intros n r m, dsimp only, 
    rw [← algebra_map_smul R r m, dp_smul R (algebra_map A R r) n m, ← map_pow,
      algebra_map_smul], },
  { intros n p m, dsimp only, rw dp_mul, },
  { intros n x y, dsimp only, rw dp_add, },
end


noncomputable
def dp_scalar_extension (A : Type u) [comm_ring A] (R : Type u) [comm_ring R] [algebra A R]
  (M : Type u) [add_comm_group M] [module A M]  :
  R ⊗[A] (divided_power_algebra A M) →ₐ[R] divided_power_algebra R (R ⊗[A] M) := 
begin
  apply alg_hom.base_change, 
  apply lift_aux A M 
    (λ nm, dp R nm.1 (1 ⊗ₜ[A] nm.2) : ℕ × M → divided_power_algebra R (R ⊗[A] M)), 
  { intro m, dsimp only, rw dp_zero, },
  { intros n a m, dsimp only, simp only [tensor_product.tmul_smul],  
    rw [← algebra_map_smul R a], rw dp_smul, 
    rw ← map_pow, rw algebra_map_smul R, 
    apply_instance,
    apply_instance, },
  { intros n p m, dsimp only, rw dp_mul, },
  { intros n x y, dsimp only, simp only [tensor_product.tmul_add], rw dp_add, }
end

noncomputable
def dp_scalar_extension_inv (A : Type u) [comm_ring A] 
  (R : Type u) [comm_ring R] [algebra A R]
  (M : Type u) [add_comm_group M] [module A M] :
  divided_power_algebra R (R ⊗[A] M) →ₐ[R] R ⊗[A] (divided_power_algebra A M) :=
begin
  let f : ℕ × M → R ⊗[A] (divided_power_algebra A M) :=
  λ nm, algebra.tensor_product.include_right (dp A nm.1 nm.2),
  apply lift_aux R M (λ nm, algebra.tensor_product.include_right (dp A nm.1 nm.2)),
  { intro m, dsimp only, rw dp_zero, rw map_one, },
  { intros n r m, dsimp only, 
  -- does not seem obvious !
    sorry, },
  { intros n p m, dsimp only, rw [← map_mul, ← map_nsmul,dp_mul], },
  { intros n x y, dsimp only, simp_rw [← map_mul, ← map_sum], rw dp_add, }
end

-- TODO ! But in Roby, this follows from the exponential power series interpretation 
def dp_scalar_extension_equiv (A : Type*) [comm_ring A] (R : Type*) [comm_ring R] [algebra A R]
  (M : Type*) [add_comm_group M] [module A M] [module R M] [is_scalar_tower A R M] :
  R ⊗[A] (divided_power_algebra A M) ≃ₐ[R] divided_power_algebra R M := 
sorry
end divided_power_algebra