import divided_powers.dp_algebra.init
import divided_powers.dp_algebra.graded

/-! Polynomial laws on modules

Reference : N. Roby, Lois polynômes et lois formelles… 

-/


-- open algebra.tensor_product

open_locale tensor_product

variables {A M N : Type*}
  [comm_ring A] [add_comm_group M] [module A M] [add_comm_group N] [module A N]
variables {R R' : Type*} [comm_ring R] [comm_ring R'] [algebra A R] [algebra A R']

structure polynomial_map {A M N : Type*}
  [comm_ring A] [add_comm_group M] [module A M] [add_comm_group N] [module A N] :=
(to_fun : Π (R : Type*) [comm_ring R], 
Π [by exactI algebra A R], 
by exactI (R ⊗[A] M →ₗ[R] R ⊗[A] N))
(is_compat : ∀ {R R' : Type*} [comm_ring R] [comm_ring R'] [algebra A R] [algebra A R']
(φ : R →ₐ[A] R'), 
(φ.to_linear_map.rtensor N).comp ((to_fun R).restrict_scalars A)
= ((to_fun R').restrict_scalars A).comp 
  (φ.to_linear_map.rtensor M))




