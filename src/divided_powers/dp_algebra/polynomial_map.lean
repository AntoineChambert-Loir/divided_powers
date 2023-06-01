import divided_powers.dp_algebra.init
import divided_powers.dp_algebra.graded
import ring_theory.power_series.basic


/-! Polynomial laws on modules

Reference : N. Roby, Lois polynômes et lois formelles en théorie des modules… 

-/


-- open algebra.tensor_product

open_locale tensor_product

universes u v 
variables {A M N : Type u}
  [comm_semiring A] [add_comm_monoid M] [module A M] [add_comm_monoid N] [module A N]
variables {R R' : Type u} [comm_semiring R] [comm_semiring R'] [algebra A R] [algebra A R']

/-- A polynomial M → N between A-modules is a functorial family
of maps R ⊗[A] M →ₗ[R] R ⊗[A] N, for all A-algebras R -/
structure polynomial_map (A M N : Type u)
  [comm_semiring A] [add_comm_monoid M] [module A M] [add_comm_monoid N] [module A N] :=
(to_fun : Π (R : Type u) [comm_semiring R], 
Π [by exactI algebra A R], 
by exactI (R ⊗[A] M →ₗ[R] R ⊗[A] N))
(is_compat : ∀ {R R' : Type u} [comm_semiring R] [comm_semiring R'] [algebra A R] [algebra A R']
(φ : R →ₐ[A] R'), 
(φ.to_linear_map.rtensor N).comp ((to_fun R).restrict_scalars A)
= ((to_fun R').restrict_scalars A).comp 
  (φ.to_linear_map.rtensor M))

namespace polynomial_map 

variables (f g : polynomial_map A M N) 

lemma ext_iff : f = g ↔ f.to_fun = g.to_fun := 
begin
  split,
  intro h, rw h,
  intro h, cases f, cases g, congr, exact h,
end

lemma is_compat_apply (φ : R →ₐ[A] R') (x : R ⊗[A] M) : 
  (φ.to_linear_map.rtensor N) ((f.to_fun R) x) = ((f.to_fun R') (φ.to_linear_map.rtensor M x)) :=
by simpa only using linear_map.congr_fun (f.is_compat φ) x

variables {ι : Type u} (x : ι → M) (k : ι →₀ ℕ)

def linear_map.mv_polynomial.coeff (k : ι →₀ ℕ) : mv_polynomial ι A →ₗ[A] A := {
to_fun := mv_polynomial.coeff k,
map_add' := mv_polynomial.coeff_add k, 
map_smul' := mv_polynomial.coeff_smul k, }

instance has_add : has_add (polynomial_map A M N) := { 
add := λ f g, { 
  to_fun := λ R _, by exactI λ _, by exactI f.to_fun R + g.to_fun R,
  is_compat :=
  begin
    intros R R' _ _ _ _ φ , 
    resetI,
    ext, 
    simp only [linear_map.coe_comp, linear_map.coe_restrict_scalars_eq_coe, function.comp_app, linear_map.add_apply, map_add], 
    simp only [is_compat_apply],
  end } }

lemma add_def: (f + g).to_fun R = f.to_fun R + g.to_fun R := rfl

instance add_comm_monoid : add_comm_monoid (polynomial_map A M N) := {
add := has_add.add, 
add_assoc := λ f g h,
begin rw ext_iff, ext R _ _ m, resetI, simp only [add_def, add_assoc], end,
 zero := sorry ,
 zero_add := sorry,
 add_zero := sorry,
 nsmul := sorry,
 nsmul_zero' := sorry,
 nsmul_succ' := sorry,
 add_comm := sorry}


instance has_smul : has_smul A (polynomial_map A M N) := {
smul := λ a f, {
  to_fun := λ R _, by exactI λ _, by exactI a • (f.to_fun R),
  is_compat := sorry } } 

instance module : module A (polynomial_map A M N) := sorry 

example : A ⊗[A] M ≃ₗ[A] M := tensor_product.lid A M
example (k : ι →₀ ℕ): (mv_power_series ι A) ⊗[A] N →ₗ[A] N :=
 (tensor_product.lid A N).to_linear_map.comp ((mv_power_series.coeff A k).rtensor N)


noncomputable def coeff (f : polynomial_map A M N) {ι : Type u} 
  (x : ι →₀ M) (k : ι →₀ ℕ) : N :=
  tensor_product.lid A N ((linear_map.mv_polynomial.coeff k).rtensor N  (
  ((f.to_fun (mv_polynomial ι A)).restrict_scalars A) (
    finsupp.sum x (λ i m, (mv_polynomial.X i) ⊗ₜ[A] m) )))


end polynomial_map


