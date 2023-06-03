import divided_powers.dp_algebra.init
import divided_powers.dp_algebra.graded
import ring_theory.power_series.basic
import ring_theory.tensor_product 

import ...for_mathlib.ring_theory.submodule_mem

/-! Polynomial laws on modules

Reference : N. Roby, Lois polynômes et lois formelles en théorie des modules… 

-/


-- open algebra.tensor_product

section algebra

open_locale tensor_product 

variables (A : Type*) [comm_semiring A] (R : Type*) [comm_semiring R] [algebra A R]

def algebra.tensor_product.rid' : R ⊗[A] A →ₐ[R] R := {
map_one' := by simp, 
map_zero' := by simp,
commutes' := λ r, by simp, 
..  algebra.tensor_product.rid A R, }

@[simp]
lemma algebra.tensor_product.rid'_tmul (a : A) (r : R): 
(algebra.tensor_product.rid' A R) (r ⊗ₜ[A] a) = a • r := rfl 

variables (M : Type*) [add_comm_monoid M] [module A M]
def linear_form.base_change (f : M →ₗ[A] A) : R ⊗[A] M →ₗ[R] R := 
(algebra.tensor_product.rid' A R).to_linear_map.comp (linear_map.base_change R f)

lemma linear_form.base_change_apply_tmul (f : M →ₗ[A] A) (r : R) (m : M) : 
linear_form.base_change A R M f (r ⊗ₜ[A] m) = r * ((f m) • 1) := 
by simp only [linear_form.base_change, algebra.tensor_product.rid'_tmul, 
  linear_map.coe_comp, function.comp_app, linear_map.base_change_tmul, 
  alg_hom.to_linear_map_apply, algebra.mul_smul_comm, mul_one]

variables (R' : Type*) [comm_semiring R'] [algebra A R']
variable (φ : R →ₐ[A] R')

lemma linear_form.base_change_compat_apply (f : M →ₗ[A] A) (m : R ⊗[A] M) :
  φ (linear_form.base_change A R M f m) =
  (linear_form.base_change A R' M f) ((linear_map.rtensor M φ.to_linear_map) m) :=
begin
  induction m using tensor_product.induction_on with r m x y hx hy,
  simp only [map_zero],
  simp [linear_form.base_change, algebra.tensor_product.rid'_tmul],
  simp only [map_add, hx, hy],
end


end algebra

section tensor_product


end tensor_product

section mv_polynomial

variables {A : Type*} [comm_semiring A]
variable {ι : Type*} 
def linear_map.mv_polynomial.coeff (k : ι →₀ ℕ) : mv_polynomial ι A →ₗ[A] A := {
to_fun := mv_polynomial.coeff k,
map_add' := mv_polynomial.coeff_add k, 
map_smul' := mv_polynomial.coeff_smul k, }

lemma linear_map.mv_polynomial.coeff_apply (k : ι →₀ ℕ) (f : mv_polynomial ι A) :
  linear_map.mv_polynomial.coeff k f = mv_polynomial.coeff k f := rfl 


end mv_polynomial

section mv_polynomial_module

/- This is boring stuff devoted to prove the standard
linear equivalence between M[σ] and A[σ] ⊗ M 
for any A-module M and any type ι 
Probably, this should be generalized to an arbitrary monoid,
not only polynomials (corresponding to σ →₀ ℕ). 
M[σ] has to be defined has (σ →₀ M) because mathlib doesn't know 
about “the monoid module”.
-/

open_locale tensor_product

variables (σ : Type*) [decidable_eq σ] 
variables (A : Type*) [comm_semiring A] (N : Type*) [add_comm_monoid N] [module A N]

noncomputable def zoo : ((σ →₀ ℕ) →₀ N) →ₗ[A] mv_polynomial σ A ⊗[A] N :=
{to_fun := λ f, f.sum (λ k n, mv_polynomial.monomial k 1 ⊗ₜ[A] n),
map_add' := λ f g , 
begin 
  rw finsupp.sum_of_support_subset f (f.support.subset_union_left g.support), 
  rw finsupp.sum_of_support_subset g (f.support.subset_union_right g.support), 
  rw finsupp.sum_of_support_subset (f + g) (finsupp.support_add),
  rw ←finset.sum_add_distrib, 
  apply finset.sum_congr rfl,
  intros k hk, simp only [finsupp.coe_add, pi.add_apply, tensor_product.tmul_add],
  all_goals { intros k hk,rw tensor_product.tmul_zero, },
end,
map_smul' := λ a f, 
begin
  simp only [ring_hom.id_apply], rw finsupp.smul_sum,
  rw finsupp.sum_of_support_subset (a • f) (finsupp.support_smul),
  simp only [finsupp.sum],
  apply finset.sum_congr rfl,
  intros k hk, simp only [finsupp.coe_smul, pi.smul_apply, tensor_product.tmul_smul],
  intros k hk,rw tensor_product.tmul_zero,
end }

lemma zoo_apply_single (k : σ →₀ ℕ) (n : N): 
zoo σ A N (finsupp.single k n) = (mv_polynomial.monomial k) 1 ⊗ₜ[A] n :=
by simp only [zoo, finsupp.sum_single_index, tensor_product.tmul_zero, linear_map.coe_mk]

noncomputable def zoo_inv' : mv_polynomial σ A ⊗[A] N →ₗ[A] ((σ →₀ ℕ) → N) := {
to_fun := λ f k, tensor_product.lid A N (linear_map.rtensor N (linear_map.mv_polynomial.coeff k) f),
map_add' := λ f g,
begin
  ext k, simp only [map_add, pi.add_apply], 
end,
map_smul' := λ a f, 
begin
  ext k,
  simp only [linear_map.map_smulₛₗ, ring_hom.id_apply, linear_equiv.map_smulₛₗ, pi.smul_apply],
end }

lemma zoo_inv'_apply_tmul (f : mv_polynomial σ A) (n : N) (k : σ →₀ ℕ): 
  zoo_inv' σ A N (f ⊗ₜ[A] n) k = mv_polynomial.coeff k f • n := 
by simp only [zoo_inv', linear_map.coe_mk, linear_map.rtensor_tmul, tensor_product.lid_tmul, linear_map.mv_polynomial.coeff_apply]

lemma zoo_inv'_eq (f : mv_polynomial σ A) (n : N) :
zoo_inv' σ A N (f ⊗ₜ[A] n) = λ k, mv_polynomial.coeff k f • n := 
begin
  ext k,
  rw zoo_inv'_apply_tmul,
end

lemma zoo_inv'_support (p : mv_polynomial σ A ⊗[A] N) : 
  (function.support (zoo_inv' σ A N p)).finite := 
begin
  classical,
  induction p using tensor_product.induction_on with f n f g hf hg,
  -- case C0
  simp only [map_zero, function.support_zero', set.finite_empty],

  -- case C1,
  { apply set.finite.subset (mv_polynomial.support f).finite_to_set, 
    intro k,
    simp only [function.mem_support, finset.mem_coe, mv_polynomial.mem_support_iff, not_imp_not, zoo_inv'_apply_tmul], 
    intro hk, simp only [hk, zero_smul], },

  -- case Cp
  { simp only [map_add], 
    refine set.finite.subset (set.finite.union hf hg) (function.support_add _ _), },
end

noncomputable def zoo_inv : mv_polynomial σ A ⊗[A] N →ₗ[A] ((σ →₀ ℕ) →₀ N) := {
to_fun := λ p, finsupp.of_support_finite _ (zoo_inv'_support σ A N p),
map_add' := λ p q, 
begin
  rw finsupp.ext_iff, intro k,
  simp only [finsupp.of_support_finite_coe, map_add, finsupp.coe_add, pi.add_apply],
end,
map_smul' := λ a p, 
begin
  rw finsupp.ext_iff, intro k,
  simp only [finsupp.of_support_finite_coe, linear_map.map_smulₛₗ, finsupp.coe_smul],
end }

lemma zoo_inv_coe_apply (p : mv_polynomial σ A ⊗[A] N) : 
  zoo_inv' σ A N p = zoo_inv σ A N p := rfl

lemma zoo_inv_apply_tmul (f : mv_polynomial σ A) (n : N) :
   zoo_inv σ A N (f ⊗ₜ[A] n) = f.sum (λ (k : (σ →₀ ℕ)) (a : A), finsupp.single k (a • n)) := 
begin
  conv_lhs { rw f.as_sum, },
  simp_rw tensor_product.sum_tmul,
  rw map_sum, 
  simp only [finsupp.sum],
  apply finset.sum_congr rfl, 
  intros k hk,
  ext l,
  rw ← zoo_inv_coe_apply, rw zoo_inv'_apply_tmul,
  simp only [mv_polynomial.coeff_monomial],
  simp only [finsupp.single_apply],
  split_ifs with h, refl, rw zero_smul,
end

lemma zoo_inv'_comp_zoo (f : (σ →₀ ℕ) →₀ N)(k : σ →₀ ℕ) :
zoo_inv' σ A N (zoo σ A N f) k = f k :=
begin
  dsimp only [zoo, finsupp.sum], dsimp, 
  rw map_sum, 
  simp_rw zoo_inv'_eq, 
  simp_rw [mv_polynomial.coeff_monomial],
  simp only [finset.sum_apply], 
  rw finset.sum_eq_single k, 
  simp only [eq_self_iff_true, if_true, one_smul], 
  intros b hb hb', simp only [if_neg hb', zero_smul],
  rw finsupp.not_mem_support_iff, intro hk, simp only [hk, smul_zero],
end

lemma zoo_inv_zoo_apply (f) : zoo_inv σ A N (zoo σ A N f) = f := 
begin
  ext k, 
  rw [←zoo_inv_coe_apply σ A N, zoo_inv'_comp_zoo ],
end

/- lemma zoo_inv_zoo' : function.left_inverse (zoo_inv σ A N) (zoo σ A N) :=
zoo_inv_zoo_apply σ A N -/

lemma zoo_inv_zoo : (zoo_inv σ A N).comp (zoo σ A N) = linear_map.id := 
begin
  apply linear_map.ext, intro f,
  simp only [zoo_inv_zoo_apply, linear_map.coe_comp, function.comp_app, linear_map.id_coe, id.def],
end

lemma zoo_injective : function.injective (zoo σ A N) := 
begin
  apply function.has_left_inverse.injective,
  use zoo_inv σ A N,
  exact zoo_inv_zoo_apply σ A N, 
end

lemma zoo_zoo_inv_of_tmul (f : mv_polynomial σ A) (n : N) : 
  zoo σ A N (zoo_inv σ A N (f ⊗ₜ[A] n)) = f ⊗ₜ[A] n :=
begin
  rw zoo_inv_apply_tmul, simp only [finsupp.sum],
  rw map_sum, 
  simp_rw zoo_apply_single,
  conv_rhs {rw f.as_sum},
  rw tensor_product.sum_tmul,
  apply finset.sum_congr rfl,
  intros k hk, 
  rw tensor_product.tmul_smul,  rw tensor_product.smul_tmul', 
  apply congr_arg2 _ _ rfl,
  rw ← map_smul,
  apply congr_arg, simp only [algebra.id.smul_eq_mul, mul_one],
  refl,
end

lemma zoo_zoo_inv_apply (p : mv_polynomial σ A ⊗[A] N) : zoo σ A N (zoo_inv σ A N p) = p :=
begin
  induction p using tensor_product.induction_on with f n f g hf hg,
  simp only [map_zero],
  rw zoo_zoo_inv_of_tmul,
  simp only [map_add, hf, hg], 
end

lemma zoo_surjective : function.surjective (zoo σ A N) :=
begin
  apply function.has_right_inverse.surjective,
  use zoo_inv σ A N,  
  exact zoo_zoo_inv_apply σ A N, 
end

lemma zoo_zoo_inv : (zoo σ A N).comp (zoo_inv σ A N) = linear_map.id :=
begin
  apply linear_map.ext, intro p,
  simp only [zoo_zoo_inv_apply, linear_map.coe_comp, function.comp_app, linear_map.id_coe, id.def],
end

lemma zoo_inv_injective : function.injective (zoo_inv σ A N) := 
begin
  apply function.has_left_inverse.injective,
  use zoo σ A N,
  exact zoo_zoo_inv_apply σ A N, 
end

noncomputable def linear_map_equiv : ((σ →₀ ℕ) →₀ N) ≃ₗ[A] mv_polynomial σ A ⊗[A] N  := {
inv_fun := zoo_inv σ A N,
left_inv := zoo_inv_zoo_apply σ A N,
right_inv := zoo_zoo_inv_apply σ A N,
.. zoo σ A N }

end mv_polynomial_module


open_locale tensor_product

universes u v 
variables {A M N : Type u}
  [comm_semiring A] [add_comm_monoid M] [module A M] [add_comm_monoid N] [module A N]
variables {R R' : Type u} [comm_semiring R] [comm_semiring R'] [algebra A R] [algebra A R']

/-- A polynomial M → N between A-modules is a functorial family
of maps R ⊗[A] M → R ⊗[A] N, for all A-algebras R -/
structure polynomial_map (A M N : Type u)
  [comm_semiring A] [add_comm_monoid M] [module A M] [add_comm_monoid N] [module A N] :=
(to_fun : Π (R : Type u) [comm_semiring R], Π [by exactI algebra A R], by exactI 
  (R ⊗[A] M → R ⊗[A] N))
(is_compat : ∀ {R R' : Type u} [comm_semiring R] [comm_semiring R'] 
  [algebra A R] [algebra A R'] (φ : R →ₐ[A] R'), 
  (φ.to_linear_map.rtensor N) ∘ (to_fun R) = (to_fun R') ∘ (φ.to_linear_map.rtensor M))

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
by simpa only using congr_fun (f.is_compat φ) x

section module

instance has_add : has_add (polynomial_map A M N) := { 
add := λ f g, { 
  to_fun := λ R _, by exactI λ _, by exactI f.to_fun R + g.to_fun R,
  is_compat :=
  begin
    intros R R' _ _ _ _ φ , 
    resetI,
    ext, 
    simp only [map_add, is_compat_apply, function.comp_app, pi.add_apply],
  end } }

@[simp]
lemma add_def: (f + g).to_fun R = f.to_fun R + g.to_fun R := rfl

instance add_comm_monoid : add_comm_monoid (polynomial_map A M N) := {
add := has_add.add, 
add_assoc := λ f g h,
begin rw ext_iff, ext R _ _ m, resetI, simp only [add_def, add_assoc], end,
 zero := {
  to_fun := λ R _, by exactI λ _, by exactI 0, 
  is_compat := λ R R' _ _ _ _ φ, rfl, },
zero_add := λ f, 
begin
 rw ext_iff, ext R _ _ m, simp only [add_def, zero_add], 
end,
add_zero := λ f,
begin
 rw ext_iff, ext R _ _ m, simp only [add_def, add_zero], 
end,
nsmul := λ n f, {
  to_fun := λ R _, by exactI λ _, by exactI (n • (f.to_fun R)),
  is_compat := λ R R' _ _ _ _ φ, 
  begin 
    ext m, 
    simp only [is_compat_apply, map_nsmul, function.comp_app, pi.smul_apply],
  end, },
nsmul_zero' := λ f,
begin
  rw ext_iff, ext R _ _ m, simp [zero_smul], refl,
end,
nsmul_succ' := λ n f, 
begin
  rw ext_iff, ext R _ _m, 
  simp only [add_def, pi.smul_apply, pi.add_apply, nat.succ_eq_one_add, add_smul, one_smul],
end,
add_comm := λ f g,
begin
  rw ext_iff, ext R _ _ m, simp [add_def],
  rw add_comm,
end }

instance has_smul : has_smul A (polynomial_map A M N) := {
smul := λ a f, {
  to_fun := λ R _, by exactI λ _, by exactI a • (f.to_fun R),
  is_compat := λ R R' _ _ _ _ φ, 
  begin 
    ext m, 
    simp  [is_compat_apply],
  end } } 

lemma smul_def (a : A) : (a • f).to_fun R = a • (f.to_fun R) := rfl 

instance : mul_action A (polynomial_map A M N) := { 
one_smul := λ f, 
begin
  rw ext_iff, ext R _ _ m, simp only [smul_def, one_smul],
end,
mul_smul := λ a b f,
begin
  rw ext_iff, ext R _ _ m, simp only [smul_def, mul_smul], 
end,}

instance : distrib_mul_action A (polynomial_map A M N) := { 
  smul_zero := λ a, by refl, 
  smul_add := λ a f g, 
  begin
    rw ext_iff, ext R _ _ m, simp only [smul_def, add_def, smul_add],
  end, }

instance module : module A (polynomial_map A M N) := {
add_smul := λ a b f,
begin
  rw ext_iff, ext R _ _ m, simp [smul_def,add_def, add_smul], 
end,
zero_smul := λ f, 
begin  
  rw ext_iff, ext R _ _ m, simp only [smul_def, zero_smul], refl,
end, }

end module

section comp

variables {P : Type u} [add_comm_monoid P] [module A P]

def comp : polynomial_map A N P → polynomial_map A M N → polynomial_map A M P :=
λ g f, {
to_fun := λ R _, by exactI λ _, by exactI (g.to_fun R).comp (f.to_fun R),
is_compat := λ R R' _ _ _ _ φ, 
begin
  ext m, 
  simp only [is_compat_apply, function.comp_app],
end }

lemma comp_to_fun (f : polynomial_map A M N) (g : polynomial_map A N P) :
  (g.comp f).to_fun R = (g.to_fun R).comp (f.to_fun R) := rfl

lemma comp_apply (f : polynomial_map A M N) (g : polynomial_map A N P) 
  (m : R ⊗[A] M) : (g.comp f).to_fun R m = (g.to_fun R) (f.to_fun R m) := rfl

variables {Q : Type u} [add_comm_monoid Q] [module A Q]

lemma comp_assoc (f : polynomial_map A M N) (g : polynomial_map A N P) (h : polynomial_map A P Q) :
h.comp (g.comp f) = (h.comp g).comp f :=
begin
  rw ext_iff, 
  ext R _ _ m,
  simp only [comp_to_fun],
end

end comp

section coefficients

variables {ι : Type u} [fintype ι] [decidable_eq ι]

/-- The coefficients of a `polynomial_map` -/
noncomputable def coeff' (m : ι → M) (k : ι →₀ ℕ) : 
  polynomial_map A M N  →ₗ[A] N := { 
to_fun := λ f, tensor_product.lid A N ((linear_map.mv_polynomial.coeff k).rtensor N
  (f.to_fun (mv_polynomial ι A)
    (finset.univ.sum (λ i, (mv_polynomial.X i) ⊗ₜ[A] m i)))), 
map_add' := λ f g, by simp only [add_def, pi.add_apply, map_add],
map_smul' := λ a f, by simp only [smul_def, pi.smul_apply, linear_map.map_smulₛₗ, ring_hom.id_apply, linear_equiv.map_smulₛₗ] }


/-- The coefficients of a `polynomial_map` -/
noncomputable def coeff (m : ι → M) : polynomial_map A M N
  →ₗ[A] ((ι →₀ ℕ) →₀ N) := {
to_fun := λ f, zoo_inv _ A N (f.to_fun (mv_polynomial ι A)
    (finset.univ.sum (λ i, (mv_polynomial.X i) ⊗ₜ[A] m i))),
map_add' := λ f g, 
by { rw ← map_add, refl, },
map_smul' := λ a f, 
by { simp only [ring_hom.id_apply, ← map_smul], refl, }, }


lemma coeff_eq (m : ι → M) (k : ι →₀ ℕ) 
  (f : polynomial_map A M N) :
  coeff m f k = 
  (tensor_product.lid A N)
  ((linear_map.rtensor N (linear_map.mv_polynomial.coeff k))
     (f.to_fun (mv_polynomial ι A) (finset.univ.sum (λ (i : ι), mv_polynomial.X i ⊗ₜ[A] m i)))) :=
by simp only [coeff, linear_map.coe_mk, zoo_inv, zoo_inv', finsupp.of_support_finite_coe]


theorem image_eq_coeff_sum  (r : ι → R) (m : ι → M) (f : polynomial_map A M N) :
f.to_fun R (finset.univ.sum (λ i, r i ⊗ₜ[A] m i)) =
(coeff m f).sum (λ k n, finset.univ.prod (λ i, r i ^ (k i)) ⊗ₜ[A] n) := 
begin
  suffices : f.to_fun (mv_polynomial ι A) (finset.univ.sum (λ i, mv_polynomial.X i ⊗ₜ[A] m i)) = (coeff m f).sum (λ k n, mv_polynomial.monomial k 1 ⊗ₜ n),

  let φ : mv_polynomial ι A →ₐ[A] R := mv_polynomial.aeval r, 
  have that := congr_fun (f.is_compat φ) (finset.univ.sum (λ i, mv_polynomial.X i ⊗ₜ[A] m i)), 
  simp only [function.comp_app, linear_map.map_sum, linear_map.rtensor_tmul, alg_hom.to_linear_map_apply, mv_polynomial.aeval_X] at that, 
  rw ← that, rw this, 
  simp only [finsupp.sum], 
  rw map_sum,  
  apply finset.sum_congr rfl,
  intros k hk, simp only [linear_map.rtensor_tmul, alg_hom.to_linear_map_apply], 
  apply congr_arg2 _ _ rfl,
  simp  [φ, mv_polynomial.aeval_monomial], 

  -- The generic case
  simp only [coeff], dsimp,
  generalize : f.to_fun (mv_polynomial ι A) (finset.univ.sum (λ (i : ι), mv_polynomial.X i ⊗ₜ[A] m i)) = p, 
  obtain ⟨g, rfl⟩ := zoo_surjective ι A N p,
  rw zoo_inv_zoo_apply, refl,
end

lemma span_tensor_product_eq_top_of_span_eq_top
  (σ : Type*) (e : σ → M) (hm : submodule.span A (set.range e) = ⊤) :
  (submodule.span R (set.range (λ s, (1 : R) ⊗ₜ[A] (e s))) : 
  submodule R (R ⊗[A] M)) = ⊤ :=
begin
  rw eq_top_iff,
  intros m h,
  induction m using tensor_product.induction_on with r m x y hx hy,
  exact zero_mem _,
  { let f : M →ₗ[A] R ⊗[A] M := {
    to_fun := λ m, (1 : R) ⊗ₜ[A] m, 
    map_add' := λ x y, sorry,
    map_smul' := λ a x, sorry, },
    have hf : ∀ (m : M), (1 : R) ⊗ₜ[A] m = f m, intro m, refl,
    suffices : r ⊗ₜ[A] m = r • ((1 : R) ⊗ₜ[A] m),
    rw this, 
    refine submodule.smul_mem _ r _,
    apply submodule.span_le_restrict_scalars A ,
    rw hf, simp_rw hf, 
    convert submodule.apply_mem_span_image_of_mem_span f _,
    swap, exact set.range e, 
    conv_rhs {rw ← set.image_univ,}, 
    rw set.image_image , 
    rw set.image_univ, 
    rw hm, exact submodule.mem_top,
    rw tensor_product.smul_tmul', simp only [algebra.id.smul_eq_mul, mul_one], },
  exact submodule.add_mem _ (hx submodule.mem_top) (hy submodule.mem_top),
end


lemma coeff_injective (m : ι → M) (hm : submodule.span A (set.range m) = ⊤) 
  (f g : polynomial_map A M N) 
  (h : coeff m f = coeff m g) : f = g :=
begin
  resetI,
  rw ext_iff,
  ext R _ _ p,
  resetI,
  have h : p ∈ ⊤ := submodule.mem_top, 
  rw ←  span_tensor_product_eq_top_of_span_eq_top ι m hm at h,
  rw submodule.mem_span_iff_exists_sum _ p at h, 
  simp [tensor_product.smul_tmul'] at h,
  obtain ⟨r, rfl⟩ := h, 
  rw finsupp.sum_of_support_subset _ (finset.subset_univ _), 
  rw image_eq_coeff_sum r m f, 
  simp only [image_eq_coeff_sum], rw h,
  intros i hi, simp only [tensor_product.zero_tmul],
end

noncomputable def finsupp.polynomial_map (b : basis ι A M) (h : (ι →₀ ℕ) →₀ N) : 
polynomial_map A M N := {
to_fun := λ R _ _ x, by exactI 
  h.sum (λ k n, finset.univ.prod 
    (λ i, (linear_form.base_change A R _ (b.coord i)) x ^ (k i)) ⊗ₜ[A] n),
is_compat := λ R R' _ _ _ _ φ, 
begin
  resetI,
  ext m,
  dsimp,
  simp only [finsupp.sum],
  rw map_sum,
  apply finset.sum_congr rfl,

  intros k hk,
  simp only [linear_map.rtensor_tmul, alg_hom.to_linear_map_apply],
  apply congr_arg2 _ _ rfl,
  rw map_prod φ, 
  apply finset.prod_congr rfl,
  intros i hi,
  rw map_pow, 
  apply congr_arg2 _ _ rfl,
  rw linear_form.base_change_compat_apply,
end }

lemma finsupp.polynomial_map_to_fun_apply (b : basis ι A M) (h : (ι →₀ ℕ) →₀ N)
(m : R ⊗[A] M) :
(finsupp.polynomial_map b h).to_fun R m = 
h.sum (λ k n, finset.univ.prod 
    (λ i, (linear_form.base_change A R _ (b.coord i)) m ^ (k i)) ⊗ₜ[A] n) :=
    rfl

example (f g : ι → ℕ) (i : ι): (f + g) i = f i + g i :=
begin
exact pi.add_apply f g i
end

.

lemma coeff_of_finsup_polynomial_map (b : basis ι A M) (h : (ι →₀ ℕ) →₀ N) :
  coeff (coe_fn b) (finsupp.polynomial_map b h) = h :=
begin
  simp only [coeff], dsimp,
  conv_rhs { rw ← zoo_inv_zoo_apply ι A N h, },
  apply congr_arg,
  simp only [zoo, finsupp.polynomial_map], 
  dsimp,
  apply congr_arg,
  ext k, 
  apply congr_arg2 _ _ rfl,
  rw mv_polynomial.monomial_eq,
  simp,
  apply congr_arg,
  ext i,
  congr,
  rw finset.sum_eq_single_of_mem i (finset.mem_univ i),
  simp [linear_form.base_change],
  intros j hj hij, 
  simp only [linear_form.base_change_apply_tmul],
  rw [basis.coord_apply,  basis.repr_self, finsupp.single_apply],
  rw if_neg hij,
  simp only [zero_smul, mul_zero],
end

lemma finsup_polynomial_map_of_coeff (b : basis ι A M) (f : polynomial_map A M N) : 
  finsupp.polynomial_map b (coeff (coe_fn b) f) = f :=
begin
  apply coeff_injective  (coe_fn b),
  { rw eq_top_iff, intros m hm,
    apply submodule.span_mono _ (basis.mem_span_repr_support b m),
    apply set.image_subset_range, },
  rw coeff_of_finsup_polynomial_map, 
end

example (b : basis ι A M) (i j : ι) :
  (b.coord i) (b j) = ite (j = i) 1 0 :=
  by
  rw [basis.coord_apply,  basis.repr_self, finsupp.single_apply]


noncomputable def coeff_polynomial_map_equiv (b : basis ι A M) : 
((ι →₀ ℕ) →₀ N) ≃ₗ[A] polynomial_map A M N := {
to_fun := λ h, finsupp.polynomial_map b h,
map_add' := λ h k, 
begin
  rw ext_iff,
  ext R _ _ m,
  simp only [finsupp.polynomial_map_to_fun_apply, add_def, pi.add_apply],
  rw finsupp.sum_of_support_subset h (h.support.subset_union_left k.support), 
  rw finsupp.sum_of_support_subset k (h.support.subset_union_right k.support), 
  rw finsupp.sum_of_support_subset (h + k) (finsupp.support_add),
  simp_rw [finsupp.coe_add, pi.add_apply, tensor_product.tmul_add],
  rw finset.sum_add_distrib,
  all_goals { intros i hi, rw [tensor_product.tmul_zero], },
end,
map_smul' := λ a h, 
begin
  rw ext_iff, ext R _ _ m,  resetI,
  simp only [ring_hom.id_apply, smul_def, pi.smul_apply],

  simp [finsupp.polynomial_map_to_fun_apply],
  rw finsupp.sum_of_support_subset (a • h) (finsupp.support_smul),
  simp only [finsupp.sum, finset.smul_sum],
  apply finset.sum_congr rfl,
  intros k hk, 
  simp [finsupp.coe_smul, pi.smul_apply, tensor_product.tmul_smul],

  intros k hk, rw tensor_product.tmul_zero,
end,
inv_fun := λ f,  coeff (coe_fn b) f, 
left_inv := λ h, by { dsimp, rw coeff_of_finsup_polynomial_map, },
right_inv := λ f, by { dsimp, rw finsup_polynomial_map_of_coeff b, } }

end coefficients

end polynomial_map 
