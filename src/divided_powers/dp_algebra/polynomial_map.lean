import divided_powers.dp_algebra.init
import divided_powers.dp_algebra.graded
import ring_theory.power_series.basic
import ring_theory.tensor_product 

import ...for_mathlib.ring_theory.submodule_mem

/-! Polynomial laws on modules

Reference : N. Roby, Lois polynômes et lois formelles en théorie des modules… 

-/

open algebra function linear_map

section algebra

open_locale tensor_product 

variables (A : Type*) [comm_semiring A] (R : Type*) [comm_semiring R] [algebra A R]

namespace algebra.tensor_product
/- The natural `R`-algebra map from `R ⊗[A] A` to `R`. -/
def rid' : R ⊗[A] A →ₐ[R] R := 
{ map_one'  := by simp only [alg_equiv.to_fun_eq_coe, map_one], 
  map_zero' := by simp only [alg_equiv.to_fun_eq_coe, map_zero],
  commutes' := λ r, by simp only [algebra_map_apply, alg_equiv.to_fun_eq_coe, rid_tmul, one_smul], 
  ..algebra.tensor_product.rid A R, }

@[simp] lemma rid'_tmul (a : A) (r : R) : (rid' A R) (r ⊗ₜ[A] a) = a • r := rfl 

end algebra.tensor_product

open algebra.tensor_product

variables (M : Type*) [add_comm_monoid M] [module A M]

-- Q (not important): I am not sure if `linear_form` is used in mathlib.
namespace linear_form

def base_change (f : M →ₗ[A] A) : R ⊗[A] M →ₗ[R] R := 
(rid' A R).to_linear_map.comp (base_change R f)

lemma base_change_apply_tmul (f : M →ₗ[A] A) (r : R) (m : M) : 
  base_change A R M f (r ⊗ₜ[A] m) = r * ((f m) • 1) := 
by simp only [base_change, rid'_tmul, coe_comp, comp_app, base_change_tmul, 
  alg_hom.to_linear_map_apply, mul_smul_comm, _root_.mul_one]

variables (R' : Type*) [comm_semiring R'] [algebra A R'] (φ : R →ₐ[A] R')

lemma base_change_compat_apply (f : M →ₗ[A] A) (m : R ⊗[A] M) :
  φ (base_change A R M f m) = (base_change A R' M f) ((rtensor M φ.to_linear_map) m) :=
begin
  induction m using tensor_product.induction_on with r m x y hx hy,
  { simp only [map_zero] },
  { simp only [base_change, rid'_tmul, coe_comp, comp_app, base_change_tmul,
      alg_hom.to_linear_map_apply, alg_hom.map_smul, rtensor_tmul] },
  { simp only [map_add, hx, hy]} ,
end

end linear_form

end algebra

namespace mv_polynomial

variables {A : Type*} [comm_semiring A] {ι : Type*} 

-- I think it makes more sense to have this in the `mv_polynomial` namespace
--def linear_map.mv_polynomial.coeff (k : ι →₀ ℕ) : mv_polynomial ι A →ₗ[A] A := 
def coeff_hom (k : ι →₀ ℕ) : mv_polynomial ι A →ₗ[A] A := -- or `coeff_linear_map`
{ to_fun    := coeff k,
  map_add'  := coeff_add k, 
  map_smul' := coeff_smul k, }

lemma coeff_hom_apply (k : ι →₀ ℕ) (f : mv_polynomial ι A) :
  coeff_hom k f = mv_polynomial.coeff k f := rfl 

end mv_polynomial


section mv_polynomial_module

/- This is boring stuff devoted to prove the standard linear equivalence between M[σ] and A[σ] ⊗ M 
  for any A-module M and any type ι.
  Probably, this should be generalized to an arbitrary monoid, not only polynomials (corresponding 
  to σ →₀ ℕ). M[σ] has to be defined has (σ →₀ M) because mathlib doesn't know 
  about “the monoid module”. -/

open_locale tensor_product

variables (σ : Type*) [decidable_eq σ] (A : Type*) [comm_semiring A] (N : Type*) 
  [add_comm_monoid N] [module A N]

open finsupp

-- TODO: rename
noncomputable def zoo : ((σ →₀ ℕ) →₀ N) →ₗ[A] mv_polynomial σ A ⊗[A] N :=
{ to_fun := λ f, f.sum (λ k n, mv_polynomial.monomial k 1 ⊗ₜ[A] n),
  map_add' := λ f g , 
  begin 
    rw [sum_of_support_subset f (f.support.subset_union_left g.support), 
      sum_of_support_subset g (f.support.subset_union_right g.support), 
      sum_of_support_subset (f + g) support_add, ← finset.sum_add_distrib], 
    apply finset.sum_congr rfl,
    intros k hk, 
    rw [coe_add, pi.add_apply, tensor_product.tmul_add],
    all_goals { intros k hk, rw tensor_product.tmul_zero, },
  end,
  map_smul' := λ a f, 
  begin
    rw [ring_hom.id_apply, smul_sum, sum_of_support_subset (a • f) support_smul, finsupp.sum],
    apply finset.sum_congr rfl,
    intros k hk, 
    simp only [finsupp.coe_smul, pi.smul_apply, tensor_product.tmul_smul],
    { intros k hk, rw tensor_product.tmul_zero },
  end }

lemma zoo_apply_single (k : σ →₀ ℕ) (n : N) : 
  zoo σ A N (single k n) = (mv_polynomial.monomial k) 1 ⊗ₜ[A] n :=
by simp only [zoo, sum_single_index, tensor_product.tmul_zero, linear_map.coe_mk]

noncomputable def zoo_inv' : mv_polynomial σ A ⊗[A] N →ₗ[A] ((σ →₀ ℕ) → N) := 
{ to_fun    := λ f k, tensor_product.lid A N (linear_map.rtensor N (mv_polynomial.coeff_hom k) f),
  map_add'  := λ f g, by ext k; simp only [map_add, pi.add_apply], 
  map_smul' := λ a f, by ext k; 
    simp only [linear_map.map_smulₛₗ, ring_hom.id_apply, linear_equiv.map_smulₛₗ, pi.smul_apply] }

lemma zoo_inv'_apply_tmul (f : mv_polynomial σ A) (n : N) (k : σ →₀ ℕ): 
  zoo_inv' σ A N (f ⊗ₜ[A] n) k = mv_polynomial.coeff k f • n := 
by simp only [zoo_inv', linear_map.coe_mk, linear_map.rtensor_tmul, tensor_product.lid_tmul,
  mv_polynomial.coeff_hom_apply]

lemma zoo_inv'_eq (f : mv_polynomial σ A) (n : N) :
  zoo_inv' σ A N (f ⊗ₜ[A] n) = λ k, mv_polynomial.coeff k f • n := 
by ext k; rw zoo_inv'_apply_tmul

lemma zoo_inv'_support (p : mv_polynomial σ A ⊗[A] N) : (support (zoo_inv' σ A N p)).finite := 
begin
  induction p using tensor_product.induction_on with f n f g hf hg,
  -- case C0
  { simp only [map_zero, support_zero', set.finite_empty] },
  -- case C1,
  { apply set.finite.subset (mv_polynomial.support f).finite_to_set,
    intro k,
    simp only [mem_support, finset.mem_coe, mv_polynomial.mem_support_iff, not_imp_not, 
      zoo_inv'_apply_tmul], 
    intro hk, 
    rw [hk, zero_smul] },
  -- case Cp
  { rw [map_add], 
    exact set.finite.subset (set.finite.union hf hg) (function.support_add _ _), },
end

noncomputable def zoo_inv : mv_polynomial σ A ⊗[A] N →ₗ[A] ((σ →₀ ℕ) →₀ N) := 
{ to_fun := λ p, of_support_finite _ (zoo_inv'_support σ A N p),
  map_add' := λ p q, 
  by ext k; simp only [of_support_finite_coe, map_add, coe_add, pi.add_apply],
  map_smul' := λ a p, 
  by ext k; simp only [of_support_finite_coe, linear_map.map_smulₛₗ, finsupp.coe_smul] }

lemma zoo_inv_coe_apply (p : mv_polynomial σ A ⊗[A] N) : zoo_inv' σ A N p = zoo_inv σ A N p := rfl

lemma zoo_inv_apply_tmul (f : mv_polynomial σ A) (n : N) :
   zoo_inv σ A N (f ⊗ₜ[A] n) = f.sum (λ (k : (σ →₀ ℕ)) (a : A), single k (a • n)) := 
begin
  conv_lhs { rw f.as_sum, },
  rw [tensor_product.sum_tmul, _root_.map_sum, finsupp.sum],
  apply finset.sum_congr rfl, 
  intros k hk,
  ext l,
  rw [← zoo_inv_coe_apply, zoo_inv'_apply_tmul, mv_polynomial.coeff_monomial, single_apply],
  split_ifs with h, 
  { refl }, 
  { rw zero_smul}
end


lemma zoo_inv'_comp_zoo (f : (σ →₀ ℕ) →₀ N) (k : σ →₀ ℕ) :
  zoo_inv' σ A N (zoo σ A N f) k = f k :=
begin
  simp only [zoo, finsupp.sum, linear_map.coe_mk, _root_.map_sum, zoo_inv'_eq,
    mv_polynomial.coeff_monomial, finset.sum_apply], 
  rw finset.sum_eq_single k, 
  {  simp only [eq_self_iff_true, if_true, one_smul] }, 
  { intros b hb hb', 
    rw [if_neg hb', zero_smul] },
  { rw finsupp.not_mem_support_iff, 
    intro hk,
    rw [hk, smul_zero] },
end

lemma zoo_inv_zoo_apply (f) : zoo_inv σ A N (zoo σ A N f) = f := 
by ext k; rw [← zoo_inv_coe_apply σ A N, zoo_inv'_comp_zoo ]

/- lemma zoo_inv_zoo' : function.left_inverse (zoo_inv σ A N) (zoo σ A N) :=
zoo_inv_zoo_apply σ A N -/

lemma zoo_inv_zoo : (zoo_inv σ A N).comp (zoo σ A N) = id := 
by ext f; simp only [zoo_inv_zoo_apply, coe_comp, comp_app, id_coe, id.def]

lemma zoo_injective : function.injective (zoo σ A N) := 
function.has_left_inverse.injective ⟨zoo_inv σ A N, zoo_inv_zoo_apply σ A N⟩

lemma zoo_zoo_inv_of_tmul (f : mv_polynomial σ A) (n : N) : 
  zoo σ A N (zoo_inv σ A N (f ⊗ₜ[A] n)) = f ⊗ₜ[A] n :=
begin
  conv_rhs {rw f.as_sum},
  rw [zoo_inv_apply_tmul, finsupp.sum, linear_map.map_sum, tensor_product.sum_tmul],
  apply finset.sum_congr rfl,
  intros k hk, 
  rw [zoo_apply_single, tensor_product.tmul_smul, tensor_product.smul_tmul', ← map_smul, 
    algebra.id.smul_eq_mul, mul_one],
  refl,
end

lemma zoo_zoo_inv_apply (p : mv_polynomial σ A ⊗[A] N) : zoo σ A N (zoo_inv σ A N p) = p :=
begin
  induction p using tensor_product.induction_on with f n f g hf hg,
  { rw [map_zero, map_zero] },
  { rw zoo_zoo_inv_of_tmul },
  { rw [map_add, map_add, hf, hg] }
end

lemma zoo_surjective : function.surjective (zoo σ A N) :=
function.has_right_inverse.surjective ⟨zoo_inv σ A N, zoo_zoo_inv_apply σ A N⟩

lemma zoo_zoo_inv : (zoo σ A N).comp (zoo_inv σ A N) = linear_map.id :=
begin
  apply linear_map.ext,
  intro p,
  simp only [zoo_zoo_inv_apply, linear_map.coe_comp, function.comp_app, linear_map.id_coe, id.def]
end



lemma zoo_inv_injective : function.injective (zoo_inv σ A N) := 
function.has_left_inverse.injective ⟨zoo σ A N, zoo_zoo_inv_apply σ A N⟩

noncomputable def linear_map_equiv : ((σ →₀ ℕ) →₀ N) ≃ₗ[A] mv_polynomial σ A ⊗[A] N  := 
{ inv_fun   := zoo_inv σ A N,
  left_inv  := zoo_inv_zoo_apply σ A N,
  right_inv := zoo_zoo_inv_apply σ A N,
  .. zoo σ A N }

end mv_polynomial_module

#exit


open_locale tensor_product

universes u v₁ v₂ v₃ v₄ w w'
variables {A : Type u} {M : Type v₁} {N : Type v₂}
  [comm_semiring A] [add_comm_monoid M] [module A M] [add_comm_monoid N] [module A N]

/-- A polynomial M → N between A-modules is a functorial family
of maps R ⊗[A] M → R ⊗[A] N, for all A-algebras R -/
structure polynomial_map (A : Type u) [comm_semiring A] 
  (M : Type v₁) [add_comm_monoid M] [module A M] 
  (N : Type v₂) [add_comm_monoid N] [module A N] :=
(to_fun : Π (R : Type w) [comm_semiring R], Π [by exactI algebra A R], by exactI 
  (R ⊗[A] M → R ⊗[A] N))
(is_compat : ∀ {R  : Type w} [comm_semiring R] [algebra A R] 
  {R' : Type w} [comm_semiring R'] [algebra A R'] 
  (φ : R →ₐ[A] R'), 
  (φ.to_linear_map.rtensor N) ∘ (to_fun R) = (to_fun R') ∘ (φ.to_linear_map.rtensor M))

namespace polynomial_map 

lemma ext_iff (f g : polynomial_map A M N) : f = g ↔ f.to_fun = g.to_fun := 
begin
  split,
  intro h, rw h,
  intro h, cases f, cases g, congr, exact h,
end

lemma is_compat_apply (f : polynomial_map A M N) 
  (R : Type w) [comm_semiring R] [algebra A R] 
  (R' : Type w) [comm_semiring R'] [algebra A R']
  (φ : R →ₐ[A] R') (x : R ⊗[A] M) : 
  (φ.to_linear_map.rtensor N) ((f.to_fun R) x) = ((f.to_fun R') (φ.to_linear_map.rtensor M x)) :=
by simpa only using congr_fun (f.is_compat φ) x

section module

def add : (polynomial_map A M N) → (polynomial_map A M N) → (polynomial_map A M N)  := λ f g, { 
  to_fun := λ R _, by exactI λ _, by exactI f.to_fun R + g.to_fun R,
  is_compat := λ R _ _ R' _ _ φ,
  begin
    resetI,
    ext, 
    simp only [function.comp_app, pi.add_apply, map_add, is_compat_apply],
  end }

instance has_add : has_add (polynomial_map A M N) := { 
add := add }

@[simp]
lemma add_def (f g : polynomial_map A M N) 
  (R : Type w) [comm_semiring R] [algebra A R] : 
    (f + g).to_fun R = f.to_fun R + g.to_fun R := rfl

@[simp]
lemma add_def_apply (f g : polynomial_map A M N)
  (R : Type w) [comm_semiring R] [algebra A R] (m : R ⊗[A] M): 
    (f + g).to_fun R m = f.to_fun R m + g.to_fun R m := rfl

instance add_comm_monoid : add_comm_monoid (polynomial_map A M N) := {
add := has_add.add, 
add_assoc := λ f g h,
begin rw ext_iff, ext R _ _ m, resetI, simp only [add_def, add_assoc], end,
 zero := {
  to_fun := λ R _, by exactI λ _, by exactI 0, 
  is_compat := λ R _ _ R' _ _ φ, rfl, },
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

def smul : A → (polynomial_map A M N) → (polynomial_map A M N) := λ a f, {
to_fun := λ R _ _ , by exactI a • (f.to_fun R),
is_compat := λ R R' _ _ _ _ φ, 
begin 
  ext m, 
  simp  [is_compat_apply],
end }

instance has_smul : has_smul A (polynomial_map A M N) := 
{ smul := smul } 

lemma smul_def (f : polynomial_map A M N) (a : A) 
  (R : Type w) [comm_semiring R] [algebra A R] :  
  (a • f).to_fun R = a • (f.to_fun R) := rfl 

instance : mul_action A (polynomial_map A M N) := { 
one_smul := λ f, 
begin
  rw ext_iff, ext R _ _ m, resetI, simp only [smul_def, one_smul],
end,
mul_smul := λ a b f,
begin
  rw ext_iff, ext R _ _ m, resetI, simp only [smul_def, mul_smul], 
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

variables {P : Type v₃} [add_comm_monoid P] [module A P]

def comp : polynomial_map A N P → polynomial_map A M N → polynomial_map A M P :=
λ g f, {
to_fun := λ R _, by exactI λ _, by exactI (g.to_fun R).comp (f.to_fun R),
is_compat := λ R R' _ _ _ _ φ, 
begin
  ext m, 
  simp only [is_compat_apply, function.comp_app],
end }

lemma comp_to_fun (f : polynomial_map A M N) (g : polynomial_map A N P) 
  (R : Type w) [comm_semiring R] [algebra A R] : 
  (g.comp f).to_fun R = (g.to_fun R).comp (f.to_fun R) := rfl

lemma comp_apply (f : polynomial_map A M N) (g : polynomial_map A N P)
  (R : Type w) [comm_semiring R] [algebra A R] (m : R ⊗[A] M) : 
  (g.comp f).to_fun R m = (g.to_fun R) (f.to_fun R m) := rfl

variables {Q : Type v₄} [add_comm_monoid Q] [module A Q]

lemma comp_assoc (f : polynomial_map A M N) (g : polynomial_map A N P) (h : polynomial_map A P Q) :
h.comp (g.comp f) = (h.comp g).comp f :=
begin
  rw ext_iff, 
  ext R _ _ m,
  simp only [comp_to_fun],
end

end comp

section constant_map

open_locale tensor_product 

def of_constant (n : N) : polynomial_map A M N := {
to_fun := λ R _ _ m, by exactI tensor_product.tmul A 1 n,
is_compat := λ R _ _ R' _ _ φ , by exactI by simp, 
}

end constant_map

section linear

def of_linear_map (v : M →ₗ[A] N) : polynomial_map A M N := {
to_fun := λ R _ _, by exactI v.base_change R,
is_compat := λ R _ _ _ _ _ φ,
begin
  resetI,
  ext m, 
  simp only [linear_map.base_change_eq_ltensor, ←linear_map.comp_apply, function.comp_app, 
    linear_map.rtensor_comp_ltensor, linear_map.ltensor_comp_rtensor], 
end }

def of_linear_map_to_fun (u : M →ₗ[A] N) 
  (R : Type w) [comm_semiring R] [algebra A R] :
  (of_linear_map u).to_fun R = linear_map.base_change R u := rfl

def of_linear_map_hom :  (M →ₗ[A] N) →ₗ[A] (polynomial_map A M N):= {
to_fun := of_linear_map,
map_add' := λ u v, 
begin
  rw ext_iff, ext R _ _ m,
  simp [add_def, of_linear_map_to_fun],
end,
map_smul' := λ a v, 
begin
  rw ext_iff, ext R _ _ m,
  resetI,
  simp [smul_def, of_linear_map_to_fun], refl,
end }

lemma of_linear_map_hom_apply (v : M →ₗ[A] N) : 
  of_linear_map_hom v = of_linear_map v := rfl 

end linear

section locally_finite

def locfinsupp {ι : Type*} (f : ι → polynomial_map A M N) : Prop :=
  ∀ (R : Type w) [comm_semiring R], by exactI ∀ [algebra A R],
  by exactI ∀ (m : R ⊗[A] M), (function.support (λ i, (f i).to_fun R m)).finite

variables (A M N)
def with_locfinsupp (ι : Type*) : submodule A (ι → polynomial_map A M N) := {
carrier := locfinsupp,
add_mem' := λ a b ha hb, 
begin
  intros R _ _ m, 
  resetI,
  simp only [pi.add_def, polynomial_map.add_def],
  refine set.finite.subset _ (function.support_add _ _),
  rw set.finite_union,
  exact ⟨ha R m, hb R m⟩,
end,
zero_mem' := 
begin
  intros R _ _ m, resetI, 
  convert set.finite_empty , 
  convert function.support_zero ,
end,
smul_mem' := λ a f hf,
begin
  intros R _ _ m, resetI,
  simp only [pi.smul_def, polynomial_map.smul_def],
  refine set.finite.subset (hf R m) (function.support_smul_subset_right a _),
end, }

variables {A M N}
noncomputable def locfinsupp.sum {ι : Type*} (f : ι → polynomial_map A M N) (hf : locfinsupp f) : 
  polynomial_map A M N := 
{ to_fun := λ R _ _ m,begin
  resetI,
  exact (finsupp.of_support_finite _ (hf R m)).sum (λ i m, m),
  end,
  is_compat := λ R _rR _aR R' _rR' _aR' φ,
  begin
    resetI, ext m,
    simp only [function.comp_app, linear_map.map_finsupp_sum],
    rw finsupp.sum,
    suffices : _ ⊆ (hf R m).to_finset, 
    rw finsupp.sum_of_support_subset _ this,
    apply finset.sum_congr rfl,
    intros i hi, 
    simp only [finsupp.of_support_finite_coe, map_sum, is_compat_apply],
    intros i hi, refl,
    intro i, 
    simp only [finsupp.of_support_finite_coe, not_imp_not, finsupp.mem_support_iff, 
      set.finite.mem_to_finset, function.mem_support, ← is_compat_apply],
    intro hi,rw [hi, map_zero],
  end }

lemma finsupp.of_support_finite_support 
  {ι α: Type*} [has_zero α] (f : ι → α) (hf : f.support.finite) :
  (finsupp.of_support_finite f hf).support = hf.to_finset :=
begin
  ext,
  simp only [finsupp.of_support_finite_coe, finsupp.mem_support_iff, set.finite.mem_to_finset, 
    function.mem_support],
end


lemma locfinsupp.sum_eq {ι : Type*} (f : ι → polynomial_map A M N)
  (hf : locfinsupp f) (R : Type w) [comm_semiring R] [algebra A R] (m : R ⊗[A] M): 
  (locfinsupp.sum f hf).to_fun R m = (finsupp.of_support_finite _ (hf R m)).sum (λ i m, m) := rfl

noncomputable def linear_map.locfinsupp.sum {ι : Type*} [decidable_eq ι]: 
  with_locfinsupp A M N ι →ₗ[A] polynomial_map A M N := {
to_fun := λ fhf, locfinsupp.sum fhf.val fhf.prop, 
map_add' := λ fhf ghg, 
begin
  obtain ⟨f, hf⟩ := fhf, obtain ⟨g, hg⟩ := ghg,
  rw ext_iff, ext R _ _ m, resetI,
  simp only [add_mem_class.mk_add_mk, add_def_apply],
  simp [locfinsupp.sum_eq], 
  suffices this_add : _,
  rw finsupp.sum_of_support_subset _ this_add _,
  suffices this_f : _ ⊆ (hf R m).to_finset ∪ (hg R m).to_finset,
  rw finsupp.sum_of_support_subset _ this_f _,
  suffices this_g : _,
  rw finsupp.sum_of_support_subset _ this_g _,
  rw ← finset.sum_add_distrib,  
  apply finset.sum_congr rfl,
  all_goals { try { intros i hi, refl, }, },
  all_goals { simp only [finsupp.of_support_finite_support]},
  { apply finset.subset_union_right, },
  { apply finset.subset_union_left, },
  { intro x, simp only [set.finite.mem_to_finset, function.mem_support, ne.def, finset.mem_union], 
    rw [← not_and_distrib, not_imp_not], 
    intro h, rw [h.1, h.2, add_zero], },
end,
map_smul' := λ a fhf, 
begin
  rw ext_iff, ext R _ _ m, resetI, 
  rw smul_def, simp only [pi.smul_apply],
  simp [locfinsupp.sum_eq], 
  suffices : _,
  rw finsupp.sum_of_support_subset _ this _,
  rw finsupp.smul_sum,
  rw finsupp.sum,
  apply finset.sum_congr rfl,
  { intro i, 
    simp [pi.smul_def, polynomial_map.smul_def, finsupp.of_support_finite_coe], },
  { intros i hi, refl, },
  intro i, 
  simp only [pi.smul_def, polynomial_map.smul_def, finsupp.of_support_finite_coe,
    not_imp_not, finsupp.mem_support_iff],
  intro hi, rw [hi, smul_zero],
end }


end locally_finite
section coefficients

variables {ι : Type*} [fintype ι] [decidable_eq ι]

/-- The coefficients of a `polynomial_map` -/
noncomputable def coeff' {ι : Type*} [fintype ι] [decidable_eq ι] (m : ι → M) (k : ι →₀ ℕ) : 
  polynomial_map A M N  →ₗ[A] N := { 
to_fun := λ f, tensor_product.lid A N ((linear_map.mv_polynomial.coeff k).rtensor N
  (f.to_fun (mv_polynomial ι A)
    (finset.univ.sum (λ i, (mv_polynomial.X i) ⊗ₜ[A] m i)))), 
map_add' := λ f g, by simp only [add_def, pi.add_apply, map_add],
map_smul' := λ a f, by simp only [smul_def, pi.smul_apply, linear_map.map_smulₛₗ, 
  ring_hom.id_apply, linear_equiv.map_smulₛₗ] }


/-- The coefficients of a `polynomial_map` -/
noncomputable def coeff {ι : Type*} [fintype ι] [decidable_eq ι] (m : ι → M) : polynomial_map A M N
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


theorem image_eq_coeff_sum 
  {ι : Type*} [fintype ι] [decidable_eq ι] (m : ι → M) 
  (f : polynomial_map A M N) 
  (R : Type w) [comm_semiring R] [algebra A R] (r : ι → R) :
  f.to_fun R (finset.univ.sum (λ i, r i ⊗ₜ[A] m i)) =
(coeff m f).sum (λ k n, finset.univ.prod (λ i, r i ^ (k i)) ⊗ₜ[A] n) := 
begin
  suffices : f.to_fun (mv_polynomial ι A) (finset.univ.sum (λ i, mv_polynomial.X i ⊗ₜ[A] m i)) = 
    (coeff m f).sum (λ k n, mv_polynomial.monomial k 1 ⊗ₜ n),

  let φ : mv_polynomial ι A →ₐ[A] R := mv_polynomial.aeval r, 
  have that := congr_fun (f.is_compat φ) (finset.univ.sum (λ i, mv_polynomial.X i ⊗ₜ[A] m i)), 
  simp only [function.comp_app, linear_map.map_sum, linear_map.rtensor_tmul, 
    alg_hom.to_linear_map_apply, mv_polynomial.aeval_X] at that, 
  rw ← that, rw this, 
  simp only [finsupp.sum], 
  rw map_sum,  
  apply finset.sum_congr rfl,
  intros k hk, simp only [linear_map.rtensor_tmul, alg_hom.to_linear_map_apply], 
  apply congr_arg2 _ _ rfl,
  simp  [φ, mv_polynomial.aeval_monomial], 

  -- The generic case
  simp only [coeff], dsimp,
  generalize : f.to_fun (mv_polynomial ι A) 
    (finset.univ.sum (λ (i : ι), mv_polynomial.X i ⊗ₜ[A] m i)) = p, 
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
