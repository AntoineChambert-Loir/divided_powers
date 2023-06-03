import divided_powers.dp_algebra.init
import divided_powers.dp_algebra.graded
import ring_theory.power_series.basic
import ...for_mathlib.ring_theory.submodule_mem

/-! Polynomial laws on modules

Reference : N. Roby, Lois polynômes et lois formelles en théorie des modules… 

-/


-- open algebra.tensor_product


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

/-- The coefficients of a `polynomial_map` -/
noncomputable def coeff {ι : Type u} [fintype ι] (m : ι → M) (k : ι →₀ ℕ) : 
  polynomial_map A M N  →ₗ[A] N := { 
to_fun := λ f, tensor_product.lid A N ((linear_map.mv_polynomial.coeff k).rtensor N
  (f.to_fun (mv_polynomial ι A)
    (finset.univ.sum (λ i, (mv_polynomial.X i) ⊗ₜ[A] m i)))), 
map_add' := λ f g, by simp only [add_def, pi.add_apply, map_add],
map_smul' := λ a f, by simp only [smul_def, pi.smul_apply, linear_map.map_smulₛₗ, ring_hom.id_apply, linear_equiv.map_smulₛₗ] }

lemma coeff_eq  {ι : Type u} [fintype ι] (m : ι → M) (k : ι →₀ ℕ) 
  (f : polynomial_map A M N) :
  coeff m k f = (tensor_product.lid A N)
  ((linear_map.rtensor N (linear_map.mv_polynomial.coeff k))
     (f.to_fun (mv_polynomial ι A) 
      (finset.univ.sum (λ (i : ι), mv_polynomial.X i ⊗ₜ[A] m i)))) := 
by simp only [coeff, linear_map.coe_mk]



example {α : Type*} : α → plift α := plift.up

/- 
def finset.plift {α : Type*} : finset α → finset (plift α) := 
λ s, finset.map ⟨plift.up, plift.up_injective⟩ s
-/

lemma support_finite {ι : Type*} [fintype ι] (p : mv_polynomial ι A ⊗[A] N) :
  (function.support (λ (k : ι →₀ ℕ),
--       mv_polynomial.monomial k (1 : A) ⊗ₜ[A]
         (tensor_product.lid A N) 
         ((linear_map.rtensor N (linear_map.mv_polynomial.coeff k)) p))).finite := 
begin
  classical,
  induction p using tensor_product.induction_on with f n f g hf hg,
  -- case C0
  simp only [map_zero, function.support_zero, set.finite_empty], 

  -- case C1,
  { apply set.finite.subset (mv_polynomial.support f).finite_to_set, 
    intro k,
    simp only [linear_map.mv_polynomial.coeff_apply, linear_map.rtensor_tmul, 
      function.mem_support, ne.def, finset.mem_coe, mv_polynomial.mem_support_iff,
      not_imp_not],
    intro hk, rw hk, simp only [tensor_product.zero_tmul], 
    simp only [map_zero], },

  -- case Cp
  { simp only [map_add], 
    refine set.finite.subset (set.finite.union hf hg) (function.support_add _ _), },
end

lemma support_finite' {ι : Type*} [fintype ι] (p : mv_polynomial ι A ⊗[A] N) :
  (function.support (λ (k : ι →₀ ℕ),
    mv_polynomial.monomial k (1 : A) ⊗ₜ[A]
      (tensor_product.lid A N) 
        ((linear_map.rtensor N (linear_map.mv_polynomial.coeff k)) p))).finite := 
begin
  classical,
  induction p using tensor_product.induction_on with f n f g hf hg,
  -- case C0
  simp only [map_zero, tensor_product.tmul_zero, function.support_zero, set.finite_empty],

  -- case C1,
  { apply set.finite.subset (mv_polynomial.support f).finite_to_set, 
    intro k,
    simp only [linear_map.rtensor_tmul, tensor_product.lid_tmul, tensor_product.tmul_smul, function.mem_support, ne.def,
    finset.mem_coe, mv_polynomial.mem_support_iff, not_imp_not, linear_map.mv_polynomial.coeff_apply],
    intro hk, rw hk, rw zero_smul,},

  -- case Cp
  { simp only [map_add, tensor_product.tmul_add],
    refine set.finite.subset (set.finite.union hf hg) (function.support_add _ _), },
end

lemma finset.sum_eq_of_suport_subset {α β : Type*} [decidable_eq α] [add_comm_monoid β] {f : α → β} {s : finset α} (hs : f.support ⊆ s) (t : finset α) (hst : s ⊆ t) : t.sum f = s.sum f :=
begin
  rw ← finset.sum_sdiff hst, 
  convert zero_add _, 
  apply finset.sum_eq_zero,
  intros x hx, simp only [finset.mem_sdiff] at hx,
  rw ← function.nmem_support, intro hx', apply hx.2, apply hs, exact hx',
end


lemma finset.sum_add_distrib_of_support_subset {α β : Type*} [decidable_eq α] [add_comm_monoid β] (f g : α → β)
  {s t u : finset α} (hf : f.support ⊆ s) (hg : g.support ⊆ t) (hk : (f + g).support ⊆ u) :
  s.sum f + t.sum g = u.sum (f+g) :=
begin
  rw ← finset.sum_eq_of_suport_subset hf (s ∪ t ∪ u),
  rw ← finset.sum_eq_of_suport_subset hg (s ∪ t ∪ u),
  rw ← finset.sum_eq_of_suport_subset hk (s ∪ t ∪ u),
  rw ← finset.sum_add_distrib,
  refl,
  refine (s ∪ t).subset_union_right u,
  apply subset_trans (s.subset_union_right t) ((s ∪ t).subset_union_left u),
  apply subset_trans (s.subset_union_left t) ((s ∪ t).subset_union_left u),
end


lemma mv_polynomial_tmul_eq {ι : Type*} [fintype ι] (p : mv_polynomial ι A ⊗[A] N) :
  p = (support_finite p).to_finset.sum
    (λ (k : ι →₀ ℕ), mv_polynomial.monomial k (1 : A) ⊗ₜ[A]
      (tensor_product.lid A N) ((linear_map.rtensor N (linear_map.mv_polynomial.coeff k)) p)) :=
begin
  classical,
  induction p using tensor_product.induction_on with f n f g hf hg,
  -- case C0
  simp only [map_zero, tensor_product.tmul_zero, finset.sum_const_zero], 

  {  -- case C1 
    simp only [linear_map.rtensor_tmul, tensor_product.lid_tmul, tensor_product.tmul_smul],

  rw f.as_sum,
  simp_rw map_sum, simp_rw finset.sum_smul, 
  rw finset.sum_comm,
  simp_rw tensor_product.sum_tmul,
  apply finset.sum_congr rfl,
  intros k hk, 
  rw finset.sum_eq_single k,
  simp only [linear_map.mv_polynomial.coeff_apply, mv_polynomial.coeff_monomial, eq_self_iff_true, if_true],
  apply congr_arg2 _ _ rfl,
  simp only [mv_polynomial.monomial_eq, mv_polynomial.C_eq_smul_one, algebra.smul_mul_assoc, one_smul],


  { intros d hd hdk,  
    simp only [linear_map.mv_polynomial.coeff_apply, mv_polynomial.coeff_monomial], 
    rw if_neg (ne_comm.mp hdk), simp only [zero_smul], },

  { simp only [set.finite.mem_to_finset, function.mem_support, 
      linear_map.mv_polynomial.coeff_apply, not_not], 
    simp_rw mv_polynomial.coeff_monomial,
    rw finset.sum_eq_single k, 
    simp only [eq_self_iff_true, if_true],
    intro hk', 
    rw ← tensor_product.tmul_smul, 
    -- rw ← tensor_product.lid_tmul, 
    rw hk', 
    simp only [map_zero, tensor_product.tmul_zero],

    intro d,
    simp only [function.mem_support, ne.def, finset.mem_coe, mv_polynomial.mem_support_iff],
    intros hd hdk, rw [if_neg hdk, zero_smul], 

    intro hk', exfalso, exact hk' hk, }, },
  { -- case add 
    simp only [map_add, tensor_product.tmul_add], 
    conv_lhs {rw [hf, hg], },
    convert finset.sum_add_distrib_of_support_subset _ _ _ _ _,
    apply_instance,
    all_goals { simp only [set.finite.coe_to_finset],
    intro k, simp only [function.mem_support, ne.def, not_imp_not],  
    intro hk, simp only [pi.add_apply, ← tensor_product.tmul_add, 
      hk, map_zero, tensor_product.tmul_zero], }, },
end

-- ATTEMPT TO DO IT USING finsupp.sum
example {ι : Type*} [fintype ι] (p : mv_polynomial ι A ⊗[A] N) : Prop :=
begin
let hp := mv_polynomial_tmul_eq p, 
let f := finsupp.of_support_finite _ (support_finite p),
have hf : f.support = (support_finite p).to_finset := rfl,
rw ← hf at hp, 
let np := f.sum (λ k n, (mv_polynomial.monomial k 1 : mv_polynomial ι A) ⊗ₜ[A] n), 
end

lemma mv_polynomial_tmul_eq' {ι : Type*} [fintype ι] (p : mv_polynomial ι A ⊗[A] N) :
   p = (finsupp.of_support_finite _ (support_finite p)).sum
    (λ k n, (mv_polynomial.monomial k 1 : mv_polynomial ι A) ⊗ₜ[A] n) :=
begin

  sorry,
  /- have H : ∀ (p : mv_polynomial ι A ⊗[A] N) (k : ι →₀ ℕ),
    finsupp.of_support_finite _ (support_finite p) k  = 
    (mv_polynomial.monomial k) 1 ⊗ₜ[A] (tensor_product.lid A N) ((linear_map.rtensor N (linear_map.mv_polynomial.coeff k)) p),-/
  intros p k, refl,

  let f := finsupp.of_support_finite _ (support_finite p),
  change p = f.support.sum _, 
  suffices : p = f.sum (λ k a,a),
  simp only [finsupp.sum] at this,
  exact this, 

  revert f,
  induction p using tensor_product.induction_on with f n f g hf hg,
  { intro f,
    suffices : f = 0,
    rw this, simp only [finsupp.sum_zero_index],
    ext, simp [f, H], refl, },
  { intro φ, simp only [φ, finsupp.sum, linear_map.rtensor_tmul, tensor_product.lid_tmul, tensor_product.tmul_smul], 

  
  
  sorry },
  { sorry },
end
 -/


example {ι : Type u} [fintype ι] (f : polynomial_map A M N) (m : ι → M) : 
  (coeff m k) f =
begin

  sorry 
end
example {ι : Type u} [fintype ι] (f : polynomial_map A M N) (m : ι → M) : 
  (function.support (λ k, (coeff m k) f)).finite :=
begin
 let p := (f.to_fun (mv_polynomial ι A) 
      (finset.univ.sum (λ (i : ι), mv_polynomial.X i ⊗ₜ[A] m i))),
  let hp := support_finite p,  
  sorry 
end


example {ι : Type u} [fintype ι] (r : ι → R) (m : ι → M) (f : polynomial_map A M N) :
f.to_fun R (finset.univ.sum (λ i, r i ⊗ₜ[A] m i)) =
finsum (λ (k : ι →₀ ℕ), finset.univ.prod (λ i : ι, (r i) ^ (k i)) ⊗ₜ (coeff m k f)) :=
begin
  suffices : f.to_fun (mv_polynomial ι A) (finset.univ.sum (λ i, mv_polynomial.X i ⊗ₜ[A] m i)) = finsum (λ (k : ι →₀ ℕ), mv_polynomial.monomial k 1 ⊗ₜ (coeff m k f)),

  let φ : mv_polynomial ι A →ₐ[A] R := mv_polynomial.aeval r, 
  have that := congr_fun (f.is_compat φ) (finset.univ.sum (λ i, mv_polynomial.X i ⊗ₜ[A] m i)), 
  simp only [function.comp_app, linear_map.map_sum, linear_map.rtensor_tmul, alg_hom.to_linear_map_apply, mv_polynomial.aeval_X] at that, 
  rw ← that, rw this,
   
  have : ∀ (i : ι), r i = φ (mv_polynomial.X i), intro i, 
  simp only [φ, mv_polynomial.aeval_X], 

  sorry,
  sorry,

end



end coefficients


-- TODO : go on…

end polynomial_map


