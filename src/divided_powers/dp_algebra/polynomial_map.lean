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

/- def zoo {σ : Type*} : mv_polynomial σ A ⊗[A] N ≃ₗ[A] ((σ →₀ ℕ) →₀ N) := {
to_fun := sorry,
map_add' := sorry,
map_smul' := sorry,
inv_fun := sorry,
left_inv := sorry,
right_inv := sorry,
}
 -/

example {α : Type*} : α → plift α := plift.up

/- 
def finset.plift {α : Type*} : finset α → finset (plift α) := 
λ s, finset.map ⟨plift.up, plift.up_injective⟩ s
-/

lemma support_finite {ι : Type*} [fintype ι] (p : mv_polynomial ι A ⊗[A] N) :
  (function.support (λ (k : ι →₀ ℕ),
       mv_polynomial.monomial k (1 : A) ⊗ₜ[A]
         (tensor_product.lid A N) ((linear_map.rtensor N (linear_map.mv_polynomial.coeff k)) p))).finite := 
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

  { simp only [set.finite.mem_to_finset, function.mem_support, linear_map.mv_polynomial.coeff_apply, not_not], 
    simp_rw mv_polynomial.coeff_monomial,
    rw finset.sum_eq_single k, exact id,

    intro d,
    simp only [function.mem_support, ne.def, finset.mem_coe, mv_polynomial.mem_support_iff],
    intros hd hdk, rw [if_neg hdk, zero_smul], 

    intro hk', exfalso, exact hk' hk, }, },
  { -- case add 
    simp only [map_add, tensor_product.tmul_add], 
    conv_lhs {rw [hf, hg], },
    convert finset.sum_add_distrib_of_support_subset _ _ _ _ _,
    apply_instance,
    simp only [set.finite.coe_to_finset],
    refine set.subset.refl _,
    simp only [set.finite.coe_to_finset],
    refine set.subset.refl _,
    simp only [set.finite.coe_to_finset],
    refine set.subset.refl _, }
end

/- ATTEMPT TO DO IT USING finsupp.sum

lemma mv_polynomial_tmul_eq' {ι : Type*} [fintype ι] (p : mv_polynomial ι A ⊗[A] N) :
   p = (support_finite p).to_finset.sum
    (λ (k : ι →₀ ℕ), mv_polynomial.monomial k (1 : A) ⊗ₜ[A]
      (tensor_product.lid A N) ((linear_map.rtensor N (linear_map.mv_polynomial.coeff k)) p)) :=
begin
  have H : ∀ (p : mv_polynomial ι A ⊗[A] N) (k : ι →₀ ℕ),
    finsupp.of_support_finite _ (support_finite p) k  = 
    (mv_polynomial.monomial k) 1 ⊗ₜ[A] (tensor_product.lid A N) ((linear_map.rtensor N (linear_map.mv_polynomial.coeff k)) p),
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

example {ι : Type u} [fintype ι] (m : ι → M) (f : polynomial_map A M N) : 
  (function.support (λ k, (coeff m k) f)).finite :=
begin

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


