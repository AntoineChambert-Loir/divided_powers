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

lemma finite_support_coeff {ι : Type u} [fintype ι] (m : ι → M) (f : polynomial_map A M N):
  (λ k, coeff m k f).support.finite ∧ 
  f.to_fun (mv_polynomial ι A) (finset.univ.sum (λ i, (mv_polynomial.X i) ⊗ₜ[A] m i))
  = finsum (λ (k : ι →₀ ℕ), finset.univ.prod (λ i : ι, (mv_polynomial.X i) ^ (k i)) ⊗ₜ (coeff m k f))
 :=
begin
  classical,
  let p : mv_polynomial ι A ⊗ N := (f.to_fun (mv_polynomial ι A) 
      (finset.univ.sum (λ (i : ι), mv_polynomial.X i ⊗ₜ[A] m i))),
  have hcoeff : ∀ k, coeff m k f = (tensor_product.lid A N) ((linear_map.rtensor N (linear_map.mv_polynomial.coeff k)) p),
  { intro k, rw coeff_eq, },
  have hp : p ∈ ⊤ := submodule.mem_top, 
  rw ← tensor_product.span_tmul_eq_top at hp,
  rw submodule.mem_span_set_iff_exists_sum at hp,
  obtain ⟨c, hc⟩ := hp,
  let φ: ↥{t : mv_polynomial ι A ⊗ N | ∃ (m : mv_polynomial ι A) (n : N), m ⊗ₜ[A] n = t} → mv_polynomial ι A := λ t, t.prop.out.some,  
  
  let ν : ↥{t : mv_polynomial ι A ⊗ N | ∃ (m : mv_polynomial ι A) (n : N), m ⊗ₜ[A] n = t} →  N := λ t, t.prop.out.some_spec.some, 
  have h : ∀ t, ↑t = φ t ⊗ₜ[A] ν t := λ t, t.prop.out.some_spec.some_spec.symm, 

  let s' := c.support.bUnion (λ t, (φ t).support),
  
  have p_eq : p = c.sum (λ t a, φ t ⊗ₜ (a • ν t)),
  { rw ← hc,
    apply finsupp.sum_congr,
    intros t ht, rw h t, 
    simp only [tensor_product.tmul_smul], },

  suffices support_ss : function.support (λ (k : ι →₀ ℕ), (coeff m k) f) ⊆ s', 
  have finite_support : (λ k, coeff m k f).support.finite, 
  exact set.finite.subset (s'.finite_to_set) support_ss,

  apply and.intro finite_support,

  { /- change p = _, 
    suffices : function.support (λ (k : ι →₀ ℕ), finset.univ.prod (λ (i : ι), mv_polynomial.X i ^ k i) ⊗ₜ[A] (coeff m k) f) ⊆ finite_support.to_finset, 
    rw finsum_eq_sum_of_support_subset _ this, 
    simp only [hcoeff], dsimp,
    simp_rw p_eq, 
    simp,
  sorry, -/
  sorry, },

  { intro x, rw function.mem_support, intro h, by_contradiction h', apply h,
    simp only [s'] at h',
    rw finset.mem_coe at h', 
    rw finset.mem_bUnion at h', 
    push_neg at h',
    rw hcoeff, 
    rw p_eq,
    simp only [finsupp.sum, map_sum], 
    apply finset.sum_eq_zero,
    intros t ht, simp [linear_map.mv_polynomial.coeff_apply ], 
    specialize h' t ht, simp only [mv_polynomial.mem_support_iff, not_not] at h', 
    simp only [h', zero_smul, smul_zero], },

  

end

example {ι : Type u} [fintype ι] (r : ι → R) (m : ι → M) (f : polynomial_map A M N) :
f.to_fun R (finset.univ.sum (λ i, r i ⊗ₜ[A] m i)) =
finsum (λ (k : ι →₀ ℕ), finset.univ.prod (λ i : ι, (r i) ^ (k i)) ⊗ₜ (coeff m k f)) :=
begin
  suffices : f.to_fun (mv_polynomial ι A) (finset.univ.sum (λ i, (mv_polynomial.X i) ⊗ₜ[A] m i))
  = finsum (λ (k : ι →₀ ℕ), finset.univ.prod (λ i : ι, (mv_polynomial.X i) ^ (k i)) ⊗ₜ (coeff m k f)),
  sorry,
  sorry,

end



end coefficients


-- TODO : go on…

end polynomial_map


