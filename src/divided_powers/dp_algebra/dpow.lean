
import divided_powers.dp_algebra.init
import divided_powers.dp_algebra.graded
import divided_powers.rat_algebra
import divided_powers.sub_pd_ideal
import divided_powers.ideal_add
import divided_powers.dp_algebra.roby_lemma5
import divided_powers.dp_algebra.roby_lemma9


-- import ring_theory.tensor_product
import ring_theory.mv_polynomial.basic
import for_mathlib.ring_theory.ideal

noncomputable theory

universes u v v₁ v₂ w 

section 


variables (R M : Type u) [comm_ring R] [add_comm_group M] [module R M]

variables (x : M) (n : ℕ)

open finset mv_polynomial ideal.quotient 
-- triv_sq_zero_ext 
open ideal 
-- direct_sum 
open ring_quot

namespace divided_power_algebra

open divided_power_algebra

/-- Lemma 2 of Roby 65. -/
lemma on_dp_algebra_unique (h h' : divided_powers (aug_ideal R M))
  (h1 : ∀ (n : ℕ) (x : M), h.dpow n (ι R x) = dp R n x)
  (h1' : ∀ (n : ℕ) (x : M), h'.dpow n (ι R x) = dp R n x) :
h = h' := 
begin
  apply divided_powers.dp_uniqueness_self h' h (aug_ideal_eq_span R M),
  rintros n f ⟨q, m, hq : 0 < q, _, rfl⟩, 
  nth_rewrite 0 [← h1' q m],
  rw [← h1 q m, h.dpow_comp n (ne_of_gt hq) (ι_mem_aug_ideal R M m), 
    h'.dpow_comp n (ne_of_gt hq) (ι_mem_aug_ideal R M m), 
    h1 _ m,  h1' _ m], 
end


def cond_δ (R : Type u) [comm_ring R] (M : Type u) [add_comm_group M] [module R M] : Prop :=
∃ (h : divided_powers (aug_ideal R M)), ∀ (n : ℕ) (x : M), h.dpow n (ι R x) = dp R n x 

def cond_D (R : Type u) [comm_ring R] : Prop :=
∀ (M : Type u) [add_comm_group M], by exactI ∀ [module R M], by exactI cond_δ R M 


end divided_power_algebra

end 

section roby
/- Formalization of Roby 1965, section 8 -/


open finset mv_polynomial ideal.quotient 
-- triv_sq_zero_ext 
open ideal 
-- direct_sum 
open ring_quot
open divided_powers

namespace divided_power_algebra

open divided_power_algebra

section tensor_product

open_locale tensor_product

variables (A R S : Type u) [comm_ring A] [comm_ring R] [algebra A R] [comm_ring S] [algebra A S] 
  {I : ideal R} {J : ideal S} (hI : divided_powers I) (hJ : divided_powers J)

def i_1 : R →ₐ R ⊗[A] S := algebra.tensor_product.include_left

def i_2 : S →ₐ R ⊗[A] S := algebra.tensor_product.include_right


variables {R S} (I J)
def K : ideal (R ⊗[A] S) := (I.map (i_1 A R S)) ⊔ (J.map (i_2 A R S))

variables {I J}
/- Lemma 1 : uniqueness of the dp structure on R ⊗ S for I + J -/
lemma on_tensor_product_unique (hK hK' : divided_powers (K A I J))
  (hIK : is_pd_morphism hI hK (i_1 A R S)) (hIK' : is_pd_morphism hI hK' (i_1 A R S))
  (hJK : is_pd_morphism hJ hK (i_2 A R S)) (hJK' : is_pd_morphism hJ hK' (i_2 A R S)) : 
  hK = hK' :=
begin
  apply eq_of_eq_on_ideal,
  intros n x hx,
  suffices : x ∈ pd_equalizer hK hK',  
  { exact ((mem_pd_equalizer_iff _ _).mp this).2 n,},
  suffices h_ss : K A I J ≤ pd_equalizer hK hK',
  { exact h_ss hx },
  dsimp only [K], 
  rw sup_le_iff,
  split,
  apply le_equalizer_of_pd_morphism hI (i_1 A R S).to_ring_hom
    le_sup_left hK hK' hIK hIK',
  apply le_equalizer_of_pd_morphism hJ (i_2 A R S).to_ring_hom
    le_sup_right hK hK' hJK hJK',
end

def cond_τ (A : Type u) [comm_ring A] {R : Type u} [comm_ring R] [algebra A R] 
  {S : Type u} [comm_ring S] [algebra A S] 
  {I : ideal R} {J : ideal S} (hI : divided_powers I) (hJ : divided_powers J) : Prop :=
∃ hK : divided_powers (K A I J), 
  is_pd_morphism hI hK (i_1 A R S) ∧ is_pd_morphism hJ hK (i_2 A R S)

def cond_T (A : Type u) [comm_ring A] : Prop := 
∀ (R : Type u)[comm_ring R] (S : Type u) [comm_ring S], 
by exactI ∀ [algebra A R] [algebra A S],
by exactI ∀ {I : ideal R} {J : ideal S} (hI : divided_powers I) (hJ : divided_powers J),
cond_τ A hI hJ

end tensor_product

section free

-- hR_free, hS_free are not used for the def (they might be needed at lemmas about cond_T_free)

def cond_T_free (A : Type u) [comm_ring A] : Prop := 
∀ (R : Type u) [comm_ring R] (S : Type u) [comm_ring S], 
by exactI ∀ [algebra A R] [algebra A S],
by exactI ∀ (hR_free : module.free A R) (hS_free : module.free A S),
by exactI ∀ {I : ideal R} {J : ideal S} (hI : divided_powers I) (hJ : divided_powers J),
cond_τ A hI hJ

/- def cond_Q (A R : Type*) [comm_ring A] [comm_ring R] /- [algebra A R] not used -/
  {I : ideal R} (hI : divided_powers I) : Prop := 
∃ (T : Type*) [comm_ring T], by exactI ∃ [algebra A T], by exactI ∃ [module.free A T]
  {J : ideal T} (hJ : divided_powers J) (f : pd_morphism hI hJ), 
  function.surjective f.to_ring_hom
 -/

def cond_Q (A : Type u) [comm_ring A] : Prop := 
∀ (R : Type u) [comm_ring R],
by exactI ∀ [algebra A R] (I : ideal R) (hI : divided_powers I),
∃ (T : Type u) [comm_ring T], 
  by exactI ∃ [algebra A T], 
  by exactI ∃ [module.free A T] 
  (f : T →ₐ[A] R)  
  (J : ideal T) (hJ : divided_powers J) (hf : is_pd_morphism hJ hI f),
  function.surjective f
  
end free

section Proofs

variables {R : Type u} [comm_ring R] 

open divided_power_algebra

open_locale tensor_product

/- 
variables {M : Type*} [add_comm_group M] [module R M] (h : divided_powers (aug_ideal R M))
(hh : ∀ (x : M) (n : ℕ), h.dpow n (ι R x) = dp R n x)
include M  h -/

-- Roby, lemma 3
lemma cond_D_uniqueness {M : Type u} [add_comm_group M] [module R M] 
  (h : divided_powers (aug_ideal R M))
  (hh : ∀ (n : ℕ) (x : M), h.dpow n (ι R x) = dp R n x)
  {S : Type*} [comm_ring S]
  [algebra R S] {J : ideal S} (hJ : divided_powers J) (f : M →ₗ[R] S) 
  (hf : ∀ m, f m ∈ J) :
  is_pd_morphism h hJ (divided_power_algebra.lift R M hJ f hf)  := 
begin
  split,
  { rw aug_ideal_eq_span, 
    rw ideal.map_span,
    rw ideal.span_le,
    intro s,
    rintro ⟨a,⟨n, m, hn : 0 < n, hm, rfl⟩, rfl⟩,
    simp only [alg_hom.coe_to_ring_hom, set_like.mem_coe],
    rw lift_dp_eq,
    apply hJ.dpow_mem (ne_of_gt hn) (hf m), },
  { intros n a ha,
--    simp only [alg_hom.coe_to_ring_hom], 
    apply symm,
    rw (dp_uniqueness h hJ (lift R M hJ f hf) (aug_ideal_eq_span R M) _ _ ) n a ha,
    { rintros a ⟨q, m, hq : 0 < q, hm, rfl⟩,
      simp only [alg_hom.coe_to_ring_hom, lift_dp_eq],
      exact hJ.dpow_mem (ne_of_gt hq) (hf m), },
    { rintros n a ⟨q, m, hq : 0 < q, hm, rfl⟩,
      simp only [alg_hom.coe_to_ring_hom, lift_dp_eq], 
      rw hJ.dpow_comp n (ne_of_gt hq) (hf m),
      rw ← hh q m, 
      rw h.dpow_comp n (ne_of_gt hq) (ι_mem_aug_ideal R M m),
      simp only [_root_.map_mul, map_nat_cast],
      apply congr_arg2 _ rfl,
      rw hh, rw lift_dp_eq, }, },
end



-- Roby, lemma 4
lemma T_free_and_D_to_Q (A : Type u) [comm_ring A] :
  cond_T_free A → cond_D A → cond_Q A :=
begin
  intros hT_free hD, 
  simp only [cond_Q, cond_D, cond_T_free] at *,
  intros S _ _ I hI, 
  resetI,
  let R := mv_polynomial S A,
  -- R = A[S] →ₐ[A] S, morphisme de A-algèbres
  letI : algebra R S := ring_hom.to_algebra
    (mv_polynomial.aeval id).to_ring_hom,
  have mapRS : algebra_map R S = (mv_polynomial.aeval id).to_ring_hom := 
  ring_hom.algebra_map_to_algebra _,
  resetI,
  haveI : is_scalar_tower A R S := {
  smul_assoc := λ a r s, 
  begin 
    simp only [algebra.smul_def, mapRS], 
    simp only [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom, _root_.map_mul, 
      alg_hom.commutes],
    rw ← mul_assoc, 
  end, },

  classical,
  let hR := divided_powers_bot R, 
  let M := (↥I →₀ A),
  let f : M →ₗ[A] S := {
  to_fun := λ p, finsupp.sum p (λ (i : I) (r : A), r • (i : S)),
  map_add' := λ p q, 
  begin
    rw finsupp.sum_add_index, 
    rintros ⟨a, ha⟩ ha', rw zero_smul, 
    rintros ⟨a, ha⟩ ha' r r', rw add_smul,
  end,
  map_smul' := λ r p, 
  begin
    rw [ring_hom.id_apply, finsupp.smul_sum, finsupp.sum_smul_index], 
    apply congr_arg2 _ rfl,
    ext i q, rw ← smul_assoc, congr,
    intro i, rw zero_smul, 
  end, },
  have hf : ∀ p, f p ∈ I,
  { intro p, simp only [f, finsupp.sum], 
    apply ideal.sum_mem, 
    rintro ⟨a, ha⟩ ha', 
    simp only [subtype.coe_mk],
    rw ← algebra_map_smul S,
    rw smul_eq_mul, 
    exact I.mul_mem_left _ ha,
    apply_instance, apply_instance, },

  obtain ⟨hM, hM_eq⟩ := hD M,
  haveI hdpM_free : module.free A (divided_power_algebra A M),
  sorry,
  haveI hR_free : module.free A R :=
  module.free.of_basis (mv_polynomial.basis_monomials _ _),

  use R ⊗[A] (divided_power_algebra A M),
  use (by apply_instance),
  use (by apply_instance),
  split, 
  apply_instance, -- tensor product of free modules is free
  use algebra.tensor_product.product_map (is_scalar_tower.to_alg_hom A R S) 
    (divided_power_algebra.lift A M hI f hf),

  suffices : cond_τ A hR hM,
  obtain ⟨hK, hR_pd, hM_pd⟩ := this, 
  use K A ⊥ (aug_ideal A M),
  use hK,
  split,
  { suffices hmap_le : _,
    apply and.intro hmap_le, -- split,
    { intros n a ha,
      let ha' := id ha,
      simp only [K, ideal.map_bot, bot_sup_eq] at ha,
      simp only [is_pd_morphism] at hM_pd,
      apply dp_uniqueness hK hI, 
      simp only [K, ideal.map_bot, bot_sup_eq], rw ideal.map, 
      { rintros s ⟨a, ha, rfl⟩,
        simp only [i_2, algebra.tensor_product.include_right_apply, 
          alg_hom.coe_to_ring_hom, algebra.tensor_product.product_map_apply_tmul, 
          map_one, one_mul],
        apply lift_mem_of_mem_aug_ideal, 
        exact ha, },
        
      { rintros n s ⟨a, ha, rfl⟩,
        simp only [set_like.mem_coe] at ha,
        have := hM_pd.2 n a ha,
        simp only [alg_hom.coe_to_ring_hom] at this,
        rw this,
        simp only [i_2, algebra.tensor_product.include_right_apply, 
          alg_hom.coe_to_ring_hom, algebra.tensor_product.product_map_apply_tmul, 
          map_one, one_mul],

        apply symm,
        apply dp_uniqueness hM hI,
        rw aug_ideal_eq_span,
        { rintros s ⟨q, m, hq, hm, rfl⟩,
          change (lift A M hI f hf) (dp A q m) ∈ I, 
          rw lift_dp_eq, 
          exact hI.dpow_mem (ne_of_gt hq) (hf m), },
        { rintros n s ⟨q, m, hq, hm, rfl⟩,
          change (lift A M hI f hf) (hM.dpow n (dp A q m)) = 
            hI.dpow n ((lift A M hI f hf) (dp A q m)),
          rw [lift_dp_eq, ← hM_eq, hM.dpow_comp n (ne_of_gt hq), hM_eq,
            hI.dpow_comp n (ne_of_gt hq) (hf m)],
          simp only [← nsmul_eq_mul], rw map_nsmul,
          rw lift_dp_eq,
          exact ι_mem_aug_ideal A M m, },
        exact ha, },
      exact ha' },
    { rw [K, ideal.map_bot, bot_sup_eq],
      simp only [ideal.map_le_iff_le_comap],
      intros x hx,
      simp only [ideal.mem_comap, i_2, algebra.tensor_product.include_right_apply, alg_hom.coe_to_ring_hom,
  algebra.tensor_product.product_map_apply_tmul, map_one, one_mul],
      apply lift_mem_of_mem_aug_ideal,
      exact hx, }, },
  { rw ← (algebra.range_top_iff_surjective _),
    rw algebra.tensor_product.product_map_range, 
    suffices : (is_scalar_tower.to_alg_hom A R S).range = ⊤,
    rw [this, top_sup_eq],
    rw algebra.range_top_iff_surjective,
    intro s, use mv_polynomial.X s, 
    simp only [mapRS, is_scalar_tower.coe_to_alg_hom', alg_hom.to_ring_hom_eq_coe, 
      alg_hom.coe_to_ring_hom, aeval_X, id.def], },
  
  { -- cond_τ 
    apply hT_free,
    exact hR_free,
    exact hdpM_free, }, 
end

example {A : Type*} [comm_ring A] (a : A) (n : ℕ) : n • a = n * a :=
begin
refine nsmul_eq_mul n a,
end

.

/- In Roby, all PD-algebras A considered are of the form A₀ ⊕ A₊, 
where A₊ is the PD-ideal. In other words, the PD-ideal is an augmentation ideal.
Moreover, PD-morphisms map A₀ to B₀ and A₊ to B₊,
so that their kernel is a direct sum K₀ ⊕ K₊ 

Roby states this as a sory of `pre-graded algebras`, 
which correspond to graded algebras by the monoid {⊥, ⊤} with carrier set (fin 0)
or fin 2 (with multiplication)

I am not sure that the proofs can avoid this hypothesis, 
especially for tensor products (alas…).

The question is about the formalism to use. 
With `is_augmentation_ideal A I`, and `is_augmentation_ideal B J`,
we need to state out the assumption that `f : A →+* B` is homogeneous.

It maps A₊ to B₊ by definition of a PD-morphism,
but A₀ and B₀ are not canonical. 
The definition of an augmentation ideal is the existence of
a section A/A₊ →+* A, whose image is A₀. 
Write r₀ for the composition A →+* A/A₊ →+* A₀.
The assumptions are : A₊ ≤ r₀.ker, r₀.range ⊓ A₊ = 0

If f is homogeneous (for the two chosen maps r₀), then r₀ (f a) = f (r₀ a)
and f.ker = (f.ker ⊓ A₀) ⊕ (f.ker ⊓ A₊)
or map f I is an augmentation ideal in f.range 

This looks less convenient than imposing the graded structure

In lemma 6, we have two surjective algebra morphisms
 f : R →+* R',  g : S →+* S'
and we consider the induced surjective morphism fg : R ⊗ S →+* R' ⊗ S'
R has a PD-ideal I,  R' has a PD-ideal I',
S has a PD-ideal J,  S' has a PD-ideal J'
with assumptions that I' = map f I and J' = map g J,
with quotient PD structures

Lemma 5 has proved that  fg.ker = (f.ker ⊗ 1) ⊔ (1 ⊗ g.ker)

In the end, Roby applies its proposition 4 which we
apparently haven't formalized and make use of yet another definition, 
namely of a `divised ideal` : 
Up to the homogeneous condition, this is exactly that `K ⊓ I` is a sub-pd-ideal.
The proof of proposition goes by using that 
`ideal.span s ⊓ I = ideal.span s ⊓ I`
if `s` is made of homogeneous elements. 

So we assume the `roby` condition in the statement, in the hope
that will be possible to prove it each time we apply cond_τ_rel
-/

-- Should be elsewhere, and is probably already there…
lemma algebra.tensor_product.map_surjective 
  (A : Type*) [comm_ring A] {R S R' S' : Type*} 
  [comm_ring R] [comm_ring S] [comm_ring R'] [comm_ring S']
  [algebra A R] [algebra A S] [algebra A R'] [algebra A S'] 
  (f : R →ₐ[A] R') (hf : function.surjective f) 
  (g : S →ₐ[A] S') (hg : function.surjective g) :
  function.surjective (algebra.tensor_product.map f g) :=
begin
  rw ← set.range_iff_surjective,
  rw ← alg_hom.coe_range,
  rw set.eq_univ_iff_forall, intro x,
  induction x using tensor_product.induction_on with x y x y hx hy, 
  use 0, rw map_zero,
  obtain ⟨x, hx, rfl⟩ := hf x, 
  obtain ⟨y, hy, rfl⟩ := hg y,
  use x ⊗ₜy,refl, 
  simp only [set_like.mem_coe] at hx hy ⊢,
  exact subalgebra.add_mem _ hx hy,
end

-- Roby, lemma 6
lemma cond_τ_rel (A : Type*) [comm_ring A] {R S R' S' : Type*} 
  [comm_ring R] [comm_ring S] [comm_ring R'] [comm_ring S']
  [algebra A R] [algebra A S] [algebra A R'] [algebra A S'] 
  (f : R →ₐ[A] R') (hf : function.surjective f) 
  {I : ideal R} (hI : divided_powers I) {I' : ideal R'} (hI' : divided_powers I') 
  (hf' : is_pd_morphism hI hI' f) (hI'I : I' = I.map f)
  (g : S →ₐ[A] S') (hg : function.surjective g)
  {J : ideal S} (hJ : divided_powers J) {J' : ideal S'} (hJ' : divided_powers J') 
  (hg' : is_pd_morphism hJ hJ' g) (hJ'J : J' = J.map g)
  (roby : ring_hom.ker (algebra.tensor_product.map f g) ⊓ K A I J = 
    map (algebra.tensor_product.include_left : R →ₐ[A] R ⊗[A] S) (ring_hom.ker f ⊓ I) 
    ⊔ map (algebra.tensor_product.include_right : S →ₐ[A] R ⊗[A] S) (ring_hom.ker g ⊓ J))
  (hRS : cond_τ A hI hJ) : cond_τ A hI' hJ' :=
begin
  obtain ⟨hK, hK_pd⟩ := hRS, 
  simp only [cond_τ],
  let fg := (algebra.tensor_product.map f g),
  let k_fg := algebra.tensor_product.ker_tens hf hg, 
  have s_fg : function.surjective fg.to_ring_hom, 
  { exact algebra.tensor_product.map_surjective A f hf g hg, },
  suffices hK_map: K A I' J' = (K A I J).map fg,
  rw hK_map,
  suffices hK'_pd : is_sub_pd_ideal hK (ring_hom.ker fg.to_ring_hom ⊓ K A I J), 
  let hK' := divided_powers.quotient.of_surjective.divided_powers hK s_fg hK'_pd,
  use hK',
  split,
  { -- hI'.is_pd_morphism hK' ↑(i_1 A R' S')
    split, 
    { rw ← hK_map,
      rw ideal.map_le_iff_le_comap, intros a' ha',
      rw ideal.mem_comap,
      apply ideal.mem_sup_left, apply ideal.mem_map_of_mem, exact ha', },
    { intros n a' ha', 
      suffices ha : a' ∈ f '' I, obtain ⟨a, ha, rfl⟩ := ha,
      simp only [i_1, alg_hom.coe_to_ring_hom, algebra.tensor_product.include_left_apply],
      suffices : ∀ (x : R), fg.to_ring_hom (x ⊗ₜ[A] 1) = f x ⊗ₜ[A] 1, rw ← this,
      rw quotient.of_surjective.dpow_apply hK s_fg, 
      have that := hf'.2 n a ha, 
      simp only [alg_hom.coe_to_ring_hom] at that, rw that,
      rw ← this, 
      apply congr_arg,
      simp only [← algebra.tensor_product.include_left_apply], 
      exact hK_pd.1.2 n a ha, 
      { apply ideal.mem_sup_left, apply ideal.mem_map_of_mem, exact ha, },
      { intro x, 
        simp only [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom, 
          algebra.tensor_product.map_tmul, map_one], }, 
      { have := ideal.image_eq_map_of_surjective f.to_ring_hom I _, 
        simp only [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom] at this,
        rw this, rw hI'I at ha', exact ha', 
        simp only [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom], 
        exact hf, }, }, },
  { -- hJ'.is_pd_morphism hK' ↑(i_2 A R' S')
    split, 
    { rw ← hK_map,
      rw ideal.map_le_iff_le_comap, intros a' ha',
      rw ideal.mem_comap,
      apply ideal.mem_sup_right, apply ideal.mem_map_of_mem, exact ha', },
    { intros n a' ha', 
      suffices ha : a' ∈ g '' J, obtain ⟨a, ha, rfl⟩ := ha,
      simp only [i_2, alg_hom.coe_to_ring_hom, algebra.tensor_product.include_right_apply],
      suffices : ∀ (y : S), fg.to_ring_hom (1 ⊗ₜ[A] y) = 1 ⊗ₜ[A] g y, rw ← this,
      rw quotient.of_surjective.dpow_apply hK s_fg, 
      have that := hg'.2 n a ha, 
      simp only [alg_hom.coe_to_ring_hom] at that, rw that,
      rw ← this, 
      apply congr_arg,
      simp only [← algebra.tensor_product.include_right_apply], 
      exact hK_pd.2.2 n a ha, 
      { apply ideal.mem_sup_right, apply ideal.mem_map_of_mem, exact ha, },
      { intro x, 
        simp only [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom, 
          algebra.tensor_product.map_tmul, map_one], }, 
      { have := ideal.image_eq_map_of_surjective g.to_ring_hom J _, 
        simp only [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom] at this,
        rw this, rw hJ'J at ha', exact ha',
        simp only [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom], 
        exact hg, }, }, },
  { -- ring_hom.ker fg is a “divised ideal”
    change is_sub_pd_ideal hK (ring_hom.ker (algebra.tensor_product.map f g) ⊓ K A I J),
    rw roby, 
    apply is_sub_pd_ideal_sup,
    apply is_sub_pd_ideal_map hI hK hK_pd.1,
    exact is_sub_pd_ideal_ker hI hI' hf', 
    apply is_sub_pd_ideal_map hJ hK hK_pd.2,
    exact is_sub_pd_ideal_ker hJ hJ' hg', },
  
  { -- K A I' J' = map fg (K A I J)
    simp only [K, fg, hI'I, hJ'J], 
    rw ideal.map_sup,
    apply congr_arg2,
    change map (i_1 A R' S').to_ring_hom (map f.to_ring_hom I) = map (algebra.tensor_product.map f g).to_ring_hom (map (i_1 A R S).to_ring_hom I),
    simp only [ideal.map_map],
    apply congr_arg2 _ _ rfl,
    ext x, 
    simp only [i_1, ring_hom.comp_apply, alg_hom.to_ring_hom_eq_coe, 
      alg_hom.coe_to_ring_hom, algebra.tensor_product.include_left_apply, 
      algebra.tensor_product.map_tmul, map_one],
    change map (i_2 A R' S').to_ring_hom (map g.to_ring_hom J) = map (algebra.tensor_product.map f g).to_ring_hom (map (i_2 A R S).to_ring_hom J),
    simp only [ideal.map_map],
    apply congr_arg2 _ _ rfl,
    ext x, 
    simp only [i_2, alg_hom.to_ring_hom_eq_coe, ring_hom.coe_comp, 
      alg_hom.coe_to_ring_hom, function.comp_app, 
      algebra.tensor_product.include_right_apply, algebra.tensor_product.map_tmul,
      map_one], },
end

-- Roby, lemma 7
lemma cond_Q_and_cond_T_free_imply_cond_T (A : Type*) [comm_ring A]
  (hQ : cond_Q A) (hT_free: cond_T_free A) : cond_T A := 
begin
  introsI R' _ S' _ _ _ I' J' hI' hJ',
  -- new universe issue
  obtain ⟨R, hR⟩ := hQ R' I' hI',
  sorry
end

/- Requires to prove that divided_power_algebra is compatible with restriction of scalars -/
def dp_scalar_extension (A : Type*) [comm_ring A] (R : Type*) [comm_ring R] [algebra A R]
  (M : Type*) [add_comm_group M] [module A M] [module R M] [is_scalar_tower A R M] :
  R ⊗[A] (divided_power_algebra A M) →ₐ[R] divided_power_algebra R M := 
sorry

def dp_scalar_extension_equiv (A : Type*) [comm_ring A] (R : Type*) [comm_ring R] [algebra A R]
  (M : Type*) [add_comm_group M] [module A M] [module R M] [is_scalar_tower A R M] :
  R ⊗[A] (divided_power_algebra A M) ≃ₐ[R] divided_power_algebra R M := 
sorry


-- Roby, lemma 8
lemma cond_T_and_cond_D_imply_cond_D' (A : Type*) [comm_ring A] (R : Type*) [comm_ring R]
  [algebra A R] (hT : cond_T A) (hD : cond_D A) : cond_D R :=
sorry

-- Roby, lemma 9 is in roby9

-- Roby, lemma 10
lemma cond_T_implies_cond_T'_free (A : Type*)[comm_ring A] (R : Type*) [comm_ring R] [algebra A R] 
  (hA : cond_T A) : cond_T_free R := sorry

-- Roby, lemma 11
lemma cond_T_free_int : cond_T_free ℤ := sorry

-- Roby, lemma 12 
lemma cond_D_int : cond_D ℤ := sorry 

lemma cond_Q_int : cond_Q ℤ := T_free_and_D_to_Q ℤ
cond_T_free_int cond_D_int

lemma cond_T_int : cond_T ℤ := cond_Q_and_cond_T_free_imply_cond_T ℤ (cond_Q_int) cond_T_free_int

lemma cond_D_holds (A : Type*) [comm_ring A] : cond_D A :=
cond_T_and_cond_D_imply_cond_D' ℤ A  cond_T_int cond_D_int

lemma cond_T_free_holds (A : Type*) [comm_ring A] : cond_T_free A := 
cond_T_implies_cond_T'_free ℤ A cond_T_int

lemma cond_Q_holds (A : Type*) [comm_ring A] : cond_Q A := 
T_free_and_D_to_Q A (cond_T_free_holds A) (cond_D_holds A) 

lemma cond_T_holds (A : Type*) [comm_ring A] : cond_T A :=
cond_Q_and_cond_T_free_imply_cond_T A (cond_Q_holds A) (cond_T_free_holds A)

end Proofs

/- Old names -/
theorem roby_δ (A : Type*) [comm_ring A] (M : Type*) [add_comm_group M] [module A M] :
  divided_power_algebra.cond_δ A M := cond_D_holds A M

lemma roby_D (A : Type*) [comm_ring A] : divided_power_algebra.cond_D A := cond_D_holds A

theorem roby_τ (A R S : Type u) [comm_ring A] [comm_ring R] [algebra A R] [comm_ring S] 
  [algebra A S] {I : ideal R} {J : ideal S} (hI : divided_powers I) (hJ : divided_powers J) :
  cond_τ A hI hJ := cond_T_holds A R S hI hJ

lemma roby_T (A : Type*) [comm_ring A] : cond_T A :=
cond_T_holds A

open divided_power_algebra

-- namespace divided_power_algebra

-- Part of Roby65 Thm 1
def divided_powers' (A : Type u) [comm_ring A] 
  (M : Type u) [add_comm_group M] [module A M] : divided_powers (aug_ideal A M) :=
(roby_D A M).some

lemma dpow_ι (A : Type*) [comm_ring A] 
  (M : Type*) [add_comm_group M] [module A M] (x : M) (n : ℕ) :
  dpow (divided_powers' A M) n (ι A x) = dp A n x := 
(roby_D A M).some_spec n x




lemma dp_comp (A : Type*) [comm_ring A] 
  (M : Type*) [add_comm_group M] [module A M] 
  (x : M) {n : ℕ} (m : ℕ) (hn : n ≠ 0) :
  dpow (divided_powers' A M) m (dp A n x) = ↑(mchoose m n) * dp A (m * n) x :=
by erw [← (roby_D A M).some_spec, dpow_comp _ m hn (ι_mem_aug_ideal A M x),  dpow_ι]

theorem roby_theorem_2 (R : Type*) [comm_ring R] 
  (M : Type*) [add_comm_group M] [module R M]
  {A : Type*} [comm_ring A] [algebra R A] {I : ideal A} (hI : divided_powers I) 
  {φ : M →ₗ[R] A} (hφ : ∀ m, φ m ∈ I) : 
  is_pd_morphism (divided_powers' R M) hI (divided_power_algebra.lift R M hI φ hφ) :=
begin
  apply cond_D_uniqueness,
  intros m n,
  rw dpow_ι,
end

lemma lift'_eq_dp_lift (R : Type u) [comm_ring R] 
  {M : Type v} [add_comm_group M] [module R M]
  (S : Type w) [comm_ring S] [algebra R S] 
  {N : Type w} [add_comm_group N] [module R N] [module S N] [is_scalar_tower R S N] 
  (f : M →ₗ[R] N) : 
  ∃ (hφ: ∀ m, ((ι S).restrict_scalars R).comp f m ∈ aug_ideal S N), 
  lift' R S f = divided_power_algebra.lift R M (divided_powers' S N) 
    (((ι S).restrict_scalars R).comp f) hφ := 
begin 
  suffices hφ : ∀ m, ((ι S).restrict_scalars R).comp f m ∈ aug_ideal S N,
  use hφ,
  ext a,
  obtain ⟨p, rfl⟩ := ideal.quotient.mk_surjective a, 
  rw p.as_sum, 
  simp only [map_sum],
  apply congr_arg2 _ rfl, 
  ext, 
  rw [monomial_eq, finsupp.prod],
  simp only [mv_polynomial.C_eq_smul_one, algebra.smul_mul_assoc, one_mul],
  simp only [← mkₐ_eq_mk R (relI R M), map_smul],
  apply congr_arg2 (•) rfl,
  simp only [map_prod], 
  apply congr_arg2 _ rfl,
  ext ⟨n, m⟩, 
  simp only [mkₐ_eq_mk, map_pow],
  apply congr_arg2 _ _ rfl,
  rw ← dp_eq_mk R n m, 
  rw lift'_dp_eq, rw lift_dp_eq, 
  simp only [linear_map.coe_comp, linear_map.coe_restrict_scalars_eq_coe,
    function.comp_app, dpow_ι], 

  intro m,
  simp only [linear_map.coe_comp, linear_map.coe_restrict_scalars_eq_coe, function.comp_app,
    ι_mem_aug_ideal S N (f m)],
end

#check lift'_eq_dp_lift

theorem roby_prop_8 (R : Type u) [comm_ring R] 
  {M : Type u} [add_comm_group M] [module R M]
  (S : Type u) [comm_ring S] [algebra R S] 
  {N : Type u} [add_comm_group N] [module R N] 
  [module S N] [is_scalar_tower R S N] 
  (f : M →ₗ[R] N) :
  is_pd_morphism (divided_powers' R M) (divided_powers' S N) 
    (divided_power_algebra.lift' R S f) := 
begin
  let φ := ((ι S).restrict_scalars R).comp f,
  suffices hφ : ∀ m, φ m ∈ aug_ideal S N,

  have roby := roby_theorem_2 R M (divided_powers' S N) hφ,
  suffices : lift R M (divided_powers' S N) φ hφ = lift' R S f, 
  rw this at roby, exact roby,
  
  obtain ⟨hφ', phφ'⟩ := lift'_eq_dp_lift R S f, 
  rw phφ',

  intro m,
  simp only [linear_map.coe_comp, linear_map.coe_restrict_scalars_eq_coe, 
    function.comp_app, ι_mem_aug_ideal S N (f m)],
end

end divided_power_algebra

end roby



/- 
and a divided power structure on that ideal such that
dpow R n (ι R x) = mk_alg_hom R (rel R M) (X (x, n)) 

(x,n) represents dpow n x
dpow m (x,n) should be dpow m (dpow n x) = (mchoose m n) dpow (m*n) x
An element x in divided_power_algebra R M takes the form
mk_alg_hom R (rel R M) (P)
where P is a sum of monomials  a * (m,n)   : m ∈ M, n ∈ ℕ
define
dpow k x = sum products a ^ kᵢ * dpow (mchoose kᵢ nᵢ (mᵢ,nᵢ * kᵢ)) 
where the sum is over functions → ℕ, with sum k
-/

/- Prove that it is unique… -/


/- Introduce notation ?
Here : x ^ [n] = mk_alg_hom R _ (X (x, n))
In general, x ^ [n]  for dpow n x ? 

-/

