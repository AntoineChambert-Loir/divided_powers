
import divided_powers.dp_algebra.init
import divided_powers.dp_algebra.graded
import divided_powers.rat_algebra
import divided_powers.sub_pd_ideal
import divided_powers.ideal_add

import ring_theory.tensor_product

noncomputable theory

section 


variables (R M : Type*) [comm_ring R] [add_comm_group M] [module R M]

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
  (h1 : ∀ (x : M) (n : ℕ), h.dpow n (ι R x) = dp R n x)
  (h1' : ∀ (x : M) (n : ℕ), h'.dpow n (ι R x) = dp R n x) :
h = h' := 
begin
  apply divided_powers.dp_uniqueness h h' (aug_ideal_eq_span R M),
  rintros n f ⟨q, m, hq : 0 < q, _, rfl⟩, 
  nth_rewrite 0 [← h1 m q],
  rw [← h1' m q, h.dpow_comp n (ne_of_gt hq) (ι_mem_aug_ideal R M m), 
    h'.dpow_comp n (ne_of_gt hq) (ι_mem_aug_ideal R M m), h1 m,  h1' m], 
end

def cond_δ : Prop := ∃ (h : divided_powers (aug_ideal R M)), 
  ∀ (x : M) (n : ℕ), h.dpow n (ι R x) = dp R n x 

def cond_D (R : Type*) [_inst_1 : comm_ring R] := 
  ∀ (M : Type*) [add_comm_group M], by exactI ∀ [module R M],
  by exactI cond_δ R M

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

open_locale tensor_product

variables (A R S : Type*) [comm_ring A] [comm_ring R] [algebra A R] [comm_ring S] [algebra A S] 
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
  suffices : x ∈ sub_pd_ideal.pd_equalizer hK hK',  
  { exact ((sub_pd_ideal.mem_pd_equalizer_iff _ _).mp this).2 n,},
  suffices h_ss : K A I J ≤ sub_pd_ideal.pd_equalizer hK hK',
  { exact h_ss hx },
  dsimp only [K], 
  rw sup_le_iff,
  split,
  apply sub_pd_ideal.le_equalizer_of_pd_morphism hI (i_1 A R S).to_ring_hom
    le_sup_left hK hK' hIK hIK',
  apply sub_pd_ideal.le_equalizer_of_pd_morphism hJ (i_2 A R S).to_ring_hom
    le_sup_right hK hK' hJK hJK',
end

def cond_τ : Prop :=
∃ hK : divided_powers (K A I J), 
  is_pd_morphism hI hK (i_1 A R S) ∧ is_pd_morphism hJ hK (i_2 A R S)

def cond_T (A : Type*) [comm_ring A] : Prop := ∀ (R S : Type*)[comm_ring R] [comm_ring S], by exactI ∀ [algebra A R] [algebra A S],
by exactI ∀ {I : ideal R} {J : ideal S} (hI : divided_powers I) (hJ : divided_powers J),
cond_τ A hI hJ 

section free

-- hR_free, hS_free are not used for the def (they might be needed at lemmas about cond_T_free)

def cond_T_free (A : Type*) [comm_ring A] : Prop := ∀ (R S : Type*) [comm_ring R] [comm_ring S], by exactI ∀ [algebra A R] [algebra A S],
by exactI ∀ (hR_free : module.free A R) (hS_free : module.free A S),
by exactI ∀ {I : ideal R} {J : ideal S} (hI : divided_powers I) (hJ : divided_powers J),
cond_τ A hI hJ

/- def cond_Q (A R : Type*) [comm_ring A] [comm_ring R] /- [algebra A R] not used -/
  {I : ideal R} (hI : divided_powers I) : Prop := 
∃ (T : Type*) [comm_ring T], by exactI ∃ [algebra A T], by exactI ∃ [module.free A T]
  {J : ideal T} (hJ : divided_powers J) (f : pd_morphism hI hJ), 
  function.surjective f.to_ring_hom
 -/

def cond_Q (A : Type*) [comm_ring A] : Prop := 
∀ (R : Type*) [comm_ring R],
by exactI ∀ [algebra A R] {I : ideal R} (hI : divided_powers I),
∃ (T : Type*) [comm_ring T], 
  by exactI ∃ [algebra A T], 
  by exactI ∃ [module.free A T] 
  (f : T →ₐ[A] R)  
  {J : ideal T} (hJ : divided_powers J) (hf : is_pd_morphism hJ hI f),
  function.surjective f
  
end free

.

section Proofs

open divided_power_algebra

/- 
variables {M : Type*} [add_comm_group M] [module R M] (h : divided_powers (aug_ideal R M))(hh : ∀ (x : M) (n : ℕ), h.dpow n (ι R x) = dp R n x)
include M  h -/

-- Roby, lemma 3
lemma cond_D_uniqueness {M : Type*} [add_comm_group M] [module R M] 
  (h : divided_powers (aug_ideal R M))
  (hh : ∀ (x : M) (n : ℕ), h.dpow n (ι R x) = dp R n x)
  {S : Type*} [comm_ring S]
  [algebra R S] {J : ideal S} (hJ : divided_powers J) (f : M →ₗ[R] S) 
  (hf : ∀ m, f m ∈ J) :
  is_pd_morphism h hJ (divided_power_algebra.lift R M hJ f hf)  := 
sorry


-- Roby, lemma 4
lemma T_free_and_D_to_Q (A : Type*) [comm_ring A] 
  (hT_free : cond_T_free A) (hD : cond_D A) : cond_Q A :=
sorry

-- Roby, lemma 5
lemma ker_tens (A : Type*) [comm_ring A] {R S R' S' : Type*} 
  [comm_ring R] [comm_ring S] [comm_ring R'] [comm_ring S']
  [algebra A R] [algebra A S] [algebra A R'] [algebra A S'] 
  (f : R →ₐ[A] R') (g : S →ₐ[A] S') 
  (hf : function.surjective f) (hg : function.surjective g) : 
  ring_hom.ker (algebra.tensor_product.map f g) 
  = (f.to_ring_hom.ker.map (algebra.tensor_product.include_left : R →ₐ[A] (R ⊗[A] S))) 
  ⊔ ((g.to_ring_hom.ker.map (algebra.tensor_product.include_right : S →ₐ[A] (R ⊗[A] S)))) :=
sorry

-- Roby, lemma 6
lemma cond_τ_rel (A : Type*) [comm_ring A] {R S R' S' : Type*} 
  [comm_ring R] [comm_ring S] [comm_ring R'] [comm_ring S']
  [algebra A R] [algebra A S] [algebra A R'] [algebra A S'] 
  (f : R →ₐ[A] R') (g : S →ₐ[A] S') 
  (hf : function.surjective f) (hg : function.surjective g)
  {I : ideal R} (hI : divided_powers I) 
  {J : ideal S} (hJ : divided_powers J)
  {I' : ideal R'} (hI' : divided_powers I') 
  {J' : ideal S'} (hJ' : divided_powers J')
  (hf' : is_pd_morphism hI hI' f) (hg' : is_pd_morphism hJ hJ' g)
  (hRS : cond_τ A hI hJ) : cond_τ A hI' hJ' :=
sorry

-- Roby, lemma 7
lemma cond_Q_and_cond_T_free_imply_cond_T (A : Type*) [comm_ring A]
  (hQ : cond_Q A) (hT_free: cond_T_free A) : cond_T A := 
sorry

/- Requires to prove that divided_power_algebra is compatible with extension of scalars -/
def dp_scalar_extension (A : Type*) [comm_ring A] (R : Type*) [comm_ring R] [algebra A R]
  (M : Type*) [add_comm_group M] [module A M] [module R M] [is_scalar_tower A R M] :
  R ⊗[A] (divided_power_algebra A M) →ₐ[R] divided_power_algebra R M := 
sorry

def dp_scalar_extension_equiv (A : Type*) [comm_ring A] (R : Type*) [comm_ring R] [algebra A R]
  (M : Type*) [add_comm_group M] [module A M] [module R M] [is_scalar_tower A R M] :
  R ⊗[A] (divided_power_algebra A M) ≃ₐ[R] divided_power_algebra R M := 
sorry


-- Roby, lemma 8
lemma cond_T_and_cond_D_imply_cond_D' (A : Type*) [comm_ring A] (R : Type*) [comm_ring R] [algebra A R] 
(hT : cond_T A) (hD : cond_D A) : cond_D R :=
sorry

-- Roby, lemma 9 is in roby9

-- Roby, lemma 10
lemma cond_T_implies_cond_T'_free (A : Type*)[comm_ring A] (R : Type*) [comm_ring R] [algebra A R] (hA : cond_T A) : cond_T_free R := sorry

-- Roby, lemma 11
lemma cond_T_free_int : cond_T_free ℤ := sorry

-- Roby, lemma 12 
lemma cond_D_int : cond_D ℤ := sorry 

lemma cond_Q_int : cond_Q ℤ := T_free_and_D_to_Q ℤ
cond_T_free_int cond_D_int

lemma cond_T_int : cond_T ℤ := cond_Q_and_cond_T_free_imply_cond_T ℤ (cond_Q_int) cond_T_free_int

lemma cond_D_holds (A : Type*) [comm_ring A] : cond_D A :=
cond_T_and_cond_D_imply_cond_D' ℤ A  cond_T_int cond_D_int

lemma cond_T_free_holds (A : Type*) [comm_ring A] : cond_T_free A := cond_T_implies_cond_T'_free ℤ A cond_T_int

lemma cond_Q_holds (A : Type*) [comm_ring A] : cond_Q A := 
T_free_and_D_to_Q A (cond_T_free_holds A) (cond_D_holds A) 

lemma cond_T_holds (A : Type*) [comm_ring A] : cond_T A :=
cond_Q_and_cond_T_free_imply_cond_T A (cond_Q_holds A) (cond_T_free_holds A)

end Proofs

/- Old names -/
theorem roby_δ (A : Type*) [comm_ring A] (M : Type*) [add_comm_group M] [module A M] :
  divided_power_algebra.cond_δ A M := cond_D_holds A M

lemma roby_D (A : Type*) [comm_ring A] : divided_power_algebra.cond_D A := cond_D_holds A

theorem roby_τ (A R S : Type*) [comm_ring A] [comm_ring R] [algebra A R] [comm_ring S] 
  [algebra A S] {I : ideal R} {J : ideal S} (hI : divided_powers I) (hJ : divided_powers J) :
  cond_τ A hI hJ := cond_T_holds A R S hI hJ

lemma roby_T (A : Type*) [comm_ring A] : cond_T A :=
cond_T_holds A

open divided_power_algebra

-- namespace divided_power_algebra

-- Part of Roby65 Thm 1
def divided_powers' (A : Type*) [comm_ring A] (M : Type*) [add_comm_group M]
  [module A M] : divided_powers (aug_ideal A M) :=
(roby_D A M).some

lemma dpow_ι (A : Type*) [comm_ring A] (M : Type*) [add_comm_group M]
  [module A M] (x : M) (n : ℕ) :
  dpow (divided_powers' A M) n (ι A x) = dp A n x :=
(roby_D A M).some_spec x n

lemma dp_comp (A : Type*) [comm_ring A] (M : Type*) [add_comm_group M]
  [module A M] (x : M) {n : ℕ} (m : ℕ) (hn : n ≠ 0) :
  dpow (divided_powers' A M) m (dp A n x) = ↑(mchoose m n) * dp A (m * n) x :=
by erw [← (roby_D A M).some_spec, dpow_comp _ m hn (ι_mem_aug_ideal A M x),  dpow_ι]

theorem roby_theorem_2 (R : Type*) [comm_ring R] (M : Type*) [add_comm_group M] [module R M]
  {A : Type*} [comm_ring A] [algebra R A] {I : ideal A} (hI : divided_powers I) {φ : M →ₗ[R] A} 
  (hφ : ∀ m, φ m ∈ I) : 
  is_pd_morphism (divided_powers' R M) hI (divided_power_algebra.lift R M hI φ hφ) :=
begin
  split,
  { -- simp only [ideal.map, ideal.span_le], 
    rw aug_ideal_eq_span,  
    rw map_span,
    rw ideal.span_le,
    rintros x ⟨a, ⟨n,m,⟨hn : 0 < n, h, rfl⟩⟩, rfl⟩,
    simp only [lift_dp_eq, alg_hom.coe_to_ring_hom, set_like.mem_coe],
    exact hI.dpow_mem (ne_of_gt hn) (hφ  m), },
  { intros n a ha, 
    apply symm,
    rw dp_uniqueness' (divided_powers' R M) hI (lift R M hI φ hφ) (aug_ideal_eq_span R M) _ n a ha,
    rintros n a ⟨q, m, hq : 0 < q, hm, rfl⟩,
    simp only [alg_hom.coe_to_ring_hom, lift_dp_eq],
    rw ← dpow_ι,
    rw hI.dpow_comp n (ne_of_gt hq) (hφ m),
    rw (divided_powers' R M).dpow_comp n (ne_of_gt hq) (ι_mem_aug_ideal R M m),
    simp only [_root_.map_mul, map_nat_cast], 
    apply congr_arg2 _ rfl, 
    rw dpow_ι, rw lift_dp_eq, },
end

lemma lift'_eq_dp_lift (R : Type*) [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
  (S : Type*) [comm_ring S] [algebra R S] {N : Type*} [add_comm_group N] [module R N]
  [module S N] [is_scalar_tower R S N] [algebra R (divided_power_algebra S N)]
  [is_scalar_tower R S (divided_power_algebra S N)] (f : M →ₗ[R] N) : 
  let φ : M →ₗ[R] divided_power_algebra S N := ((ι S).restrict_scalars R).comp f  in
  let hφ : ∀ m, φ m ∈ aug_ideal S N := sorry in  
  lift' R S f = divided_power_algebra.lift R M (divided_powers' S N) φ hφ := 
  begin 
  intros φ hφ,
  ext a,

  

  sorry

  end




theorem roby_prop_8 (R : Type*) [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
  (S : Type*) [comm_ring S] [algebra R S] {N : Type*} [add_comm_group N] [module R N]
  [module S N] [is_scalar_tower R S N] [algebra R (divided_power_algebra S N)]
  [is_scalar_tower R S (divided_power_algebra S N)] (f : M →ₗ[R] N) :
  is_pd_morphism (divided_powers' R M) (divided_powers' S N) 
    (divided_power_algebra.lift' R S f) := 
begin
  split,
  simp only [aug_ideal_eq_span],
  rw ideal.map_span,
  rw ideal.span_le, 
  rintros b ⟨a, ⟨q, m, hq : 0 < q, hm, rfl⟩, rfl⟩,
  simp only [alg_hom.coe_to_ring_hom, set_like.mem_coe, lift'_dp_eq],
  exact ideal.subset_span ⟨q, f m, hq, set.mem_univ _, rfl⟩,

  intros n a ha,

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

