import divided_powers.dp_algebra.init
import divided_powers.rat_algebra

import algebra.triv_sq_zero_ext

import ...weighted_homogeneous -- Modified version of PR #17855
import ...graded_ring_quot -- Quotients of graded rings

variables (R M : Type*) [comm_ring R] [add_comm_group M] [module R M]

noncomputable theory

namespace divided_power_algebra

open finset mv_polynomial ideal.quotient 
open triv_sq_zero_ext 
open ideal direct_sum 
open ring_quot

section decidable_eq


variable (M)
lemma relI_is_homogeneous : 
  (relI R M).is_homogeneous ((weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ))) :=
begin
  apply is_homogeneous_span,
  rintros x ⟨a, b, h, hx⟩,
  rw eq_sub_iff_add_eq.mpr hx,
  induction h with n r n m n p m n u v,
  { exact ⟨0, submodule.sub_mem _ (is_weighted_homogeneous_X R _ _) 
      (is_weighted_homogeneous_one R _)⟩ },
  { exact ⟨n, submodule.sub_mem _ (is_weighted_homogeneous_X R _ _) 
      (submodule.smul_mem _ _ (is_weighted_homogeneous_X R _ _))⟩ },
  { exact ⟨n + p, submodule.sub_mem _ (is_weighted_homogeneous.mul (is_weighted_homogeneous_X R _ _)
      (is_weighted_homogeneous_X R _ _)) (nsmul_mem (is_weighted_homogeneous_X R _ _) _)⟩ },
  { use n,
    refine submodule.sub_mem _ (is_weighted_homogeneous_X R _ _) (submodule.sum_mem _ _),
    intros c hc,
    have hnc : n = c + (n - c) := (nat.add_sub_of_le (finset.mem_range_succ_iff.mp hc)).symm, 
    nth_rewrite 1 hnc, 
    exact (is_weighted_homogeneous.mul (is_weighted_homogeneous_X R _ _)
      (is_weighted_homogeneous_X R _ _)) },
end

variables [decidable_eq R] [decidable_eq M]

/-- The graded submodules of `divided_power_algebra R M` -/
def grade := quot_submodule R (weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ))
  (divided_power_algebra.relI R M)

lemma one_mem : (1 : divided_power_algebra R M) ∈ grade R M 0 :=
⟨1, (is_weighted_homogeneous_one R _), rfl⟩

/-- The canonical decomposition of `divided_power_algebra R M` -/
def decomposition := 
quot_decomposition R (weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ)) 
  (divided_power_algebra.relI R M) (relI_is_homogeneous R M)

end decidable_eq

/-- The graded algebra structure on the divided power algebra-/
def divided_power_galgebra [decidable_eq R] [decidable_eq M] :
  graded_algebra (divided_power_algebra.grade R M) := 
graded_quot_alg R (weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ)) 
  (divided_power_algebra.relI R M) (divided_power_algebra.relI_is_homogeneous R M)

open mv_polynomial

section decidable_eq

variables (M) [decidable_eq R] [decidable_eq M]

-- Do we need both versions?
lemma dp_mem_grade (n : ℕ) (m : M) : dp R n m ∈ grade R M n  :=
⟨X (n, m), is_weighted_homogeneous_X R _ (n, m), rfl⟩

lemma mkₐ_mem_grade (n : ℕ) (m : M) : (mkₐ R (relI R M)) (X (n, m)) ∈ grade R M n :=
⟨X (n, m), is_weighted_homogeneous_X R _ (n, m), rfl⟩ 

/-- degree of a product is sum of degrees -/
lemma mul_mem ⦃i j : ℕ⦄ {gi gj : divided_power_algebra R M} (hi : gi ∈ grade R M i)
  (hj : gj ∈ grade R M j) : gi * gj ∈ grade R M (i + j) :=
(divided_power_galgebra R M).to_graded_monoid.mul_mem hi hj

def decompose : divided_power_algebra R M → direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)) :=
(divided_power_galgebra R M).to_decomposition.decompose'

/- graded_algebra (grade R M )-/
instance : graded_algebra (divided_power_algebra.grade R M) := 
divided_power_galgebra R M

end decidable_eq

variable (M)

lemma mkₐ_comp_to_supported : 
  (mkₐ R (relI R M)).comp ((subalgebra.val _).comp (to_supported R)) = (mkₐ R _) :=
begin
  apply mv_polynomial.alg_hom_ext,
  rintro ⟨n,m⟩,
  simp only [alg_hom.coe_comp, mkₐ_eq_mk, subalgebra.coe_val, function.comp_app, aeval_X,
    to_supported],
  split_ifs,
  { refl },
  { simp only [not_lt, le_zero_iff] at h,
    dsimp only [relI],
    rw [h, algebra_map.coe_one, quotient_mk_eq_of_rel rel.zero] },
end

variable {M}

lemma surjective_of_supported : function.surjective ((mkₐ R (relI R M)).comp 
  (subalgebra.val (supported R {nm : ℕ × M | 0 < nm.1 }))) := 
begin
  intro f, 
  obtain ⟨p',hp'⟩ := mk_surjective f,
  use to_supported R p',
  rw [← alg_hom.comp_apply, alg_hom.comp_assoc, mkₐ_comp_to_supported, ← hp', mkₐ_eq_mk],
end

lemma surjective_of_supported' [decidable_eq R] [decidable_eq M] {n : ℕ} (p : grade R M n) :
  ∃ (q : supported R {nm : ℕ × M | 0 < nm.1 }), 
  is_weighted_homogeneous prod.fst q.1 n ∧ ⇑(mk (relI R M)) q.1 = ↑p :=
begin
  --intro f, 
  have hp := p.2,
  simp only [grade, quot_submodule, subtype.val_eq_coe, submodule.mem_map, 
    mem_weighted_homogeneous_submodule, mkₐ_eq_mk] at hp,
  obtain ⟨p', hpn', hp'⟩ := hp,
  use to_supported R p',
  split,
  { apply to_supported_is_homogeneous,
    exact hpn', },
  rw ← mkₐ_eq_mk R,
  erw fun_like.congr_fun (mkₐ_comp_to_supported R M) p', -- TODO: write mk_comp_to_supported
  rw mkₐ_eq_mk R,
  rw hp',
  { apply_instance },
end

/-- The canonical linear map `M →ₗ[R] divided_power_algebra R M`. -/
def ι : M →ₗ[R] (divided_power_algebra R M) :=
{ to_fun    := λ m, dp R 1 m,
  map_add'  := λ x y, by simp only [dp_add, sum_range_succ', sum_range_zero, zero_add, nat.sub_zero,
    nat.sub_self, dp_zero, mul_one, one_mul],
  map_smul' := λ r x, by rw [dp_smul, pow_one, ring_hom.id_apply] }

lemma ι_def (m : M) : ι R m = dp R 1 m := rfl

lemma mk_alg_hom_mv_polynomial_ι_eq_ι (m : M) : mkₐ R (relI R M) (X (1, m)) = ι R m := rfl

lemma mk_alg_hom_mv_polynomial_ι_eq_ι' (m : M) : dp R 1 m = ι R m := rfl

@[simp] theorem ι_comp_lift {A : Type*} [comm_ring A] [algebra R A] {I : ideal A} 
  (hI : divided_powers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) :
  (lift R M hI φ hφ).to_linear_map.comp (ι R) = φ :=
begin
  ext,
  rw [linear_map.coe_comp, function.comp_app, alg_hom.to_linear_map_apply,
    ← mk_alg_hom_mv_polynomial_ι_eq_ι, lift_eqₐ, eval₂_X],
  exact hI.dpow_one (hφ x),
end

@[simp] theorem lift_ι_apply {A : Type*} [comm_ring A] [algebra R A] {I : ideal A}
  (hI : divided_powers I) (φ : M →ₗ[R] A) (hφ: ∀ m, φ m ∈ I) (x) :
  lift R M hI φ hφ (ι R x) = φ x :=
by { conv_rhs {rw ← ι_comp_lift R hI φ hφ,},refl, }

variables (M)



variable {R}
/-  [graded_algebra 𝒜] --not used in this def -/
def has_graded_dpow {A : Type*} [comm_ring A] [algebra R A] (𝒜 : ℕ → submodule R A)
  {I : ideal A} (hI : divided_powers I) := 
∀ (a : A) (ha : a ∈ I) (i : ℕ) (hai : a ∈ 𝒜 i) (n : ℕ), hI.dpow n a ∈ 𝒜 (n • i)

section decidable_eq

variables (R) [decidable_eq R] [decidable_eq M]

lemma lift_aux_is_homogeneous {A : Type*} [comm_ring A] [algebra R A] (𝒜 : ℕ → submodule R A) 
  [graded_algebra 𝒜] (f : ℕ × M → A) (hf_zero : ∀ m, f (0, m) = 1) 
  (hf_smul : ∀ (n : ℕ) (r : R) (m : M), f(⟨n, r • m⟩) = r ^ n • f(⟨n, m⟩)) 
  (hf_mul : ∀ n p m, f (⟨n, m⟩) * f (⟨p, m⟩) = ((n + p).choose n) • f (⟨n + p, m⟩))
  (hf_add : ∀ n u v, f (⟨n, u + v⟩) = (range (n + 1)).sum (λ (x : ℕ), f (⟨x, u⟩) * f (⟨n - x, v⟩))) 
  (hf : ∀ n m, f (n, m) ∈ 𝒜 n) : 
  galg_hom.is_homogeneous (divided_power_algebra.grade R M) 𝒜 
    (lift_aux R M f hf_zero hf_smul hf_mul hf_add) := 
begin
  intros i a ha,
  dsimp [grade, quot_submodule] at ha,
  obtain ⟨p, hp, rfl⟩ := ha, 
  rw [← mkₐ_eq_mk R, lift_aux_eq, p.as_sum, eval₂_sum],
  apply _root_.sum_mem,
  intros c hc, 
  rw [eval₂_monomial, ← smul_eq_mul, algebra_map_smul A],
  apply submodule.smul_mem, 
  rw ← hp (mem_support_iff.mp hc), 
  exact finsupp.prod.mem_grade _ _ _ _ (λ ⟨n,m⟩ hnm, hf n m),
  { apply_instance }, 
end

variable {R}
  
lemma lift_is_homogeneous {A : Type*} [comm_ring A] [algebra R A] (𝒜 : ℕ → submodule R A) 
  [graded_algebra 𝒜] {I : ideal A} (hI : divided_powers I) (hI' : has_graded_dpow 𝒜 hI)
  (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (hφ' : ∀ m, φ m ∈ 𝒜 1) : 
  galg_hom.is_homogeneous (divided_power_algebra.grade R M) 𝒜 (lift R M hI φ hφ) := 
begin
  apply lift_aux_is_homogeneous,
  intros n m,
  simpa only [algebra.id.smul_eq_mul, mul_one] using hI' (φ m) (hφ m) 1 (hφ' m) n
end

lemma lift'_is_homogeneous {N : Type*} [decidable_eq N] [add_comm_group N] [module R N] 
  (f : M →ₗ[R] N) :
  galg_hom.is_homogeneous (divided_power_algebra.grade R M) (divided_power_algebra.grade R N) 
    (lift' R R f) := 
begin
  apply lift_aux_is_homogeneous,
  { intro m, rw dp_zero},
  { intros n r m, rw [linear_map.map_smul, dp_smul] },
  { intros n p m, rw dp_mul }, 
  { intros n u v, rw [map_add, dp_add] },
  { intros n m, exact ⟨X(n, f m), ⟨is_weighted_homogeneous_X R _ _, rfl⟩⟩ },
end

/- We need the projections (divided_power_algebra R M) → grade R M n ,
more generally for graded algebras -/

variable (R)

def proj' (n : ℕ) : divided_power_algebra R M →ₗ[R] grade R M n := 
proj (grade R M) n

lemma proj'_zero_one : (proj' R M 0) 1 = 1 :=
by rw [proj', proj, linear_map.coe_mk, decompose_one]; refl

lemma proj'_zero_mul (x y : divided_power_algebra R M) : 
  (proj' R M 0) (x * y) = (proj' R M 0) x * (proj' R M 0) y :=
by simp only [proj', ← proj_zero_ring_hom'_apply, _root_.map_mul]

end decidable_eq 

instance : add_submonoid_class (submodule R (mv_polynomial (ℕ × M) R ⧸ relI R M))
  (divided_power_algebra R M) := 
submodule.add_submonoid_class

section grade_zero

variables (R)
-- TODO: use divided_powers.bot instead of of_square_zero
def algebra_map_inv : divided_power_algebra R M →ₐ[R] R :=
lift R M (divided_powers.of_square_zero.divided_powers (by rw [zero_eq_bot, pow_two, bot_mul]))
  (0 : M →ₗ[R] R) (λ m, by simp only [linear_map.zero_apply, zero_eq_bot, mem_bot])

lemma algebra_map_inv_eq (f : mv_polynomial (ℕ × M) R) : 
  algebra_map_inv R M (mkₐ R (relI R M) f) = aeval (λ nm : ℕ × M, ite (0 < nm.1) (0 : R) 1) f :=
begin
  rw ← alg_hom.comp_apply, 
  apply alg_hom.congr_fun,
  ext ⟨n, m⟩,
  simp only [algebra_map_inv, alg_hom.comp_apply, lift_eqₐ, linear_map.zero_apply, aeval_X],
  by_cases hn : 0 < n,
  { rw [if_pos hn, eval₂_X, divided_powers.dpow_eval_zero _ (ne_of_gt hn)] },
  { rw if_neg hn,
    rw [not_lt, le_zero_iff] at hn,
    rw [hn, eval₂_X, divided_powers.dpow_zero _ (mem_bot.mpr rfl)] }
end

lemma proj'_zero_comp_algebra_map [decidable_eq R] [decidable_eq M] (x : R) :
  (((proj' R M 0) ∘ (algebra_map R (divided_power_algebra R M))) x).val =
  ((algebra_map R (divided_power_algebra R M))) x :=
begin
  rw [function.comp_app, subtype.val_eq_coe, proj', proj, linear_map.coe_mk,
    algebra.algebra_map_eq_smul_one, decompose_smul, decompose_one, dfinsupp.coe_smul,
    pi.smul_apply, submodule.coe_smul_of_tower],
  refl,
end

-- variables (M) 
lemma algebra_map_left_inverse :
  function.left_inverse (algebra_map_inv R M) (algebra_map R (divided_power_algebra R M)) := 
λ m, by simp only [alg_hom.commutes, algebra.id.map_eq_id, ring_hom.id_apply]

@[simp] lemma algebra_map_inj (x y : R) :
  algebra_map R (divided_power_algebra R M) x = algebra_map R (divided_power_algebra R M) y ↔ 
  x = y :=
(algebra_map_left_inverse R M).injective.eq_iff

@[simp] lemma algebra_map_eq_zero_iff (x : R) : 
  algebra_map R (divided_power_algebra R M) x = 0 ↔ x = 0 :=
map_eq_zero_iff (algebra_map _ _) (algebra_map_left_inverse _ _).injective

@[simp] lemma algebra_map_eq_one_iff (x : R) : 
  algebra_map R (divided_power_algebra R M) x = 1 ↔ x = 1 :=
map_eq_one_iff (algebra_map _ _) (algebra_map_left_inverse _ _).injective

lemma mkₐ_eq_aeval {C : Type*} [comm_ring C] {D : Type*} (I : ideal (mv_polynomial D C)) :
  (ideal.quotient.mkₐ C I) = aeval (λ (d : D), ideal.quotient.mk I (X d)) :=
by ext d; simp only [mkₐ_eq_mk, aeval_X]

lemma mk_eq_eval₂ {C : Type*} [comm_ring C] {D : Type*} (I : ideal (mv_polynomial D C)) :
  (ideal.quotient.mk I).to_fun  = eval₂ (algebra_map C ((mv_polynomial D C)⧸ I)) 
  (λ (d : D), ideal.quotient.mk I (X d)) :=
by ext d; simp_rw [ring_hom.to_fun_eq_coe, ← mkₐ_eq_mk C, mkₐ_eq_aeval, aeval_X]; refl

lemma algebra_map_right_inv_of_degree_zero [decidable_eq R] [decidable_eq M] (x : grade R M 0) :
  (algebra_map R (divided_power_algebra R M)) ((algebra_map_inv R M) x.1) = x.1 := 
begin
  have hx : x.val ∈ grade R M 0 := x.2,
  simp only [grade, quot_submodule, subtype.val_eq_coe, submodule.mem_map,
    mem_weighted_homogeneous_submodule, is_weighted_homogeneous] at hx,
  obtain ⟨p, hp0, hpx⟩ := hx,
  rw [subtype.val_eq_coe, ← hpx, algebra_map_inv_eq, mkₐ_eq_aeval, map_aeval, algebra.id.map_eq_id, 
    ring_hom_comp_triple.comp_eq, coe_eval₂_hom, aeval_def, p.as_sum, eval₂_sum, eval₂_sum, 
    finset.sum_congr rfl],
  intros exp hexp,
  have h : ∀ (nm : ℕ × M), nm ∈ exp.support → nm.fst = 0,
  { intros nm hnm, 
    specialize hp0 (mem_support_iff.mp hexp),
    rw [weighted_degree', finsupp.total_apply, finsupp.sum, finset.sum_eq_zero_iff] at hp0,
    specialize hp0 nm hnm,
    rw [algebra.id.smul_eq_mul, nat.mul_eq_zero] at hp0,
    exact or.resolve_left hp0 (finsupp.mem_support_iff.mp hnm), },
  rw [eval₂_monomial, eval₂_monomial],
  apply congr_arg,
  rw finsupp.prod_congr,
  intros nm hnm,
  rw [if_neg, ← @prod.mk.eta _ _ nm, ← dp_eq_mk, h nm hnm, dp_zero, map_one],
  { rw [h nm hnm], exact lt_irrefl 0, },
end

/-- An ideal J of a commutative ring A is an augmentation ideal
if ideal.quotient.mk J has a right inverse which is a ring_hom -/
def _root_.is_augmentation_ideal (A : Type*) [comm_ring A] (J : ideal A) : Prop :=
∃ g : A⧸J →+* A, (ideal.quotient.mk J) ∘ g = id

/-- The augmentation ideal in the divided_power_algebra -/
def aug_ideal : ideal (divided_power_algebra R M) := ring_hom.ker (algebra_map_inv R M)

lemma mem_aug_ideal_iff (f : divided_power_algebra R M) : 
  f ∈ aug_ideal R M ↔ algebra_map_inv R M f = 0 :=
by rw [aug_ideal, ring_hom.mem_ker]

/-- The image of ι is contained in the augmentation ideal -/
lemma ι_mem_aug_ideal (m : M) : (ι R) m ∈ aug_ideal R M :=
by simp only [mem_aug_ideal_iff, ι, dp, linear_map.coe_mk, algebra_map_inv_eq, aeval_X, 
  nat.lt_one_iff, eq_self_iff_true, if_true]

/- We prove that the augmentation is an augmentation ideal, namely there is a section -/
lemma aug_ideal_is_augmentation_ideal : 
  is_augmentation_ideal (divided_power_algebra R M) (aug_ideal R M) :=
begin
  let g := ker_lift_alg (algebra_map_inv R M),
  let g1 := algebra_map R (divided_power_algebra R M ⧸ aug_ideal R M),
  use (algebra_map R (divided_power_algebra R M)).comp g.to_ring_hom,
  ext x,
  rw [ker_lift_alg_to_ring_hom, ring_hom.coe_comp, function.comp_app, mk_algebra_map, id.def],
  suffices h_inv : function.right_inverse g g1, 
  { exact h_inv x },
  refine function.right_inverse_of_injective_of_left_inverse
   (ring_hom.ker_lift_injective _) _,
  intro r, 
  rw [alg_hom_class.commutes, algebra.id.map_eq_id, ring_hom.id_apply]
end 

-- Q : if algebra map has a section, is the kernel an augmentation ideal?

lemma coeff_zero_of_mem_aug_ideal {f : mv_polynomial (ℕ × M) R}
  (hf : f ∈ supported R {nm : ℕ × M | 0 < nm.fst}) (hf0 : (mk (relI R M)) f ∈ aug_ideal R M) : 
  coeff 0 f = 0 :=
begin
  rw [aug_ideal, ring_hom.mem_ker] at hf0,
  rw [← hf0, ← mkₐ_eq_mk R _, algebra_map_inv_eq R M, eq_comm],
  conv_lhs { rw [f.as_sum, map_sum] },
  convert @finset.sum_eq_single _ _ _ (f.support) _ 0 _ _,
  { rw [monomial_zero', aeval_C, algebra.id.map_eq_id, ring_hom.id_apply], },
  { intros b hb hb0,
    rw [aeval_monomial, algebra.id.map_eq_id, ring_hom.id_apply],
    convert mul_zero _,
    obtain ⟨i, hi⟩ := finsupp.support_nonempty_iff.mpr hb0,  
    rw finsupp.prod, 
    apply finset.prod_eq_zero hi,
    have hi' : 0 < i.fst,
    { apply mem_supported.mp hf,
      rw [finset.mem_coe, mem_vars],
      exact ⟨b, ⟨hb, hi⟩⟩ },
    rw if_pos hi',
    exact zero_pow (zero_lt_iff.mpr (finsupp.mem_support_iff.mp hi)) },
  { intro hf',
    rw [monomial_zero', aeval_C, algebra.id.map_eq_id, ring_hom.id_apply,
      ← not_mem_support_iff.mp hf'] }
end  

lemma aug_ideal_eq_span' : 
  aug_ideal R M = span (set.image2 (dp R) {n : ℕ | 0 < n} ⊤) := sorry


-- TODO: is it better to use ⊤ or set.univ? Is it the same?
lemma aug_ideal_eq_span :
--  aug_ideal R M = span (set.image (λ nm, mk _ (X nm)) { nm : ℕ × M | 0 < nm.1 }) := 
  aug_ideal R M = span (set.image2 (dp R) {n : ℕ | 0 < n} set.univ) :=
begin
  classical,
  apply le_antisymm,
  { intros f0 hf0,
    obtain ⟨⟨f, hf⟩, rfl⟩ := divided_power_algebra.surjective_of_supported R f0,
    have hf0' : coeff 0 f = 0 := coeff_zero_of_mem_aug_ideal R M hf hf0,
    simp only [alg_hom.coe_comp, mkₐ_eq_mk, subalgebra.coe_val, function.comp_app, set_like.coe_mk] at hf0 ⊢,
    rw f.as_sum, rw map_sum, 
    refine ideal.sum_mem _ _,
    intros c hc, 
    rw [monomial_eq, finsupp.prod],
    simp only [_root_.map_mul], 
    refine mul_mem_left _ _ _,
    suffices supp_ss : ↑(c.support) ⊆ {nm : ℕ × M | 0 < nm.fst},
    { by_cases hc0 : c.support.nonempty,
      { obtain ⟨⟨n, m⟩, hnm⟩ := hc0,
        rw finset.prod_eq_mul_prod_diff_singleton hnm,
        simp only [_root_.map_mul, map_pow],
        apply mul_mem_right _ _ 
          (pow_mem_of_mem _ _ _ (nat.pos_of_ne_zero (finsupp.mem_support_iff.mp hnm))),
        exact subset_span ⟨n, m, by simpa only using supp_ss hnm, set.mem_univ _, rfl⟩, }, 
      { -- cas où c.support est vide : c = 0 ; contradiction
        rw [not_nonempty_iff_eq_empty, finsupp.support_eq_empty] at hc0,
        rw hc0 at hc, 
        exact absurd hf0' (mem_support_iff.mp hc) }},
    { -- supp_ss
      intros nm hnm, 
      apply mem_supported.mp hf, 
      simp only [mem_vars, mem_coe, mem_support_iff, ne.def, finsupp.mem_support_iff, exists_prop],
      rw [mem_coe, finsupp.mem_support_iff] at hnm,
      exact ⟨c,⟨mem_support_iff.mp hc, hnm⟩⟩ }}, 
  { rw span_le, 
    intros f,
    simp only [set.mem_image2, set.mem_set_of_eq, set.mem_univ, true_and, exists_and_distrib_left, set_like.mem_coe,
  forall_exists_index, and_imp], 
    intros n hn m hf, 
    rw [← hf, mem_aug_ideal_iff, algebra_map_inv, lift_dp_eq],
    simp_rw linear_map.zero_apply,
    rw [divided_powers.dpow_eval_zero _ (ne_of_gt hn)] },
end

lemma right_inv' [decidable_eq R] [decidable_eq M] (x : R) :
  (algebra_map_inv R M) (((proj' R M 0) ∘ (algebra_map R (divided_power_algebra R M))) x).val = x :=
by rw proj'_zero_comp_algebra_map; exact algebra_map_left_inverse R M x

lemma left_inv' [decidable_eq R] [decidable_eq M] (x : grade R M 0) :
  ((proj' R M 0) ∘ (algebra_map R (divided_power_algebra R M))) ((algebra_map_inv R M) x.val) = x :=
begin
  ext,
  simp only [proj', proj, linear_map.coe_mk, function.comp_app], 
  conv_rhs { rw [← subtype.val_eq_coe, ← direct_sum.decompose_of_mem_same _ x.2] },
  rw algebra_map_right_inv_of_degree_zero R M x,
end

lemma lift_aug_ideal_le {A : Type*} [comm_ring A] [algebra R A] {I : ideal A} (hI : divided_powers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) : ideal.map (lift R M hI φ hφ) (aug_ideal R M) ≤ I := 
begin
  simp only [aug_ideal_eq_span, ideal.map_span, ideal.span_le, set_like.mem_coe],
  rintros y ⟨x, ⟨n, m, hn, hm, rfl⟩, rfl⟩,
  rw lift_dp_eq, 
  exact hI.dpow_mem (ne_of_gt hn) (hφ m),
end

lemma lift_mem_of_mem_aug_ideal {A : Type*} [comm_ring A] [algebra R A] {I : ideal A} (hI : divided_powers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (x : divided_power_algebra R M) (hx : x ∈ aug_ideal R M) : lift R M hI φ hφ x ∈ I := (lift_aug_ideal_le R M hI φ hφ) (mem_map_of_mem _ hx)

/- grade R M 0 → R is isomorphism -/
noncomputable! def ring_equiv_degree_zero [decidable_eq R] [decidable_eq M] :
  ring_equiv (grade R M 0) R := 
{ to_fun    := λ x, algebra_map_inv R M x.1,
  inv_fun   := (proj' R M 0) ∘ (algebra_map R (divided_power_algebra R M)),
  left_inv  := left_inv' R M,
  right_inv := right_inv' R M,
  map_mul'  := λ x y, by rw ← _root_.map_mul; refl,
  map_add'  := λ x y, by rw ← _root_.map_add; refl, }

def proj_0_ring_hom [decidable_eq R] [decidable_eq M] : ring_hom (divided_power_algebra R M) R :=
{ to_fun    := (ring_equiv_degree_zero R M).to_fun ∘ (proj' R M 0),
  map_one'  := by rw [ring_equiv.to_fun_eq_coe, mul_equiv_class.map_eq_one_iff, proj'_zero_one],
  map_mul'  := λx y, by rw [ring_equiv.to_fun_eq_coe, function.comp_app, ← _root_.map_mul, 
    proj'_zero_mul],
  map_zero' := by simp only [ring_equiv.to_fun_eq_coe, function.comp_app, map_zero],
  map_add'  := by simp only [ring_equiv.to_fun_eq_coe, function.comp_app, map_add, 
    eq_self_iff_true, forall_const] }

end grade_zero

section grade_one

variable (R)
/-- The canonical map from `divided_power_algebra R M` into `triv_sq_zero_ext R M` that sends
`divided_power_algebra.ι` to `triv_sq_zero_ext.inr`. -/
def to_triv_sq_zero_ext [module Rᵐᵒᵖ M] [is_central_scalar R M] :
  divided_power_algebra R M →ₐ[R] triv_sq_zero_ext R M :=
lift R M (divided_powers.of_square_zero.divided_powers (triv_sq_zero_ext.square_zero R M) :
  divided_powers (ker_ideal R M)) (inr_hom R M) (λ m, (mem_ker_ideal_iff_exists R M _).mpr ⟨m, rfl⟩)

@[simp] lemma to_triv_sq_zero_ext_ι [module Rᵐᵒᵖ M] [is_central_scalar R M] (x : M) :
   to_triv_sq_zero_ext R M (ι R x) = inr x :=
lift_ι_apply R _ _ _ x

lemma to_triv_sq_zero_ext_snd [module Rᵐᵒᵖ M] [is_central_scalar R M] (m : M) :
  ((to_triv_sq_zero_ext R M) ((mkₐ R (relI R M)) (X (1, m)))).snd = m :=
by rw [← dp_eq_mkₐ, ← ι_def, to_triv_sq_zero_ext_ι]; refl

lemma deg_one_left_inv [decidable_eq R] [decidable_eq M] [module Rᵐᵒᵖ M] [is_central_scalar R M] :
  function.left_inverse (λ (x : (grade R M 1)), (to_triv_sq_zero_ext R M x.1).snd) 
    ((proj' R M 1) ∘ (ι R)) :=
begin
  intros m,
  simp only [function.comp_app, subtype.val_eq_coe, ι, dp, proj', proj, linear_map.coe_mk],
  rw ← triv_sq_zero_ext.snd_inr R m, 
  apply congr_arg,
  rw [snd_inr, ← to_triv_sq_zero_ext_ι, ι, linear_map.coe_mk, dp, 
    decompose_of_mem_same _ (mkₐ_mem_grade R M 1 m)],
end

theorem grade_one_eq_span (R M : Type*) [comm_ring R] [add_comm_group M]
  [module R M] [decidable_eq R] [decidable_eq M] : 
  grade R M 1 = submodule.span R (set.range (dp R 1)) := 
begin
  apply le_antisymm,
  { intros p hp,
    obtain ⟨q, hq1, hqp⟩ := surjective_of_supported' R ⟨p, hp⟩,
    rw [subtype.val_eq_coe, submodule.coe_mk] at hqp,
    rw [is_weighted_homogeneous, subtype.val_eq_coe] at hq1,
    rw [← hqp, ← mkₐ_eq_mk R, (q : mv_polynomial (ℕ × M) R).as_sum, map_sum],
    apply submodule.sum_mem (submodule.span R (set.range (dp R 1))),
    intros d hd,
    have hsupp : ∀ (nm : ℕ × M), nm ∈ d.support → 0 < nm.fst,
    { intros nm hnm,
      apply mem_supported.mp q.2,
      rw [subtype.val_eq_coe, mem_coe, mem_vars],
      exact ⟨d, hd, hnm⟩, },
    obtain ⟨m, hm⟩ := eq_finsupp_single_of_degree_one M (hq1 (mem_support_iff.mp hd)) hsupp,
    rw [← hm, monomial_eq, C_mul', map_smul, finsupp.prod_single_index, pow_one],
    exact submodule.smul_mem (submodule.span R (set.range (dp R 1))) _ 
      (submodule.subset_span (set.mem_range.mpr ⟨m, rfl⟩)),
    { rw pow_zero}, },
  { rw submodule.span_le,
    intros p hp,
    obtain ⟨m, hm⟩ := set.mem_range.mp hp,
    rw ← hm,
    exact dp_mem_grade R M 1 m, }
end

theorem grade_one_eq_span' (R M : Type*) [comm_ring R] [add_comm_group M]
  [module R M] [decidable_eq R] [decidable_eq M] : 
  (⊤ : submodule R (grade R M 1)) = 
    submodule.span R (set.range (λ m, ⟨dp R 1 m, dp_mem_grade R M 1 m⟩)) := 
begin
  apply submodule.map_injective_of_injective (grade R M 1).injective_subtype,
  simp only [submodule.map_subtype_top],
  rw submodule.map_span,
  simp_rw grade_one_eq_span R M,
  rw ← set.range_comp, refl,
end

lemma deg_one_right_inv [decidable_eq R] [decidable_eq M] [module Rᵐᵒᵖ M] [is_central_scalar R M] :
  function.right_inverse ((triv_sq_zero_ext.snd_hom R M) ∘ 
      (to_triv_sq_zero_ext R M).to_linear_map ∘ (grade R M 1).subtype)
    ((proj' R M 1) ∘ (ι R)) := --try with snd_hom , submodule.val
begin
  simp only [function.right_inverse_iff_comp, ← linear_map.coe_comp, ← @linear_map.id_coe R],
  rw fun_like.coe_injective.eq_iff,
  apply linear_map.ext_on_range (grade_one_eq_span' R M).symm,
  intros m,
  have hm : ((to_triv_sq_zero_ext R M) (dp R 1 m)).snd = m,
  { rw [to_triv_sq_zero_ext, dp, mkₐ_eq_mk, lift, lift_aux, liftₐ_apply, lift_mk],
    simp only [inr_hom_apply, alg_hom.coe_to_ring_hom, eval₂_alg_hom_X'],
    rw [divided_powers.dpow_one _ ((mem_ker_ideal_iff_exists R M _).mpr ⟨m, rfl⟩), snd_inr] },
  simp only [linear_map.coe_comp, submodule.coe_subtype, function.comp_app, submodule.coe_mk, 
    alg_hom.to_linear_map_apply, snd_hom_apply, linear_map.id_coe, id.def, proj', proj,
    linear_map.coe_mk, ι],
  ext,
  rw [hm, decompose_of_mem_same _ (dp_mem_grade R M 1 m), subtype.coe_mk],
end

/- ι : M → grade R M 1 is isomorphism -/
def linear_equiv_degree_one [decidable_eq R] [decidable_eq M] [module Rᵐᵒᵖ M]
  [is_central_scalar R M] : linear_equiv (ring_hom.id R) M (grade R M 1) :=
{ to_fun    := (proj' R M 1).comp (ι R),
  inv_fun   := λ x, triv_sq_zero_ext.snd_hom R M (to_triv_sq_zero_ext R M x.1),
  map_add'  := λ x y, by simp only [map_add],
  map_smul' := λ r x, by simp only [linear_map.map_smulₛₗ],
  left_inv  := deg_one_left_inv R M,
  right_inv := deg_one_right_inv R M }

end grade_one

end divided_power_algebra