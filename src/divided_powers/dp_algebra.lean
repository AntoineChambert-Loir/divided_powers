/- Copyright 2022 ACL & MIdFF-/

import algebra.free_algebra
import algebra.ring_quot
import algebra.triv_sq_zero_ext
import algebra.algebra.operations
import linear_algebra.multilinear.basic

import ring_theory.graded_algebra.basic
import ring_theory.tensor_product
import data.mv_polynomial.supported

import divided_powers.basic
import divided_powers.sub_pd_ideal
import divided_powers.rat_algebra
import divided_powers.ideal_add
import ..weighted_homogeneous -- Modified version of PR #17855
import ..graded_ring_quot -- Quotients of graded rings
import ..graded_module_quot

noncomputable theory

/-! 
The divided power algebra of a module -/

open finset mv_polynomial ring_quot direct_sum

namespace mv_polynomial

/-- `mv_polynomial.eval₂ (algebra_map R S) g` as an `R`-algebra homomorphism. -/
def eval₂_alg_hom {R S σ : Type*} [comm_semiring R] [comm_semiring S] [algebra R S] (g : σ → S) :
  mv_polynomial σ R →ₐ[R] S := 
{ commutes' := λ r, by rw [ring_hom.to_fun_eq_coe, coe_eval₂_hom, algebra_map_eq, eval₂_C], 
  .. mv_polynomial.eval₂_hom (algebra_map R S) g }

@[simp] lemma eval₂_alg_hom_apply {R S σ : Type*} [comm_semiring R] [comm_semiring S] [algebra R S]
  (g : σ → S) (P : mv_polynomial σ R) : 
  eval₂_alg_hom g P = eval₂_hom (algebra_map R S) g P := rfl

@[simp] lemma eval₂_hom.smul {R S σ : Type*} [comm_semiring R] [comm_semiring S]  (f : R →+* S) (g : σ → S) (r : R) (P : mv_polynomial σ R) :
  eval₂_hom f g (r • P) = f r • eval₂_hom f g P := 
by simp only [smul_eq_C_mul, coe_eval₂_hom, eval₂_mul, eval₂_C, algebra.id.smul_eq_mul]

end mv_polynomial

section ideals_and_rel

-- R and the algebra instance are not used
/- lemma quotient_mk_eq_of_rel (R : Type*) [comm_ring R] {A : Type*} [comm_ring A] [algebra R A]  
  {r : A → A → Prop} {a b : A} (h : r a b) : -/
lemma quotient_mk_eq_of_rel {A : Type*} [comm_ring A] {r : A → A → Prop} {a b : A} (h : r a b) :
  ideal.quotient.mk (ideal.of_rel r) a = ideal.quotient.mk (ideal.of_rel r) b :=
begin
  suffices : function.injective (ring_quot.ring_quot_equiv_ideal_quotient r).inv_fun,
  { apply this, 
    exact mk_ring_hom_rel h },
  exact function.injective_iff_has_left_inverse.mpr ⟨(ring_quot_equiv_ideal_quotient r).to_fun,
    (ring_quot_equiv_ideal_quotient r).right_inv⟩,
end

lemma ideal.quotient_mk_eq_ring_quot_apply (R : Type*) [comm_ring R] {A : Type*} [comm_ring A]
  [algebra R A] (r : A → A → Prop) (a : A) :
  ideal.quotient.mk (ideal.of_rel r) a = ring_quot_to_ideal_quotient r (mk_alg_hom R r a) :=
by rw [← ring_quot_to_ideal_quotient_apply r a, ← mk_alg_hom_coe R r];  refl

end ideals_and_rel

section graded_algebra

variables {R : Type*} [comm_ring R] --[decidable_eq R] -- The linter complains about this instance
variables {A : Type*} [comm_ring A] [algebra R A]
variables {ι : Type*} [decidable_eq ι][add_comm_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]

--def galgA : graded_algebra 𝒜 := infer_instance 
--def decompose : A → direct_sum ι (λ i, 𝒜 i) := (galgA 𝒜).to_decomposition.decompose' 

-- This definition is not used (at least in this file)
/- The canonical map from the graded algebra `A` to the direct sum `⊕ 𝒜 i`. -/
/- def decompose : A → direct_sum ι (λ i, 𝒜 i) := 
(@graded_ring.to_decomposition ι A (submodule R A) _ _ _ _ _ 𝒜 _).decompose'
 -/
--example : has_lift_t (𝒜 0) A := infer_instance
--{ lift := λ x, x.val }

--instance : has_one ↥(𝒜 0) := ⟨⟨1, (galgA 𝒜).to_graded_monoid.one_mem⟩⟩
instance : has_one ↥(𝒜 0) := 
⟨⟨1, (@graded_ring.to_graded_monoid ι A (submodule R A) _ _ _ _ _ 𝒜 _).one_mem⟩⟩

instance : has_mul ↥(𝒜 0) := 
⟨λ x y, ⟨x * y, by convert set_like.mul_mem_graded x.2 y.2; rw [add_zero]⟩⟩

lemma grade_zero_coe_mul (x y : 𝒜 0) : (↑(x * y) : A) = x * y := rfl 

@[simp] lemma grade_zero_val_mul (x y : 𝒜 0) : (x * y).val = x.val * y.val := rfl

@[nolint unused_arguments] -- I don't understand why the linter complains here
lemma grade_zero_coe_smul (r : R) (x : 𝒜 0) :  (↑(r • x) : A) = r • x := rfl 

@[simp] lemma grade_zero_coe_one: (↑(1 : 𝒜 0) : A) = 1 := rfl

lemma one_mem : (1 : A) ∈ 𝒜 0 := set_like.one_mem_graded 𝒜

example : add_comm_monoid (𝒜 0) := infer_instance

example : has_neg (𝒜 0) := add_subgroup_class.has_neg

instance grade_zero_comm_ring : comm_ring ↥(𝒜 0) := { 
  add           := (+),
  zero          := 0,
  neg           := has_neg.neg,
  one           := 1,
  mul           := (*),
  mul_assoc     := λ x y z, by ext; simp only [grade_zero_coe_mul, mul_assoc],
  one_mul       := λ x, by  ext; rw [grade_zero_coe_mul, grade_zero_coe_one, one_mul],
  mul_one       := λ x, by  ext; rw [grade_zero_coe_mul, grade_zero_coe_one, mul_one],
  left_distrib  := λ x y z, 
    by ext; simp only [submodule.coe_add, grade_zero_coe_mul, left_distrib],
  right_distrib := λ x y z, 
    by ext; simp only [submodule.coe_add, grade_zero_coe_mul, right_distrib],
  mul_comm      := λ x y, by ext; simp only [grade_zero_coe_mul, mul_comm],
  ..(infer_instance : add_comm_group (𝒜 0)) }

--example : semiring ↥(𝒜 0) := ring.to_semiring

--example (a : R) : algebra_map R A a = a • 1 := algebra.algebra_map_eq_smul_one a

instance grade_zero_algebra : algebra R ↥(𝒜 0) := algebra.of_module'
  (λ r x, by ext; simp only [grade_zero_coe_mul, grade_zero_coe_smul, grade_zero_coe_one, 
    algebra.smul_mul_assoc, one_mul])
  (λ r x, by ext; simp only [grade_zero_coe_mul, grade_zero_coe_smul, grade_zero_coe_one, 
    algebra.mul_smul_comm, mul_one])


/-- The projection from `A` to the degree `i` component `𝒜 i`, as an `R`-linear map. -/
def proj (i : ι) : A →ₗ[R] (𝒜 i) :=
{ to_fun    := λ a, decompose 𝒜 a i,
  map_add'  := λ a b, by rw [decompose_add, add_apply],
  map_smul' := λ r a, by rw [decompose_smul, dfinsupp.coe_smul, pi.smul_apply, ring_hom.id_apply] }

end graded_algebra
section

/-- The linter complains about these decidable_eq instances. For now I have moved them to later
in the file, but I think more changes will be necessary. -/
variables (R : Type*) [comm_ring R] /- [decidable_eq R] -/ 
variables (M : Type*) /- [decidable_eq M] -/ [add_comm_group M] [module R M]

namespace divided_power_algebra

/-- The type coding the basic relations that will give rise to the divided power algebra. 
  The class of X (n, a) will be equal to dpow n a, with a ∈ M. --/
inductive rel : mv_polynomial (ℕ × M) R → mv_polynomial (ℕ × M) R → Prop
-- force `ι` to be linear and creates the divided powers
| zero {a : M} : rel (X (0, a)) 1
| smul {r : R} {n : ℕ} {a : M} : rel (X (n, r • a)) (r^n • X (n, a))
| mul {m n : ℕ} {a : M} : rel (X (m, a) * X (n, a)) ((nat.choose (m + n) m) • X (m + n, a))
| add {n : ℕ} {a b : M} : rel (X (n, a+b)) 
    (finset.sum (range (n + 1)) (λ k, (X (k, a) * X (n - k, b))))

/-- The ideal of mv_polynomial (ℕ × M) R generated by rel -/
def relI : ideal (mv_polynomial (ℕ × M) R) := ideal.of_rel (rel R M)

end divided_power_algebra

-- Unused now
/- The divided power algebra of a module M is the quotient of the polynomial ring
by the ring relation defined by divided_power_algebra.rel -/
/- @[derive [inhabited, comm_ring, algebra R]]
def divided_power_algebra' := ring_quot (divided_power_algebra.rel R M) -/

/-- The divided power algebra of a module M is the quotient of the polynomial ring
by the ring relation defined by divided_power_algebra.rel -/
@[derive [inhabited, comm_ring, algebra R]]
def divided_power_algebra :=
 (mv_polynomial (ℕ × M) R) ⧸ (divided_power_algebra.relI R M)

lemma divided_power_algebra.algebra' (k : Type*) [comm_ring k] [algebra k R] [module k M][is_scalar_tower k R M] : algebra k (divided_power_algebra R M) :=
ring_hom.to_algebra (ring_hom.comp (algebra_map R (divided_power_algebra R M)) (algebra_map k R))

/-  {k : Type*} [comm_ring k] [algebra k R] [module k M] [is_scalar_tower k R M] 
[algebra k (divided_power_algebra R M)] [is_scalar_tower k R (divided_power_algebra R M)] -/

namespace divided_power_algebra

/- Note that also we don't know yet that `divided_power_algebra R M`
has divided powers, it has a kind of universal property for morphisms to a ring with divided_powers -/

open mv_polynomial

variables {R M}

lemma sub_mem_rel_of_rel (a b) (h : rel R M a b):  a - b ∈ relI R M :=
begin
  rw relI, rw ideal.of_rel,
  apply submodule.subset_span,
  simp only [exists_prop, set.mem_set_of_eq],
  use a, use b, apply and.intro h, simp only [sub_add_cancel], 
end


/-  TO BE DELETED 
-- These two lemmas really belong to some other place
-- because they use of the definition of the ideal relI or divided powers
lemma eval₂_alg_hom_eval_eq {A : Type*} [comm_ring A] [algebra R A] {I : ideal A}
  (hI : divided_powers I) (φ : M →ₗ[R] A) (n : ℕ) (m : M) :
  @eval₂_alg_hom R A (ℕ × M) _ _ _(λ (nm : ℕ × M), hI.dpow nm.1 (φ nm.2)) (X (n, m)) = 
  hI.dpow n (φ m) := 
by simp only [eval₂_alg_hom_apply, ring_hom.to_fun_eq_coe, coe_eval₂_hom, alg_hom.coe_mk, eval₂_X]


lemma eval₂_alg_hom_eq_zero_of_rel {A : Type*} [comm_ring A] [algebra R A] {I : ideal A} 
  (hI : divided_powers I) {φ : M →ₗ[R] A} (hφ : ∀ m, φ m ∈ I) {x : mv_polynomial (ℕ × M) R} 
  (hx : x ∈ relI R M) : eval₂_alg_hom (λ (nm : ℕ × M), hI.dpow nm.1 (φ nm.2)) x = 0 :=
begin
  set f : mv_polynomial (ℕ × M) R →ₐ[R] A := 
  eval₂_alg_hom (λ (nm : ℕ × M), hI.dpow nm.1 (φ nm.2)) with hf,
  suffices : relI R M ≤ ring_hom.ker f, 
  rw ← ring_hom.mem_ker, 
  exact this hx,  
  dsimp only [relI, ideal.of_rel], 
  rw submodule.span_le,
  rintros x ⟨a, b, hx, hab⟩,
  rw ← eq_sub_iff_add_eq at hab, rw hab,
  simp only [set_like.mem_coe, ring_hom.mem_ker, map_sub, sub_eq_zero],
  induction hx with m r n m n p m n u v,
  { rw [eval₂_alg_hom_eval_eq hI, hI.dpow_zero (hφ m), map_one], },
  { simp only [eval₂_alg_hom_eval_eq hI φ, map_smul], 
    simp only [← algebra_map_smul A, smul_eq_mul A],
    rw hI.dpow_smul n (hφ m), 
    simp only [map_pow], },
  { simp only [map_mul, map_nsmul, eval₂_alg_hom_eval_eq hI φ], 
    rw hI.dpow_mul n p (hφ m), 
    rw nsmul_eq_mul, },
  { simp only [map_sum, eval₂_alg_hom_eval_eq hI φ, map_add],
    rw hI.dpow_add n (hφ u) (hφ v), 
    apply congr_arg2 _ rfl,
    ext k,
    simp only [map_mul, eval₂_alg_hom_eval_eq hI φ] },
end
 -/

variable (R)
def dp (n : ℕ) (m : M) : divided_power_algebra R M :=
ideal.quotient.mkₐ R (relI R M) (X (⟨n, m⟩))

lemma dp_zero (m : M) : dp R 0 m = 1 :=
begin
  dsimp [dp], 
  rw ← map_one (ideal.quotient.mk _),  
  rw ideal.quotient.eq,
  rw relI,
  rw ideal.of_rel,
  apply submodule.subset_span,
  simp,
  use X(0,m), use 1,
  split,
  exact rel.zero,
  simp,
end

lemma dp_smul (r : R) (n  : ℕ) (m : M) : dp R n (r • m) = r ^ n • dp R n m :=
begin
  dsimp [dp],
  rw ← ideal.quotient.mkₐ_eq_mk R, 
  rw ← map_smul, 
  rw ideal.quotient.mkₐ_eq_mk R, 
  rw ideal.quotient.eq, 
  apply sub_mem_rel_of_rel,
  exact rel.smul,
end

lemma dp_mul (n p : ℕ) (m : M) : dp R n m * dp R p m = (n + p).choose n • dp R (n + p) m :=
begin
  dsimp [dp],
  rw ← map_mul, 
  rw ← map_nsmul, 
  rw ideal.quotient.eq, 
  apply sub_mem_rel_of_rel,
  exact rel.mul,
end

lemma dp_add (n : ℕ) (x y : M) : dp R n (x + y) = 
(range (n+1)).sum (λ k, dp R k x * dp R (n - k) y) := 
begin
  dsimp [dp],
  simp_rw ←map_mul, rw ←map_sum,  
  rw ideal.quotient.eq, 
  apply sub_mem_rel_of_rel,
  exact rel.add,
end

lemma unique_on_dp {A : Type*} [comm_ring A] [module R A] [algebra R A]
  {f g : divided_power_algebra R M →ₐ[R] A} 
  (h : ∀ n m, f (dp R n m) = g (dp R n m)) :
  f = g := 
begin
  rw fun_like.ext'_iff,
  apply function.surjective.injective_comp_right
    (ideal.quotient.mkₐ_surjective R (relI R M)),
  simp only [←  alg_hom.coe_comp, ← fun_like.ext'_iff], 
  exact mv_polynomial.alg_hom_ext (λ ⟨n, m⟩, h n m),
end

section functoriality

variables (R M)
/- I have taken the proofs out of the definition (Kevin always tells me that definitions in
  tactic mode are a bad idea, because the generated term is sometimes too complicated to
  work with). -/

/- General purpose lifting lemma -/
lemma lift_rel_le_ker {A : Type*} [comm_ring A] [algebra R A]
  (f : ℕ × M → A) (hf_zero : ∀ m, f (0, m) = 1)
  (hf_smul : ∀ (n : ℕ) (r : R) (m : M), f(⟨n, r • m⟩) = r ^ n • f(⟨n, m⟩)) 
  (hf_mul : ∀ n p m, f (⟨n, m⟩) * f (⟨p, m⟩) = ((n + p).choose n) • f (⟨n + p, m⟩))
  (hf_add : ∀ n u v, f (⟨n, u + v⟩) = (range (n + 1)).sum (λ (x : ℕ), f (⟨x, u⟩) * f (⟨n - x, v⟩))):
  relI R M ≤ ring_hom.ker (@eval₂_alg_hom R A (ℕ × M) _ _ _ f) := 
begin
  dsimp only [relI, ideal.of_rel], 
  rw submodule.span_le,
  rintros x ⟨a, b, hx, hab⟩,
  rw ← eq_sub_iff_add_eq at hab, rw hab,
  simp only [set_like.mem_coe, ring_hom.mem_ker, map_sub, sub_eq_zero],
  induction hx with m r n m n p m n u v,

  simp only [hf_zero, eval₂_alg_hom_apply, eval₂_hom_X', eval₂_X, coe_eval₂_hom, eval₂_one, eq_self_iff_true], 

  rw map_smul,
  simp only [eval₂_alg_hom_apply, eval₂_hom_X', hf_smul],

  rw map_nsmul, rw map_mul, 
  simp only [eval₂_alg_hom_apply, eval₂_hom_X', nsmul_eq_mul, hf_mul],

  rw map_sum,
  simp only [eval₂_alg_hom_apply, coe_eval₂_hom, eval₂_mul, eval₂_X, hf_add],
end

/-- General purpose universal property of `divided_power_algebra R M` -/
def lift_aux {A : Type*} [comm_ring A] [algebra R A]
  (f : ℕ × M → A) 
  (hf_zero : ∀ m, f (0, m) = 1) 
  (hf_smul : ∀ (n : ℕ) (r : R) (m : M), f(⟨n, r • m⟩) = r ^ n • f(⟨n, m⟩)) 
  (hf_mul : ∀ n p m, f (⟨n, m⟩) * f (⟨p, m⟩) = ((n + p).choose n) • f (⟨n + p, m⟩))
  (hf_add : ∀ n u v, f (⟨n, u + v⟩) = (range (n + 1)).sum (λ (x : ℕ), f (⟨x, u⟩) * f (⟨n - x, v⟩))) : divided_power_algebra R M →ₐ[R] A :=
ideal.quotient.liftₐ (relI R M) (@eval₂_alg_hom R A (ℕ × M) _ _ _ f) (lift_rel_le_ker R M f hf_zero hf_smul hf_mul hf_add)

lemma lift_aux_eq {A : Type*} [comm_ring A] [algebra R A]
  (f : ℕ × M → A) 
  (hf_zero : ∀ m, f (0, m) = 1) 
  (hf_smul : ∀ (n : ℕ) (r : R) (m : M), f(⟨n, r • m⟩) = r ^ n • f(⟨n, m⟩)) 
  (hf_mul : ∀ n p m, f (⟨n, m⟩) * f (⟨p, m⟩) = ((n + p).choose n) • f (⟨n + p, m⟩))
  (hf_add : ∀ n u v, f (⟨n, u + v⟩) = (range (n + 1)).sum (λ (x : ℕ), f (⟨x, u⟩) * f (⟨n - x, v⟩))) (p : mv_polynomial (ℕ × M) R) :
  lift_aux R M f hf_zero hf_smul hf_mul hf_add 
  (ideal.quotient.mkₐ R (relI R M) p) = 
  eval₂ (algebra_map R A) f p :=
by simp only [lift_aux, ideal.quotient.mkₐ_eq_mk, ideal.quotient.liftₐ_apply, ideal.quotient.lift_mk, alg_hom.coe_to_ring_hom,
  eval₂_alg_hom_apply, coe_eval₂_hom]

lemma lift_aux_eq_X {A : Type*} [comm_ring A] [algebra R A]
  (f : ℕ × M → A) 
  (hf_zero : ∀ m, f (0, m) = 1) 
  (hf_smul : ∀ (n : ℕ) (r : R) (m : M), f(⟨n, r • m⟩) = r ^ n • f(⟨n, m⟩)) 
  (hf_mul : ∀ n p m, f (⟨n, m⟩) * f (⟨p, m⟩) = ((n + p).choose n) • f (⟨n + p, m⟩))
  (hf_add : ∀ n u v, f (⟨n, u + v⟩) = (range (n + 1)).sum (λ (x : ℕ), f (⟨x, u⟩) * f (⟨n - x, v⟩))) (n : ℕ) (m : M) :
  lift_aux R M f hf_zero hf_smul hf_mul hf_add 
  (ideal.quotient.mkₐ R (relI R M) (X (⟨n, m⟩))) = f (⟨n, m⟩) :=
by rw [lift_aux_eq, eval₂_X]


/-- The “universal” property of divided_power_algebra -/
def lift -- {S : Type*} [comm_ring S] [algebra R S] 
  {A : Type*} [comm_ring A] [algebra R A] 
  -- [algebra S A] [is_scalar_tower R S A]
  {I : ideal A} (hI : divided_powers I)
  (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) : divided_power_algebra R M →ₐ[R] A :=
lift_aux R M (λ nm, hI.dpow nm.1 (φ nm.2)) 
(λ m, hI.dpow_zero (hφ m)) 
(λ n r m, by rw [linear_map.map_smulₛₗ, ring_hom.id_apply,
← algebra_map_smul A r (φ m), smul_eq_mul, 
hI.dpow_smul n (hφ m), ← smul_eq_mul, ← map_pow, algebra_map_smul]) 
(λ n p m, by rw [hI.dpow_mul n p (hφ m), ← nsmul_eq_mul]) 
(λ n u v, by rw [map_add, hI.dpow_add n (hφ u) (hφ v)]) 


lemma lift_eqₐ (A : Type*) [comm_ring A] [algebra R A] {I : ideal A} (hI : divided_powers I) 
  (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (p : mv_polynomial (ℕ × M) R) :
  lift R M hI φ hφ (ideal.quotient.mkₐ R (relI R M) p) = 
  eval₂ (algebra_map R A) (λ (nm : ℕ × M), hI.dpow nm.1 (φ nm.2)) p :=
by rw [lift, lift_aux_eq]

lemma lift_eq (A : Type*) [comm_ring A] [algebra R A] {I : ideal A} (hI : divided_powers I) 
  (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (p : mv_polynomial (ℕ × M) R) :
  lift R M hI φ hφ (ideal.quotient.mk (relI R M) p) = 
  eval₂ (algebra_map R A) (λ (nm : ℕ × M), hI.dpow nm.1 (φ nm.2)) p :=
by rw [← ideal.quotient.mkₐ_eq_mk R, lift_eqₐ]

lemma lift_eqₐ_X (A : Type*) [comm_ring A] [algebra R A] {I : ideal A} (hI : divided_powers I) 
  (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (n : ℕ) (m : M) :
  lift R M hI φ hφ (ideal.quotient.mkₐ R (relI R M) (X (n, m))) = hI.dpow n (φ m) :=
by rw [lift, lift_aux_eq_X]

lemma lift_eq_X (A : Type*) [comm_ring A] [algebra R A] {I : ideal A} (hI : divided_powers I) 
  (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (n : ℕ) (m : M) :
  lift R M hI φ hφ (ideal.quotient.mk (relI R M) (X (n, m))) = hI.dpow n (φ m) :=
by rw [← ideal.quotient.mkₐ_eq_mk R, lift_eqₐ_X]

/- Now given an R-algebra S, an S-module N and f : M →ₗ[R] N,
we define 
 divided_power_algebra R M →ₐ[R] divided_power_algebra S N 
 that maps X(n,m) to X(n, f m)
 -/

lemma ideal.quotient.rel_le_ker {R : Type*} [comm_ring R] {S : Type*} [comm_ring S] (I : ideal R) {r : R → R → Prop} (hr : I = ideal.of_rel r) (f : R →+* S)
  (hf : ∀ (a b : R), r a b → f a = f b) : 
  I ≤ f.ker :=
begin
  rw [hr, ideal.of_rel, submodule.span_le],
  rintros x ⟨a, b, hx, hab⟩,  
  rw ← eq_sub_iff_add_eq at hab, 
  rw [hab, set_like.mem_coe, ring_hom.mem_ker, map_sub, sub_eq_zero, hf a b hx],
end

def ideal.quotient.lift_rel {R : Type*} [comm_ring R] {S : Type*} [comm_ring S] (I : ideal R) {r : R → R → Prop} (hr : I = ideal.of_rel r) (f : R →+* S)
  (hf : ∀ (a b : R), r a b → f a = f b) : R ⧸ I →+* S :=
ideal.quotient.lift I f (ideal.quotient.rel_le_ker I hr f hf)

variables {M}
lemma lift'_rel_le_ker (S : Type*) [comm_ring S] [algebra R S] 
  {N : Type*} [add_comm_group N] [module R N] [module S N] [is_scalar_tower R S N] 
  [algebra R (divided_power_algebra S N)] [is_scalar_tower R S (divided_power_algebra S N)]
  (f : M →ₗ[R] N) :
relI R M ≤ ring_hom.ker (@eval₂_alg_hom R _ (ℕ × M) _ _ _ (λ nm, dp S nm.1 (f nm.2))) := 
begin
  dsimp only [relI],
  apply ideal.quotient.rel_le_ker (relI R M) rfl,
  intros a b hab,
  induction hab with m r n m n p m n u v,
  { simp only [coe_eval₂_hom, eval₂_X, eval₂_one],
    rw dp_zero,  },
  { simp only [← eval₂_alg_hom_apply],
    rw map_smul,
    simp only [eval₂_alg_hom_apply, eval₂_hom_X', linear_map.map_smul],
    rw ← algebra_map_smul S r,
    rw ← algebra_map_smul S (r ^ n),  
    rw [dp_smul, map_pow],
    apply_instance, apply_instance, },
  { simp only [coe_eval₂_hom, eval₂_mul, eval₂_X, nsmul_eq_mul], 
    simp only [mv_polynomial.eval₂_eq_eval_map, map_nat_cast, ← nsmul_eq_mul],
    rw dp_mul, },
  { simp only [map_add, coe_eval₂_hom, eval₂_sum, eval₂_mul, eval₂_X],
    rw dp_add, },
end

/-- The functoriality map between divided power algebras associated
with a linear map of the underlying modules -/
def lift' (S : Type*) [comm_ring S] [algebra R S] 
  {N : Type*} [add_comm_group N] [module R N] [module S N] [is_scalar_tower R S N] 
  [algebra R (divided_power_algebra S N)] [is_scalar_tower R S (divided_power_algebra S N)]
  (f : M →ₗ[R] N) : divided_power_algebra R M →ₐ[R] divided_power_algebra S N := 
ideal.quotient.liftₐ (relI R M) _ (lift'_rel_le_ker R S f)

lemma lift'_eq (S : Type*) [comm_ring S] [algebra R S] 
  {N : Type*} [add_comm_group N] [module R N] [module S N] [is_scalar_tower R S N] 
  [algebra R (divided_power_algebra S N)] [is_scalar_tower R S (divided_power_algebra S N)]
  (f : M →ₗ[R] N) (p : mv_polynomial (ℕ × M) R) :
  lift' R S f (ideal.quotient.mk (relI R M) p) = 
  eval₂ (algebra_map R (divided_power_algebra S N)) (λ nm : ℕ × M, dp S nm.1 (f nm.2)) p := 
by rw [lift', ideal.quotient.liftₐ_apply, ideal.quotient.lift_mk, alg_hom.coe_to_ring_hom, eval₂_alg_hom_apply, coe_eval₂_hom]

lemma lift'_eqₐ (S : Type*) [comm_ring S] [algebra R S] 
  {N : Type*} [add_comm_group N] [module R N] [module S N] [is_scalar_tower R S N] 
  [algebra R (divided_power_algebra S N)] [is_scalar_tower R S (divided_power_algebra S N)]
  (f : M →ₗ[R] N) (p : mv_polynomial (ℕ × M) R) :
  lift' R S f (ideal.quotient.mkₐ R (relI R M) p) = 
  eval₂ (algebra_map R (divided_power_algebra S N)) (λ nm : ℕ × M, dp S nm.1 (f nm.2)) p := 
by rw [ideal.quotient.mkₐ_eq_mk, lift'_eq]

end functoriality

variables [decidable_eq R] [decidable_eq M]

variable (M)

instance  : graded_algebra (weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ)) := weighted_graded_algebra _ _

lemma relI_is_homogeneous : (relI R M).is_homogeneous ((weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ))) :=
begin
  dsimp only [relI, ideal.of_rel],
  apply ideal.is_homogeneous_span,
  rintros x ⟨a, b, h, hx⟩,
  rw ← eq_sub_iff_add_eq at hx, rw hx,
  induction h with n r n m n p m n u v,
  { use 0, 
    refine submodule.sub_mem _ _ _;
    rw [mem_weighted_homogeneous_submodule], 
    apply is_weighted_homogeneous_X, 
    apply is_weighted_homogeneous_one, },
  { use n, 
    refine submodule.sub_mem _ _ _,
    rw [mem_weighted_homogeneous_submodule], 
    apply is_weighted_homogeneous_X, 
    refine submodule.smul_mem _ _ _,
    rw [mem_weighted_homogeneous_submodule], 
    apply is_weighted_homogeneous_X, },
  { use n + p, 
    refine submodule.sub_mem _ _ _,
    rw [mem_weighted_homogeneous_submodule], 
    apply is_weighted_homogeneous.mul;
    apply is_weighted_homogeneous_X, 
    refine nsmul_mem _ _,
    rw [mem_weighted_homogeneous_submodule], 
    apply is_weighted_homogeneous_X, },
  { use n,
    refine submodule.sub_mem _ _ _,
    rw [mem_weighted_homogeneous_submodule], 
    apply is_weighted_homogeneous_X, 
    
    refine submodule.sum_mem _ _,
    intros c hc,
    rw [mem_weighted_homogeneous_submodule], 
    have : n = c + (n - c)
    := (nat.add_sub_of_le (finset.mem_range_succ_iff.mp hc)).symm, 
    nth_rewrite 1 this, 
    apply is_weighted_homogeneous.mul;
    apply is_weighted_homogeneous_X, },
end

/-- The graded submodules of `divided_power_algebra R M` -/
def grade := quot_submodule R (weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ)) (divided_power_algebra.relI R M)

/- 
instance : decidable_eq (mv_polynomial (ℕ × M) R ⧸ relI R M) :=
begin
haveI : Π (a b : mv_polynomial (ℕ × M) R), decidable (ideal.quotient.ring_con (relI R M) a b ),
intros a b,
suffices : (ideal.quotient.ring_con (relI R M)) a b ↔ a - b ∈ (relI R M),
rw this,

apply quotient.decidable_eq,
end -/

-- I can't manage to prove the above instance
-- open_locale classical

/-- The canonical decomposition of `divided_power_algebra R M` -/
def decomposition := quot_decomposition R 
(weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ)) (divided_power_algebra.relI R M)
(relI_is_homogeneous R M)

end divided_power_algebra

variables [decidable_eq R] [decidable_eq M]

/-- The graded algebra structure on the divided power algebra-/
def divided_power_galgebra : graded_algebra (divided_power_algebra.grade R M) := 
  graded_quot_alg R 
    (weighted_homogeneous_submodule R (prod.fst : ℕ × M → ℕ)) 
    (divided_power_algebra.relI R M) (divided_power_algebra.relI_is_homogeneous R M)

lemma mv_polynomial.vars_X_subset {R : Type*} {σ : Type*} [decidable_eq σ] (n : σ) [comm_semiring R] :
  (mv_polynomial.X n : mv_polynomial σ R).vars ⊆ {n} := 
begin
  rw X,
  intro u,
  rw mem_vars, 
  rintro ⟨c, hc, hc'⟩,
  simp only [mem_singleton],
  by_contradiction h', 
  simp only [mem_support_iff, coeff_monomial, ne.def] at hc, 
  by_cases h : finsupp.single n 1 = c,
  { rw [← h, finsupp.mem_support_iff, ne.def, finsupp.single_apply] at hc',
    apply hc', rw if_neg (ne.symm h'), },
  { apply hc, rw if_neg h, },
end


namespace divided_power_algebra

variable {M}

lemma surjective_of_supported : function.surjective 
  ((ideal.quotient.mkₐ R (relI R M)).comp (subalgebra.val (mv_polynomial.supported R {nm : ℕ ×M | 0 < nm.1 }))) := 
begin
  intro f, 
  obtain ⟨p',hp'⟩ := ideal.quotient.mk_surjective f,
  have hX : ∀ (nm : ℕ × M), 0 < nm.1 → X nm ∈ mv_polynomial.supported R {nm : ℕ × M | 0 < nm.1},
  { intros nm hnm,
    rw mv_polynomial.mem_supported, 
    refine set.subset.trans (finset.coe_subset.mpr (mv_polynomial.vars_X_subset nm)) _,
    simp only [coe_singleton, set.singleton_subset_iff, set.mem_set_of_eq],
    exact hnm, },
  let φ : mv_polynomial (ℕ × M) R →ₐ[R] mv_polynomial.supported R {nm : ℕ × M | 0 < nm.1} :=  
    mv_polynomial.aeval (λ (nm: ℕ × M), dite (0 < nm.1) (λ h, ⟨(X nm), hX nm h⟩) (λ h, 1)),
  have hφ : (ideal.quotient.mkₐ R (relI R M)).comp ((subalgebra.val _).comp φ) = (ideal.quotient.mkₐ R _),
  { apply mv_polynomial.alg_hom_ext, 
    rintro ⟨n,m⟩,
    simp only [alg_hom.coe_comp, ideal.quotient.mkₐ_eq_mk, subalgebra.coe_val, function.comp_app, aeval_X],
    split_ifs,
    refl,
    simp only [not_lt, le_zero_iff] at h, rw h,
    apply symm,
    simp only [algebra_map.coe_one],
    dsimp only [relI],
    rw quotient_mk_eq_of_rel rel.zero, },
  use φ p',
  rw ← alg_hom.comp_apply, 
  rw alg_hom.comp_assoc, 
  rw [hφ,  ← hp', ideal.quotient.mkₐ_eq_mk],
end

/-- The canonical linear map `M →ₗ[R] divided_power_algebra R M`. -/
def ι : M →ₗ[R] (divided_power_algebra R M) :=
{ to_fun := λ m, (ideal.quotient.mkₐ R _ (X (1, m))),
  map_add' := λ x y, by { 
    rw [← map_add, ideal.quotient.mkₐ_eq_mk],
    dsimp only [relI],
    rw quotient_mk_eq_of_rel rel.add, 
    simp only [sum_range_succ', sum_range_zero, zero_add, nat.sub_zero,
    nat.sub_self], 
    simp only [map_add, map_mul],
    simp only [quotient_mk_eq_of_rel rel.zero],
    simp only [map_one, one_mul, mul_one], },
  map_smul' := λ r x, by { 
    rw [← map_smul, ideal.quotient.mkₐ_eq_mk],
    dsimp only [relI],
    rw [quotient_mk_eq_of_rel rel.smul], 
    simp only [pow_one, ring_hom.id_apply] }}

lemma mk_alg_hom_mv_polynomial_ι_eq_ι (m : M) :
  ideal.quotient.mkₐ R (relI R M) (X (1, m)) = ι R m := rfl

@[simp]
theorem ι_comp_lift {A : Type*} [comm_ring A] [algebra R A] {I : ideal A} (hI : divided_powers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) :
  (lift R M hI φ hφ).to_linear_map.comp (ι R) = φ :=
begin
  ext,
  simp only [linear_map.coe_comp, function.comp_app, alg_hom.to_linear_map_apply, ← mk_alg_hom_mv_polynomial_ι_eq_ι, lift_eqₐ],
  exact hI.dpow_one (hφ x),
end

@[simp]
theorem lift_ι_apply {A : Type*} [comm_ring A] [algebra R A] {I : ideal A} (hI : divided_powers I) (φ : M →ₗ[R] A) (hφ: ∀ m, φ m ∈ I) (x) :
  lift R M hI φ hφ (ι R x) = φ x :=
by { conv_rhs {rw ← ι_comp_lift R hI φ hφ,},refl, }

variable {R}
def degree (v : (ℕ × M) →₀ ℕ) : ℕ := finsum (λ x, (v x) * x.1)

def is_homogeneous_of_degree (p : mv_polynomial (ℕ × M) R) (n : ℕ) : Prop :=
∀ v ∈ p.support, degree v = n 

variables (R M)

/-- The degree-n submodule of the divided power algebra -/
def grade' (n : ℕ) : submodule R (divided_power_algebra R M) :=
submodule.span R 
  { u : divided_power_algebra R M | ∃ p : mv_polynomial (ℕ × M) R,
    (is_homogeneous_of_degree p n ∧ ideal.quotient.mkₐ R (relI R M) p = u) }

-- instance : module R (direct_sum ℕ (λ (i : ℕ), ↥(grade R M i))) := infer_instance

lemma one_mem : (1 : divided_power_algebra R M) ∈ grade R M 0 := begin
  refine ⟨1, _, rfl⟩,
  simp only [set_like.mem_coe, mem_weighted_homogeneous_submodule, is_weighted_homogeneous_one], 
end

/-
submodule.subset_span ⟨C 1, 
  ⟨λ v hv, 
  begin
    classical,
    suffices hv : v = 0,
    simp only [hv, degree, finsupp.coe_zero, pi.zero_apply, zero_mul, finsum_zero],   
    { apply symm,
      by_contradiction hv', 
      simp only [mem_support_iff, mv_polynomial.coeff_C, if_neg hv'] at hv,
      apply hv, refl,},
  end,
  by simp only [map_one]⟩⟩
-/

/-- degree of a product is sum of degrees -/
lemma mul_mem ⦃i j : ℕ⦄ {gi gj : divided_power_algebra R M} (hi : gi ∈ grade R M i)
  (hj : gj ∈ grade R M j) : gi * gj ∈ grade R M (i + j) :=
(divided_power_galgebra R M).to_graded_monoid.mul_mem hi hj

 /-
  revert gj,
  apply submodule.span_induction hi,
  { intros x hx gj hj,
    apply submodule.span_induction hj,
    { intros y hy,
      obtain ⟨p, hp, rfl⟩ := hx,
      obtain ⟨q, hq, rfl⟩ := hy,
      apply submodule.subset_span,
      use p * q, 
      split,
      intros w hw,
      let hw' := mv_polynomial.support_mul p q hw, 
      simp only [mem_bUnion] at hw', 
      obtain ⟨u, hu, v, hv, huv⟩ := hw', 
      simp only [mem_singleton] at huv, 
      rw [huv, degree, ← hp u hu, ← hq v hv, degree, degree, ← finsum_add_distrib],
      apply finsum_congr, 
      intro x, 
      simp only [finsupp.coe_add, pi.add_apply], 
      rw add_mul, 
      -- finiteness assumptions
      apply set.finite.subset u.support.finite_to_set _, 
      intro i, 
      simp only [function.mem_support, mem_coe, finsupp.mem_support_iff, ne.def],
      intros hui hi, apply hui, rw [hi, zero_mul],
      -- finiteness assumptions
      apply set.finite.subset v.support.finite_to_set _, 
      intro i, 
      simp only [function.mem_support, mem_coe, finsupp.mem_support_iff, ne.def],
      intros hvi hi, apply hvi, rw [hi, zero_mul],
      --
      simp only [map_mul], },
    { rw mul_zero, exact zero_mem _, },
    { intros y z hxy hxz,
      rw left_distrib,
      exact add_mem hxy hxz },
    { intros r y hxy,
      rw mul_smul_comm,
      exact submodule.smul_mem _ r hxy,}},
  { intros gj hj,
    rw zero_mul, exact zero_mem _, },
  { intros x y hx hy gj hj,
    rw right_distrib,
    exact add_mem (hx hj) (hy hj), },
  { intros r x hx gj hj,
    rw smul_mul_assoc,
    exact submodule.smul_mem _ _ (hx hj) },
    -/

/- The initial version 

def grade' (n : ℕ) : submodule R (divided_power_algebra R M) :=
submodule.span R 
  { u : divided_power_algebra R M | ∃ (s : multiset (ℕ × M)) 
    (hs : (s.map (λ x : ℕ × M, x.1)).sum = n),
    (s.map (λ x, mk_alg_hom R (rel R M) (X x))).prod = u }

lemma one_mem' : (1 : divided_power_algebra R M) ∈ grade' R M 0 := 
submodule.subset_span ⟨{(0, 0)}, by rw [multiset.map_singleton, multiset.sum_singleton], 
  by { rw [multiset.map_singleton, multiset.prod_singleton, 
    ← map_one (mk_alg_hom R (rel R M)), mk_alg_hom_rel R rel.zero]}⟩

lemma mul_mem' ⦃i j : ℕ⦄ {gi gj : divided_power_algebra R M} (hi : gi ∈ grade' R M i)
  (hj : gj ∈ grade' R M j) : gi * gj ∈ grade' R M (i + j) :=
begin
  revert gj,
  apply submodule.span_induction hi,
  { intros x hx gj hj,
    apply submodule.span_induction hj,
    { intros y hy,
      obtain ⟨s, hs, rfl⟩ := hx,
      obtain ⟨t, ht, rfl⟩ := hy,
      rw [← multiset.prod_add, ← multiset.map_add],
      apply submodule.subset_span,
      exact ⟨s + t, by rw [multiset.map_add, multiset.sum_add, hs, ht], rfl⟩,},
    { rw mul_zero, exact zero_mem _, },
    { intros y z hxy hxz,
      rw left_distrib,
      exact add_mem hxy hxz },
    { intros r y hxy,
      rw mul_smul_comm,
      exact submodule.smul_mem _ r hxy,}},
  { intros gj hj,
    rw zero_mul, exact zero_mem _, },
  { intros x y hx hy gj hj,
    rw right_distrib,
    exact add_mem (hx hj) (hy hj), },
  { intros r x hx gj hj,
    rw smul_mul_assoc,
    exact submodule.smul_mem _ _ (hx hj) },
end

def f :  R →+ (direct_sum ℕ (λ (i : ℕ), ↥(grade R M i))) := sorry

def decompose'' : ℕ × M → direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)) :=
λ x,  direct_sum.of (λ n, grade R M n) x.1  
  (⟨ring_quot.mk_alg_hom R (rel R M) (X x), submodule.subset_span ⟨{x},
    by rw [multiset.map_singleton, multiset.sum_singleton],
    by rw [multiset.map_singleton, multiset.prod_singleton]⟩⟩ : (grade R M x.1))

-/

/-
/-- Split the class of a polynomial into its components of various degrees -/
def decompose' : mv_polynomial (ℕ × M) R → direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)) := λ p, 
  -- p = p.support.sum (λ (v : ℕ × M →₀ ℕ), ⇑(monomial v) (coeff v p))
  p.support.sum
    (λ (v : ℕ × M →₀ ℕ), 
    direct_sum.of (λ n, grade R M n) 
    (finsum (λ x : ℕ × M, (v x) * x.1))
    (⟨ring_quot.mk_alg_hom R (rel R M) (monomial v (coeff v p)), 
      begin
        apply submodule.subset_span,
        use monomial v (coeff v p), 
        split,
        { intros v' hv', 
          suffices : v' = v, rw [degree, this], 
          rw [← finset.mem_singleton], 
          exact mv_polynomial.support_monomial_subset hv', },
        refl,
     end⟩))

  /- p.support : finset ((ℕ × M) →₀ ℕ)
    si v ∈ p.support, le monôme v est prod ("dpow n m")^(v (n, m))
    son degré est finsum (λ x, x.1 * (v x))
  -- p.coeff : ((ℕ × M) →₀ ℕ) → R
  -- p is a lift of sum (coeff v p) • prod ("dpow n m")^(v (n, m))
  -- dpow n m vit en degré n
  -- (prod ("dpow n m")^(v (n,m))) vit en degré finsum (ℕ × M) (λ x, v x * x.1)
  -/

  /-
  refine p.sum _ ,
  intros s a,
  refine direct_sum.mk (λ n, grade R M n) s.frange (λ m, _),
  obtain ⟨m, hm⟩ := m,
  simp only [mem_coe] at hm,
  rw finsupp.mem_frange at hm,
  
  --exact p.sum (λs a, f a * s.prod (λ n e, decompose'' n ^ e))
  --change add_monoid_algebra R ((ℕ × M)  →₀ ℕ) →+ direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)),
  --refine add_monoid_algebra.lift_nc  _ (decompose'' R M),
  --intro x,
  --apply direct_sum.mk,
  sorry-/

def take_degree (p : mv_polynomial (ℕ ×M) R) (n : ℕ) :
  finset (ℕ × M →₀ ℕ) := 
  p.support.filter (λ v, finsum (λ x : ℕ × M, (v x) * x.1) = n)

lemma decompose'_eq (p: mv_polynomial (ℕ × M) R) (n : ℕ) :
  (decompose' R M p n : divided_power_algebra R M) = 
  ring_quot.mk_alg_hom R (rel R M) 
  ((p.support.filter 
    (λ v : (ℕ × M) →₀ ℕ, finsum (λ x : ℕ × M, (v x) * x.1) = n )).sum 
    (λ v, monomial v (coeff v p))) := 
begin
  classical,
  unfold decompose',
  
  induction p using mv_polynomial.induction_on' with v c p q hp hq,
  { -- case of monomials
    rw finset.sum_eq_single v,
    -- basic equality
    by_cases hn : finsum (λ x : ℕ × M, (v x) * x.1) = n,
    { rw ← hn,
      rw direct_sum.of_eq_same, 
      simp only [subtype.coe_mk], 
      apply congr_arg, 
      rw finset.sum_eq_single v, 
      intros w hw hw', 
      rw finset.mem_filter at hw, 
      rw mv_polynomial.monomial_eq_zero, rw mv_polynomial.coeff_monomial w v c, 
      rw if_neg, intro h, exact hw' h.symm, 
      --
      simp only [filter_true_of_mem, mem_support_iff, coeff_monomial, ne.def, ite_eq_right_iff, not_forall, exists_prop, and_imp,
  forall_eq', eq_self_iff_true, implies_true_iff, if_true, not_not, monomial_eq_zero, imp_self], },
    { rw direct_sum.of_eq_of_ne, 
      simp only [submodule.coe_zero, coeff_monomial], 
      apply symm, convert map_zero _, 
      convert finset.sum_empty, 
      rw finset.eq_empty_iff_forall_not_mem,
      intros w hw, rw finset.mem_filter at hw,  
      apply hn,
      suffices : w = v, rw ← this, exact hw.2,
      rw ← finset.mem_singleton, 
      exact mv_polynomial.support_monomial_subset hw.1, 
      --
      exact hn,  }, 
    -- support condition 
    intros w hw hwv, 
    ext m, 
    rw direct_sum.zero_apply , 
    rw subtype.coe_inj,
    by_cases hm : m = finsum (λ x, w x * x.1),
    { rw hm,
      rw direct_sum.of_eq_same,
      simp only [coeff_monomial, submodule.mk_eq_zero],
      rw if_neg,
      simp only [map_zero],
      { intro h, exact hwv h.symm }, },
    { rw direct_sum.of_eq_of_ne,
      intro h, exact hm h.symm, },

    -- second support condition
    unfold direct_sum.of, 
    simp only [mem_support_iff, not_not, dfinsupp.single_add_hom_apply, dfinsupp.single_eq_zero],
    intro hv, simp_rw hv, 
    simp only [map_zero, submodule.mk_eq_zero], }, 
  sorry
end

lemma not_mem_monomial_support (n : ℕ) (v : ℕ × M →₀ ℕ) (c : R) :
v ∉ ((monomial v) c).support
↔ c = 0  := 
begin
  classical,
rw [mv_polynomial.not_mem_support_iff, mv_polynomial.coeff_monomial], 
simp only [eq_self_iff_true, if_true], 
end


lemma decompose_rel' (a b : mv_polynomial (ℕ × M) R) (hab : ring_quot.rel (rel R M) a b) :
  decompose' R M a = decompose' R M b :=
begin
  induction hab with a b hab a b c h ih a b c h ih a b c h ih,
  { -- rel 
    induction hab with m c n m n p m n m m', 
    { unfold decompose',
    
    
    sorry },
    { sorry },
    { sorry },
    { sorry } },
  { sorry },
  { sorry },
  { sorry },


end
-/

def decompose : divided_power_algebra R M → direct_sum ℕ (λ (i : ℕ), ↥(grade R M i)) :=
(divided_power_galgebra R M).to_decomposition.decompose'

/- graded_algebra (grade R M )-/
instance : graded_algebra (divided_power_algebra.grade R M) := divided_power_galgebra R M

example : algebra R (grade R M 0) := infer_instance

/- NOW WRITTEN ABOVE, IN GENERAL CASE OF GRADED ALGEBRAS 
-- Why doesn't Lean find this instance?
instance : has_lift_t ↥(grade R M 0) (divided_power_algebra R M) := { lift := λ x, x.val }

instance : has_one (grade R M 0) := ⟨⟨1, one_mem R M ⟩⟩

instance : has_mul (grade R M 0) := 
{ mul := λ x y, ⟨x*y, by convert mul_mem R M x.2 y.2⟩ }

@[simp] lemma grade_zero_coe_mul (x y : grade R M 0) :
  (↑(x * y) : divided_power_algebra R M) = (↑x : divided_power_algebra R M) * ↑y := rfl

@[simp] lemma grade_zero_val_mul (x y : grade R M 0) :
  (↑(x * y) : divided_power_algebra  R M) = (↑x) * ↑y := rfl

@[simp] lemma grade_zero_coe_one: (↑(1 : grade R M 0) : divided_power_algebra R M) = 1 := rfl

instance : add_comm_monoid (grade R M 0) := infer_instance

instance : has_neg (grade R M 0) := add_subgroup_class.has_neg

instance : comm_ring (grade R M 0) := 
{ add           := (+),
  zero          := 0,
  neg           := has_neg.neg,
  one           := 1,
  mul           := (*),
  mul_assoc     := λ x y z, by ext; simp only [grade_zero_coe_mul, mul_assoc],
  one_mul       := λ x, by  ext; rw [grade_zero_coe_mul, grade_zero_coe_one, one_mul],
  mul_one       := λ x, by  ext; rw [grade_zero_coe_mul, grade_zero_coe_one, mul_one],
  left_distrib  := λ x y z, 
  by ext; simp only [submodule.coe_add, grade_zero_coe_mul, left_distrib],
  right_distrib := λ x y z, 
    by ext; simp only [submodule.coe_add, grade_zero_coe_mul, right_distrib],
  mul_comm      := λ x y, by ext; simp only [grade_zero_coe_mul, mul_comm],
  ..(infer_instance : add_comm_group (grade R M 0)), }

instance : algebra R (grade R M 0) := 
{ to_fun := λ a, ⟨algebra_map R (divided_power_algebra R M) a, begin use (algebra_map R _ a), split, sorry, refl,  end ⟩, 
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry, 
  commutes' := sorry,
  smul_def' := sorry, } 
  
  
  -/


def galg_hom.is_homogeneous {ι : Type*} [add_comm_monoid ι] [decidable_eq ι]
  {A : Type*} [comm_ring A] [algebra R A] (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
  {B : Type*} [comm_ring B] [algebra R B] (ℬ : ι → submodule R B) [graded_algebra ℬ] 
  (f : A →ₐ[R] B):= ∀ i a, a ∈ 𝒜 i → f a ∈ ℬ i 

/- 
def gmodule_hom.is_homogeneous {ι : Type*} [decidable_eq ι]
  {M : Type*} [add_comm_group M] [module R M] (ℳ : ι → submodule R M) [graded_module ℳ]
  {N : Type*} [add_comm_group N] [module R N] (𝒩 : ι → submodule R N) [graded_module 𝒩] 
  (f : M →ₗ[R] N):= ∀ i m, m ∈ ℳ i → f n ∈ 𝒩 i 

example {ι : Type*} [add_comm_monoid ι] [decidable_eq ι]
  {A : Type*} [comm_ring A] [algebra R A] (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
  {B : Type*} [comm_ring B] [algebra R B] (ℬ : ι → submodule R B) [graded_algebra ℬ] 
  (f : A →ₐ[R] B) : 
   f.is_homogeneous 𝒜 ℬ ↔ f.to_linear_map.is_homogeneous 𝒜 ℬ :=
begin

end
 -/

lemma finsupp.prod.mem_grade {A : Type*} [comm_ring A] [algebra R A] 
  (𝒜 : ℕ → submodule R A) [graded_algebra 𝒜] 
  {σ : Type*} [decidable_eq σ] (c : σ →₀ ℕ) (f : σ → A) (d : σ → ℕ)
  (hc : ∀ s ∈ c.support, f s ∈ 𝒜 (d s)): 
  c.prod (λ s e, (f s) ^ e) ∈ 𝒜 (c.sum (λ s e, e * d s)) := 
begin
  rw finsupp.prod, rw finsupp.sum,
  let p : finset σ → Prop := λ s, s ⊆ c.support → (s.prod (λ i, (f i) ^ c i) ∈ 𝒜 (s.sum (λ i, c i * d i))),

  apply @finset.induction_on σ p _ c.support,

  dsimp [p], apply imp_intro,
  exact set_like.one_mem_graded 𝒜, 

  intros a s ha hs,
  by_cases hs' : (insert a s) ⊆ c.support,  
  { apply imp_intro,
    rw finset.prod_insert ha,
    rw finset.sum_insert ha,
    apply set_like.mul_mem_graded,
    rw ← smul_eq_mul ℕ, 
    apply set_like.pow_mem_graded,
    exact hc a (hs' (mem_insert_self a s)),
    exact hs (subset_trans (subset_insert a s) hs'), },
  { apply not.elim, exact hs', },

  exact subset_rfl,
end


lemma lift_aux_is_homogeneous {A : Type*} [comm_ring A] [algebra R A] 
  (𝒜 : ℕ → submodule R A) [graded_algebra 𝒜]
  (f : ℕ × M → A) 
  (hf_zero : ∀ m, f (0, m) = 1) 
  (hf_smul : ∀ (n : ℕ) (r : R) (m : M), f(⟨n, r • m⟩) = r ^ n • f(⟨n, m⟩)) 
  (hf_mul : ∀ n p m, f (⟨n, m⟩) * f (⟨p, m⟩) = ((n + p).choose n) • f (⟨n + p, m⟩))
  (hf_add : ∀ n u v, f (⟨n, u + v⟩) = (range (n + 1)).sum (λ (x : ℕ), f (⟨x, u⟩) * f (⟨n - x, v⟩))) 
  (hf : ∀ n m, f (n, m) ∈ 𝒜 n) : 
  galg_hom.is_homogeneous R (divided_power_algebra.grade R M) 𝒜 (lift_aux R M f hf_zero hf_smul hf_mul hf_add) := 
begin
  dsimp only [galg_hom.is_homogeneous],
  intros i a ha,
  dsimp [grade, quot_submodule] at ha,
  obtain ⟨p, hp, rfl⟩ := ha, 
  rw ← ideal.quotient.mkₐ_eq_mk R, rw lift_aux_eq,

  rw mv_polynomial.as_sum p,
  rw eval₂_sum,
  apply sum_mem,
  intros c hc, 
  rw [eval₂_monomial, ← smul_eq_mul, algebra_map_smul A],
  apply submodule.smul_mem, 
  rw is_weighted_homogeneous at hp,
  rw mem_support_iff at hc,
  specialize hp hc,
  suffices : i = c.sum (λ nm e, e * nm.fst), rw this,
  apply finsupp.prod.mem_grade,

  rintros ⟨n,m⟩ hnm, exact hf n m,

  rw ←hp,  refl,

  apply_instance, 
end

variable {R}
def has_graded_dpow {A : Type*} [comm_ring A] [algebra R A] 
  (𝒜 : ℕ → submodule R A) [graded_algebra 𝒜]
  {I : ideal A} (hI : divided_powers I) := ∀ (a : A) (ha : a ∈ I) 
  (i : ℕ) (hai : a ∈ 𝒜 i) (n : ℕ),  hI.dpow n a ∈ 𝒜 (n • i)
  
lemma lift_is_homogeneous {A : Type*} [comm_ring A] [algebra R A] 
  (𝒜 : ℕ → submodule R A) [graded_algebra 𝒜]
  {I : ideal A} (hI : divided_powers I) 
  (hI' : has_graded_dpow 𝒜 hI)
  (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (hφ' : ∀ m, φ m ∈ 𝒜 1) : 
  galg_hom.is_homogeneous R (divided_power_algebra.grade R M) 𝒜
    (lift R M hI φ hφ) := 
begin
  rw [lift],
  apply lift_aux_is_homogeneous,
  intros n m,
  dsimp only,
  simpa only [algebra.id.smul_eq_mul, mul_one] using hI' (φ m) (hφ m) 1 (hφ' m) n,
end

lemma lift'_is_homogeneous 
  {N : Type*} [decidable_eq N] [add_comm_group N] [module R N] 
  (f : M →ₗ[R] N) :
  galg_hom.is_homogeneous R (divided_power_algebra.grade R M) (divided_power_algebra.grade R N) (lift' R R f) := 
begin
  simp only [lift'],
  apply lift_aux_is_homogeneous,
  -- Because lift' does not use lift_aux, we have to reprove stuff…
  intro m, rw dp_zero,
  intros n r m, simp only [linear_map.map_smul], rw dp_smul,
  intros n p m, rw dp_mul, 
  intros n u v, dsimp only, rw map_add, apply dp_add R,
  intros n m, dsimp only [grade, quot_submodule, submodule.mem_map],
    use X(n, f m),
    split,
    simp only [mem_weighted_homogeneous_submodule],
    apply is_weighted_homogeneous_X,
    refl,
end

/- We need the projections (divided_power_algebra R M) → grade R M n ,
more generally for graded algebras -/

instance : add_submonoid_class (submodule R (mv_polynomial (ℕ × M) R ⧸ relI R M)) (divided_power_algebra R M) := submodule.add_submonoid_class

def proj' (n : ℕ) : divided_power_algebra R M →ₗ[R] grade R M n := 
proj (grade R M) n

section grade_zero

-- variables {R M}
def algebra_map_inv : divided_power_algebra R M →ₐ[R] R :=
lift R M (divided_powers.of_square_zero.divided_powers (by rw [ideal.zero_eq_bot, pow_two, ideal.bot_mul])) (0 : M →ₗ[R] R) (λ m, by simp only [linear_map.zero_apply, ideal.zero_eq_bot, ideal.mem_bot])

lemma algebra_map_inv_eq (f : mv_polynomial (ℕ × M) R) : 
  algebra_map_inv R M (ideal.quotient.mkₐ R (relI R M) f) =
  mv_polynomial.aeval (λ nm : ℕ × M, ite (0 < nm.1) (0 : R) 1) f :=
begin
  rw ← alg_hom.comp_apply, 
  apply alg_hom.congr_fun,
  refine mv_polynomial.alg_hom_ext _,
  rintro ⟨n,m⟩,
  rw [algebra_map_inv, alg_hom.comp_apply, lift_eqₐ],
  simp only [linear_map.zero_apply, aeval_X],
  by_cases hn : 0 < n,
  rw if_pos hn,
  rw ← ideal.mem_bot,
  refine divided_powers.dpow_mem _ _ _, 
  exact ne_of_gt hn,
  exact ideal.mem_bot.mpr rfl,
  rw if_neg hn,
  simp only [not_lt, le_zero_iff] at hn,
  rw hn,
  refine divided_powers.dpow_zero _ _,
  exact ideal.mem_bot.mpr rfl,
end

-- variables (M) 
lemma algebra_map_left_inverse :
  function.left_inverse (algebra_map_inv R M) (algebra_map R (divided_power_algebra R M)) := λ m, by simp only [alg_hom.commutes, algebra.id.map_eq_id, ring_hom.id_apply]

@[simp] lemma algebra_map_inj (x y : R) :
  algebra_map R (divided_power_algebra R M) x = algebra_map R (divided_power_algebra R M) y ↔ x = y :=
(algebra_map_left_inverse R M).injective.eq_iff

@[simp] lemma algebra_map_eq_zero_iff (x : R) : algebra_map R (divided_power_algebra R M) x = 0 ↔ x = 0 :=
map_eq_zero_iff (algebra_map _ _) (algebra_map_left_inverse _ _).injective

@[simp] lemma algebra_map_eq_one_iff (x : R) : algebra_map R (divided_power_algebra R M) x = 1 ↔ x = 1 :=
map_eq_one_iff (algebra_map _ _) (algebra_map_left_inverse _ _).injective

/-- An ideal J of a commutative ring A is an augmentation ideal
if ideal.quotient.mk J has a right inverse which is a ring_hom -/
def is_augmentation_ideal (A : Type*) [comm_ring A] (J : ideal A) : Prop :=
∃ g : A⧸J →+* A, (ideal.quotient.mk J) ∘ g = id

/-- The augmentation ideal in the divided_power_algebra -/
def aug_ideal : ideal (divided_power_algebra R M) := ring_hom.ker (algebra_map_inv R M)

lemma mem_aug_ideal_iff (f : divided_power_algebra R M) : 
  f ∈ aug_ideal R M ↔ algebra_map_inv R M f = 0 :=
by rw [aug_ideal, ring_hom.mem_ker]

/-- The image of ι is contained in the augmentation ideal -/
lemma ι_mem_aug_ideal (m : M) : (ι R) m ∈ aug_ideal R M :=
begin
  rw [mem_aug_ideal_iff, ι],
  simp only [linear_map.coe_mk, algebra_map_inv_eq, aeval_X, nat.lt_one_iff, eq_self_iff_true, if_true], 
end

/- We prove that the augmentation is an augmentation ideal, namely there is a section -/
lemma aug_ideal_is_augmentation_ideal : is_augmentation_ideal (divided_power_algebra R M) (aug_ideal R M) :=
begin
  rw is_augmentation_ideal,
  let g := ideal.ker_lift_alg (algebra_map_inv R M),
  let g1 := algebra_map R (divided_power_algebra R M ⧸ aug_ideal R M),
  use (algebra_map R (divided_power_algebra R M)).comp g.to_ring_hom, 
  ext x, 
  simp only [ideal.ker_lift_alg_to_ring_hom, ring_hom.coe_comp, function.comp_app, ideal.quotient.mk_algebra_map, id.def],
  suffices : function.right_inverse g g1, 
  exact this x, 
  apply function.right_inverse_of_injective_of_left_inverse,
  exact ring_hom.ker_lift_injective _,
  intro r, simp only [alg_hom_class.commutes, algebra.id.map_eq_id, ring_hom.id_apply],
end 

/- THE FOLLOWING LINES AIM AT PROVING THAT THE AUGMENTATION IDEAL
IS GENERATED BY X(n,m) for n > 0 
FOR THE MOMENT, I CAN'T CONCLUDE. 
ROBY MENTIONS IT WITHOUT PROOF  -/
/- example (c : R) : (algebra_map_inv R M) ((ideal.quotient.mkₐ R (relI R M)) (C c)) = c :=
begin
rw ←mv_polynomial.algebra_map_eq , 
simp only [alg_hom_class.commutes, algebra.id.map_eq_id, ring_hom.id_apply], 
end

-- X (n,m) -> 0 si n > 0
example (n : ℕ) (m : M) (hn : 0 < n): 
  algebra_map_inv R M (ideal.quotient.mkₐ R _ (X(n,m))) = 0 := 
begin
  rw [algebra_map_inv, lift_eqₐ R M, linear_map.zero_apply, divided_powers.dpow_eval_zero],
  exact ne_of_gt hn,
end

-- X (0,m) -> 1
example (m : M) : 
  algebra_map_inv R M (ideal.quotient.mkₐ R _ (X(0,m))) = 1 := 
begin
  rw [algebra_map_inv, lift_eqₐ R M, linear_map.zero_apply],
  rw divided_powers.dpow_zero,
  rw ideal.mem_bot,
end

lemma algebra_map_inv_apply (nm : ℕ × M) : algebra_map_inv R M (ideal.quotient.mkₐ R _ (X (nm))) = ite (nm.1 = 0) 1 0 :=
begin
  dsimp [algebra_map_inv, lift], 
  simp only [eval₂_X],
  by_cases h : nm.1 = 0,
  { rw [if_pos h, h],
    rw divided_powers.dpow_zero _ _,
    rw ideal.mem_bot,},
  { rw [if_neg h], 
    rw divided_powers.dpow_eval_zero _ h, }
end

lemma algebra_map_inv_of_monomial (q : ℕ × M →₀ ℕ) (c : R) :
  algebra_map_inv R M 
    (ideal.quotient.mkₐ R _ (monomial q c)) = 
    ite (∀ (x : ℕ × M), x ∈q.support → x.1 = 0) c 0 := 
begin
  rw mv_polynomial.monomial_eq , 
  simp only [map_mul],
  rw ←mv_polynomial.algebra_map_eq , 
  simp only [alg_hom_class.commutes, algebra.id.map_eq_id, ring_hom.id_apply], 

  rw finsupp.prod, simp only [map_prod],
  simp_rw [map_pow, algebra_map_inv_apply, ite_pow, one_pow],

  split_ifs,
  { convert mul_one c,
    apply finset.prod_eq_one,
    intros x hx, 
    rw if_pos (h x hx), },
  { convert mul_zero c,
    push_neg at h,
    obtain ⟨a, haq, ha'⟩ := h,
    rw finset.prod_eq_zero haq,
    rw if_neg ha', 
    apply zero_pow, 
    simpa only [finsupp.mem_support_iff, ← zero_lt_iff] using haq, },
end

lemma algebra_map_inv_mkₐ (f : mv_polynomial (ℕ × M) R) : 
  algebra_map_inv R M (ideal.quotient.mkₐ R _ f) =  
(filter (λ (x : ℕ × M →₀ ℕ), ∀ (x_1 : ℕ × M), x_1 ∈ x.support → x_1.fst = 0) f.support).sum
  (λ (x : ℕ × M →₀ ℕ), coeff x f) :=
begin
  conv_lhs { rw f.as_sum, },
  rw [map_sum (ideal.quotient.mkₐ R _)],
  rw map_sum,
  have h : ∀ (x : ℕ × M →₀ ℕ), x ∈ f.support →  _ = ite _ (coeff x f) 0,
  intros q hq, exact algebra_map_inv_of_monomial R M q (coeff q f), 
  rw finset.sum_congr rfl h,
  rw finset.sum_ite , 
  convert add_zero _,
  apply finset.sum_eq_zero,
  intros x hx, 
  refl,
end

open_locale classical

example {A : Type*} [comm_ring A] [algebra R A] {σ : Type*} (f g : mv_polynomial σ R →ₐ[R] A) : f = g ↔ ∀ s, f (X s) = g (X s) :=
begin
  split,
  intros hfg s, rw hfg, 
exact mv_polynomial.alg_hom_ext , 
end

example {A : Type*} [comm_ring A] [algebra R A] {σ : Type*} (f : mv_polynomial σ R →ₐ[R] A) : f = mv_polynomial.aeval (λ s, f (X s)) :=
begin
  apply mv_polynomial.alg_hom_ext , 
  intros s,
  simp only [aeval_X],
end -/



lemma aug_ideal_eq_span : ideal.span (set.image (λ nm, ideal.quotient.mk _ (X nm)) { nm : ℕ × M | 0 < nm.1 }) = aug_ideal R M := 
begin
  apply le_antisymm,
  { rw ideal.span_le, 
    intros f,
    simp only [ideal.quotient.mk_eq_mk, set.mem_image, set.mem_set_of_eq, prod.exists, exists_and_distrib_left, set_like.mem_coe,
  forall_exists_index, and_imp],
    intros n hn m,
    intro hf, 
    rw ← hf,
    simp only [aug_ideal, ring_hom.mem_ker, algebra_map_inv, lift_eq, linear_map.zero_apply],
    rw divided_powers.dpow_eval_zero,
    exact ne_of_gt hn, },
  { intros f0, 
    obtain ⟨⟨f, hf⟩, rfl⟩ := divided_power_algebra.surjective_of_supported R f0,
    intro hf0,
    simp only [alg_hom.coe_comp, ideal.quotient.mkₐ_eq_mk, subalgebra.coe_val, function.comp_app, set_like.coe_mk] at hf0 ⊢, -- rw subtype.coe_mk at hf0 ⊢,
    rw set.image_comp, 
    rw ← ideal.map_span (ideal.quotient.mk (relI R M)),
    apply ideal.mem_map_of_mem,
    suffices : coeff 0 f = 0,
    rw mv_polynomial.as_sum f,
    refine ideal.sum_mem _ _,
    intros c hc, 
    rw [mv_polynomial.mem_supported] at hf,
    -- since the coeff c f is nonzero by hc, this is inoccuous
    rw mv_polynomial.monomial_eq,
    refine ideal.mul_mem_left _ _ _,
    rw finsupp.prod,
    suffices that : ↑(c.support) ⊆ {nm : ℕ × M | 0 < nm.fst},
    by_cases hc0 : c.support.nonempty,
    { obtain ⟨nm, hnm⟩ := hc0, 
      rw finset.prod_eq_mul_prod_diff_singleton hnm,
      refine ideal.mul_mem_right _ _ _ ,
  --     rw finsupp.mem_support_iff at hnm,
      obtain ⟨k, hk⟩ := nat.exists_eq_succ_of_ne_zero (finsupp.mem_support_iff.mp hnm),
      rw [hk, pow_succ],
      refine ideal.mul_mem_right _ _ _ ,
      apply ideal.subset_span, 
      use nm, 
      refine and.intro _ rfl,
      simp only [set.mem_set_of_eq],
      apply that,
      simp only [mem_coe], 
      exact hnm, }, 
    { -- cas où c.support est vide : c = 0 ; contradiction
      simp only [not_nonempty_iff_eq_empty, finsupp.support_eq_empty] at hc0,
      exfalso,
      rw hc0 at hc, simp only [mem_support_iff, ne.def] at hc, 
      exact hc this, },

    { -- that 
      intros nm hnm, 
      apply hf, 
      simp only [mv_polynomial.mem_vars, mem_coe, mem_support_iff, ne.def, finsupp.mem_support_iff, exists_prop],
      simp only [mem_coe, finsupp.mem_support_iff, ne.def] at hnm,
      simp only [mem_support_iff, ne.def] at hc, 
      exact ⟨c,⟨hc, hnm⟩⟩, },

    { -- this
      rw [aug_ideal, ring_hom.mem_ker] at hf0,
      rw ← hf0, 
      rw [← ideal.quotient.mkₐ_eq_mk R _, algebra_map_inv_eq R M],
      conv_rhs { rw mv_polynomial.as_sum f, },
      apply symm,
      rw map_sum,
      
      convert @finset.sum_eq_single _ _ _ (f.support) _ 0 _ _,
      { -- constant term 
        simp only [monomial_zero', aeval_C, algebra.id.map_eq_id, ring_hom.id_apply], },
      { intros b hb hb0,
        simp only [mv_polynomial.aeval_monomial, algebra.id.map_eq_id, ring_hom.id_apply],
        convert mul_zero _,
        rw ←finsupp.support_nonempty_iff  at hb0,
        obtain ⟨i, hi⟩ := hb0,  
        rw finsupp.prod, 
        apply finset.prod_eq_zero hi,
        rw if_pos,
        exact zero_pow (zero_lt_iff.mpr (finsupp.mem_support_iff.mp hi)),
        rw mv_polynomial.mem_supported at hf,
        apply hf,
        rw finset.mem_coe,
        rw mv_polynomial.mem_vars, 
        exact ⟨b, ⟨hb, hi⟩⟩, },
      { intro hf', 
        simp only [not_mem_support_iff] at hf',
        simp only [monomial_zero', aeval_C, algebra.id.map_eq_id, ring_hom.id_apply, hf'], }, }, },
end

end grade_zero


section grade_one

variables [module Rᵐᵒᵖ M] [is_central_scalar R M]

-- variable (R)
def triv_sq_zero_ext.ideal : ideal (triv_sq_zero_ext R M) 
  := ring_hom.ker (triv_sq_zero_ext.fst_hom R R M)

lemma triv_sq_zero_ext.mem_ideal_iff_inr : 
  ∀ (x : triv_sq_zero_ext R M),
  (x ∈ triv_sq_zero_ext.ideal R M ↔ x = triv_sq_zero_ext.inr x.snd) :=
begin
  rintro ⟨r,m⟩,
  simp only [triv_sq_zero_ext.ideal, ring_hom.mem_ker, triv_sq_zero_ext.fst_hom_apply, triv_sq_zero_ext.fst_mk],
  split,
  intro hr, rw hr, refl, 
  intro hrm,
  rw [← triv_sq_zero_ext.fst_mk r m, hrm, triv_sq_zero_ext.fst_inr],
end

lemma triv_sq_zero_ext.mem_ideal_iff_exists : ∀ (x : triv_sq_zero_ext R M),
  (x ∈ triv_sq_zero_ext.ideal R M ↔ ∃ (m : M), x = triv_sq_zero_ext.inr m) :=
begin
  rintro ⟨r,m⟩,
  simp only [triv_sq_zero_ext.ideal, ring_hom.mem_ker, triv_sq_zero_ext.fst_hom_apply, triv_sq_zero_ext.fst_mk],
  split,
  intro hr, rw hr, use m, refl,
  rintro ⟨n,hn⟩,
  rw [← triv_sq_zero_ext.fst_mk r m, hn, triv_sq_zero_ext.fst_inr],
end

def triv_sq_zero_ext.square_zero : (triv_sq_zero_ext.ideal R M) ^2 = 0 := 
begin
  rw [pow_two, ideal.zero_eq_bot, eq_bot_iff, ideal.mul_le],
  simp only [triv_sq_zero_ext.mem_ideal_iff_inr],
  rintros x hx y hy, 
  rw [hx, hy, ideal.mem_bot, triv_sq_zero_ext.inr_mul_inr],
end

/-- The canonical map from `divided_power_algebra R M` into `triv_sq_zero_ext R M` that sends
`divided_power_algebra.ι` to `triv_sq_zero_ext.inr`. -/
def to_triv_sq_zero_ext :
  divided_power_algebra R M →ₐ[R] triv_sq_zero_ext R M :=
begin
  apply lift R M 
    (divided_powers.of_square_zero.divided_powers (triv_sq_zero_ext.square_zero R M) : divided_powers (triv_sq_zero_ext.ideal R M))
    (triv_sq_zero_ext.inr_hom R M), 
  intro m,
  rw triv_sq_zero_ext.mem_ideal_iff_exists, use m, refl,
end

@[simp] lemma to_triv_sq_zero_ext_ι (x : M) :
   to_triv_sq_zero_ext R M (ι R x) = triv_sq_zero_ext.inr x :=
begin
  apply lift_ι_apply,
end

/- 
/- R → grade R M 0 is isomorphism -/
def ring_equiv_degree_zero : ring_equiv R (grade R M 0) := 
{ to_fun    := (proj' R M 0) ∘ (algebra_map R (divided_power_algebra R M)),
  inv_fun   := λ ⟨x, hx⟩, begin
dsimp only [grade, quot_submodule] at hx, 
rw submodule.mem_map at hx, 
let y := hx.some, let hy := hx.some_spec, 
rw mem_weighted_homogeneous_submodule at hy,
  sorry,end,
  left_inv  := sorry,
  right_inv := sorry,
  map_mul'  := sorry,
  map_add'  := sorry }

def proj_0_ring_hom : ring_hom (divided_power_algebra R M) R :=
{ to_fun    := (ring_equiv_degree_zero R M).inv_fun ∘ (proj' R M 0),
  map_one'  := sorry,
  map_mul'  := sorry,
  map_zero' := sorry,
  map_add'  := sorry }


/- ι : M → grade R M 1 is isomorphism -/
def linear_equiv_degree_one : linear_equiv (ring_hom.id R) M (grade R M 1) :=
{ to_fun    := (proj' R M 1) ∘ ι R,
  map_add'  := sorry,
  map_smul' := sorry,
  inv_fun   := sorry,
  left_inv  := sorry,
  right_inv := sorry } -/


end grade_one


variables (x : M) (n : ℕ)

/-- Lemma 2 of Roby 65. -/
lemma on_dp_algebra_unique (h h' : divided_powers (aug_ideal R M))
  (h1 : ∀ (x : M) (n : ℕ), h.dpow n (ι R x) = ideal.quotient.mk _ (X (n, x)))
  (h1' : ∀ (x : M) (n : ℕ), h'.dpow n (ι R x) = ideal.quotient.mk _ (X (n, x))) : 
  h = h' := 
begin
  apply divided_powers.dp_uniqueness,
  exact (aug_ideal_eq_span R M),
  intros n f,
  rw set.mem_image, 
  rintro ⟨⟨q, m⟩, hq, rfl⟩,
  simp only [set.mem_set_of_eq] at hq,
  nth_rewrite 0 [← h1 m q],
  rw ← h1' m q, 

  rw h.dpow_comp n (ne_of_gt hq) (ι_mem_aug_ideal R M m), 
  rw h'.dpow_comp n (ne_of_gt hq) (ι_mem_aug_ideal R M m), 
  rw h1 m, rw h1' m,
end


def cond_D : Prop := ∃ (h : divided_powers (aug_ideal R M)), 
  ∀ (x : M) (n : ℕ), h.dpow n (ι R x) = submodule.quotient.mk (X (n, x))


end divided_power_algebra

end

section roby
/- Formalization of Roby 1965, section 8 -/

.

open_locale tensor_product

variables (A R S : Type*) [comm_ring A] [comm_ring R] [algebra A R] [comm_ring S] [algebra A S] 
  {I : ideal R} {J : ideal S} (hI : divided_powers I) (hJ : divided_powers J)


def i_1 : R →ₐ R ⊗[A] S := algebra.tensor_product.include_left

def i_2 : S →ₐ R ⊗[A] S := algebra.tensor_product.include_right

variables {R S} (I J)
def K : ideal (R ⊗[A] S) := (I.map (i_1 A R S)) ⊔ (J.map (i_2 A R S))



namespace divided_powers

variables {I J}
/- Lemma 1 : uniqueness of the dp structure on R ⊗ S for I + J -/
lemma on_tensor_product_unique (hK hK' : divided_powers (K A I J))
  (hIK : is_pd_morphism hI hK (i_1 A R S)) 
  (hIK' : is_pd_morphism hI hK' (i_1 A R S))
  (hJK : is_pd_morphism hJ hK (i_2 A R S)) 
  (hJK' : is_pd_morphism hJ hK' (i_2 A R S)) : 
  hK = hK' :=
begin
  apply eq_of_eq_on_ideal,
  intros n x hx,
  suffices : x ∈ sub_pd_ideal.pd_equalizer hK hK',  
  rw sub_pd_ideal.mem_pd_equalizer_iff at this,
  exact this.2 n,
  suffices : K A I J ≤ sub_pd_ideal.pd_equalizer hK hK',
  apply this, exact hx,
  dsimp only [K], rw sup_le_iff,
  split, 
  apply sub_pd_ideal.le_equalizer_of_pd_morphism hI (i_1 A R S).to_ring_hom
  _ hK hK' hIK hIK',
  refine le_sup_left,
  apply sub_pd_ideal.le_equalizer_of_pd_morphism hJ (i_2 A R S).to_ring_hom
  _ hK hK' hJK hJK',
  refine le_sup_right,
end

def cond_T : Prop :=
∃ hK : divided_powers (K A I J), 
  is_pd_morphism hI hK (i_1 A R S) ∧ is_pd_morphism hJ hK (i_2 A R S)

section free

def cond_T_free [hR_free : module.free A R] [hS_free : module.free A S] : Prop :=
∃ hK : divided_powers (K A I J), 
  is_pd_morphism hI hK (i_1 A R S) ∧ is_pd_morphism hJ hK (i_2 A R S)

def cond_Q (A R : Type*) [comm_ring A] [comm_ring R] [algebra A R]
  {I : ideal R} (hI : divided_powers I) : Prop := 
∃ (T : Type*) [comm_ring T], by exactI ∃ [algebra A T], by exactI ∃ [module.free A T]
  {J : ideal T} (hJ : divided_powers J) (f : pd_morphism hI hJ), 
  function.surjective f.to_ring_hom

end free


end divided_powers

end roby

section divided_power_algebra

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

end divided_power_algebra


-- #lint