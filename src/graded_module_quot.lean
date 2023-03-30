import algebra.module.linear_map
import algebra.module.graded_module
import ring_theory.graded_algebra.homogeneous_ideal
import ring_theory.ideal.quotient
import ring_theory.ideal.quotient_operations


import ring_theory.graded_algebra.basic
import algebra.graded_mul_action
import algebra.direct_sum.decomposition
import algebra.module.big_operators

/-!
# Graded modules over a graded ring, homogeneous submodules

This file defines a graded module (given by `ℳ : ι → submodule R M` for a `module R M`, homogeneous submodules, and operations on them (sums, intersections, quotients…)

The ring `R` is  not graded.

At the end, one adds an `graded_ring 𝒜` for `𝒜 : ι → submodule R A`, an `A`-algebra structure on `M` which is compatible with the `R`-module structure, and the multiplication is compatible with the gradings. 

The case of homogeneous ideals of a graded ring follows.

WORK IN PROGRESS

Question : should there be a variant “without R” ?
Mathematically, this is equivalent with having R = ℕ,
but it may be painful to have to use `to_nat_module`…

Question : There is no reason that the indices of the grading of the ring are the same as for the module, 
one should just have an `add_smul_action : ι → θ → θ`

Question : What about multiplicative weights?

-/


open set_like direct_sum set
open_locale big_operators pointwise direct_sum

variables {ι σ τ R A M : Type*}


variables [semiring R]
variables [decidable_eq ι] [add_monoid ι]
variables [add_comm_monoid M] [module R M] 

-- variables [comm_ring A] [algebra R A] [module A M] [is_scalar_tower R A M]

-- variables (𝒜 : ι → submodule R A) 

variable (ℳ : ι → submodule R M) 

section graded_module

-- variables [set_like.graded_monoid 𝒜] [graded_ring 𝒜] [set_like.has_graded_smul 𝒜 ℳ]

-- example : set_like.has_graded_smul 𝒜 𝒜 := 
-- set_like.has_graded_mul.to_has_graded_smul 𝒜

/-  Trop lourd
 class graded_module {ι : Type*}  [decidable_eq ι] [add_monoid ι]
  {A R M : Type*} 
  [comm_semiring R] [comm_semiring A] [add_comm_monoid M] [algebra R A]
  [graded_algebra 𝒜]
  [module R M] [module A M] [is_scalar_tower R A M]
  {σ : Type*} [set_like σ A] [add_submonoid_class σ A] [submodule_class σ R A] (𝒜 : ι → σ) 
  {τ : Type*} [set_like τ M] [add_submonoid_class τ M] [submodule_class τ R M] (ℳ : ι → τ) :=
(to_decomposition : direct_sum.decomposition ℳ)
(to_graded_smul : set_like.has_graded_smul 𝒜 ℳ)
 -/

class graded_module {ι : Type*}  [decidable_eq ι] [add_monoid ι]
  {R M : Type*} 
  [semiring R] [add_comm_monoid M] 
  [module R M] 
  {τ : Type*} [set_like τ M] [add_submonoid_class τ M] [submodule_class τ R M] (ℳ : ι → τ) 
  extends direct_sum.decomposition ℳ


variable [graded_module ℳ]

/-- The projection maps of a graded module -/
def graded_module.proj (i : ι) : M →+ M :=
(add_submonoid_class.subtype (ℳ i)).comp ((dfinsupp.eval_add_monoid_hom i).comp $
  add_equiv.to_add_monoid_hom $ direct_sum.decompose_add_equiv ℳ)

@[simp] lemma graded_module.proj_apply (i : ι) (r : M) :
  graded_module.proj ℳ i r = (decompose ℳ r : ⨁ i, ℳ i) i := rfl

lemma graded_module.proj_recompose (r : ⨁ i, ℳ i) (i : ι) :
  graded_module.proj ℳ i ((decompose ℳ).symm r) =
  (decompose ℳ).symm (direct_sum.of _ i (r i)) :=
by rw [graded_module.proj_apply, decompose_symm_of, equiv.apply_symm_apply]

lemma graded_module.mem_support_iff [Π i (x : ℳ i), decidable (x ≠ 0)] (r : M) (i : ι) :
  i ∈ (decompose ℳ r).support ↔ graded_module.proj ℳ i r ≠ 0 :=
dfinsupp.mem_support_iff.trans zero_mem_class.coe_eq_zero.not.symm

end graded_module


section homogeneous_def

variable [graded_module ℳ]

/- An `N : submodule R M` is homogeneous if for every `r ∈ N`, all homogeneous components
  of `r` are in `N`. -/
def submodule.is_homogeneous [graded_module ℳ] (N : submodule R M): Prop :=
∀ (i : ι) ⦃r : M⦄, r ∈ N → (direct_sum.decompose ℳ r i : M) ∈ N

/-- For any `module R M`, we collect the homogeneous ideals of `M` into a type. -/
structure homogeneous_submodule extends submodule R M :=
(is_homogeneous' : submodule.is_homogeneous ℳ to_submodule)

variable {ℳ}

lemma homogeneous_submodule.is_homogeneous (N : homogeneous_submodule ℳ) :
  N.to_submodule.is_homogeneous ℳ := N.is_homogeneous'

lemma homogeneous_submodule.to_submodule_injective :
  function.injective (homogeneous_submodule.to_submodule : homogeneous_submodule ℳ → submodule R M) :=
λ ⟨x, hx⟩ ⟨y, hy⟩ (h : x = y), by simp [h]

instance homogeneous_submodule.set_like : set_like (homogeneous_submodule ℳ) M :=
{ coe := λ N, N.to_submodule,
  coe_injective' := λ N P h, homogeneous_submodule.to_submodule_injective $ set_like.coe_injective h }

@[ext] lemma homogeneous_submodule.ext {N P : homogeneous_submodule ℳ}
  (h : N.to_submodule = P.to_submodule) : N = P := homogeneous_submodule.to_submodule_injective h

@[simp] lemma homogeneous_submodule.mem_iff {N : homogeneous_submodule ℳ} {x : M} :
  x ∈ N.to_submodule ↔ x ∈ N := iff.rfl

end homogeneous_def

section homogeneous_core

-- variables [semiring R] [add_comm_monoid M] [module R M]
-- variables [set_like τ M]  (ℳ : ι → τ)

variable (N : submodule R M)
variable (R)
include M

/-- For any `N : submodule R M`, not necessarily homogeneous, `N.homogeneous_core' ℳ`
is the largest homogeneous submodule of `M` contained in `N`, as a submodule. -/
def submodule.homogeneous_core' (N : submodule R M) : submodule R M :=
submodule.span R (coe '' ((coe : subtype (is_homogeneous ℳ) → M) ⁻¹' N))


lemma submodule.homogeneous_core'_mono : monotone (submodule.homogeneous_core' R ℳ) :=
λ N P N_le_P, submodule.span_mono $ set.image_subset _ $ λ x, @N_le_P _

lemma submodule.homogeneous_core'_le : N.homogeneous_core' R ℳ ≤ N :=
submodule.span_le.2 $ image_preimage_subset _ _

end homogeneous_core

section is_homogeneous_submodule_defs

-- variables [semiring R] [add_comm_monoid M] [module R M]
-- variables [set_like τ M] [add_submonoid_class τ M] [submodule_class τ R M] (ℳ : ι → τ)
-- variables [decidable_eq ι] [add_monoid ι] [graded_module ℳ]

variable [graded_module ℳ]

variable (N : submodule R M)
variable (R)
include M

lemma submodule.is_homogeneous_iff_forall_subset :
  N.is_homogeneous ℳ ↔ ∀ i, (N : set M) ⊆ graded_module.proj ℳ i ⁻¹' N :=
iff.rfl

lemma submodule.is_homogeneous_iff_subset_Inter :
  N.is_homogeneous ℳ ↔ (N : set M) ⊆ ⋂ i, graded_module.proj ℳ i ⁻¹' ↑N :=
subset_Inter_iff.symm

/- --  Plus tard, lorsqu'il y aura un anneau gradué 
lemma submodule.mul_homogeneous_element_mem_of_mem
  {I : ideal A} (r x : A) (hx₁ : is_homogeneous 𝒜 x) (hx₂ : x ∈ I) (j : ι) :
  graded_ring.proj 𝒜 j (r * x) ∈ I :=
begin
  classical,
  rw [←direct_sum.sum_support_decompose 𝒜 r, finset.sum_mul, map_sum],
  apply ideal.sum_mem,
  intros k hk,
  obtain ⟨i, hi⟩ := hx₁,
  have mem₁ : (direct_sum.decompose 𝒜 r k : A) * x ∈ 𝒜 (k + i) := graded_monoid.mul_mem
    (set_like.coe_mem _) hi,
  erw [graded_ring.proj_apply, direct_sum.decompose_of_mem 𝒜 mem₁,
    coe_of_apply, set_like.coe_mk],
  split_ifs,
  { exact I.mul_mem_left _ hx₂ },
  { exact I.zero_mem },
end -/

#exit

-- From now on, unfinished 

lemma submodule.is_homogeneous_span (s : set M) (h : ∀ x ∈ s, is_homogeneous ℳ x) :
  (submodule.span R s).is_homogeneous ℳ :=
begin
  rintros i r hr,
  rw [ideal.span, finsupp.span_eq_range_total] at hr,
  rw linear_map.mem_range at hr,
  obtain ⟨s, rfl⟩ := hr,
  rw [finsupp.total_apply, finsupp.sum, decompose_sum, dfinsupp.finset_sum_apply,
    add_submonoid_class.coe_finset_sum],
  refine ideal.sum_mem _ _,
  rintros z hz1,
  rw [smul_eq_mul],
  refine ideal.mul_homogeneous_element_mem_of_mem 𝒜 (s z) z _ _ i,
  { rcases z with ⟨z, hz2⟩,
    apply h _ hz2, },
  { exact ideal.subset_span z.2 },
end

/--For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`.-/
def ideal.homogeneous_core : homogeneous_ideal 𝒜 :=
⟨ideal.homogeneous_core' 𝒜 I,
  ideal.is_homogeneous_span _ _ (λ x h, by { rw [subtype.image_preimage_coe] at h, exact h.2 })⟩

lemma ideal.homogeneous_core_mono : monotone (ideal.homogeneous_core 𝒜) :=
ideal.homogeneous_core'_mono 𝒜

lemma ideal.to_ideal_homogeneous_core_le : (I.homogeneous_core 𝒜).to_ideal ≤ I :=
ideal.homogeneous_core'_le 𝒜 I

variables {𝒜 I}

lemma ideal.mem_homogeneous_core_of_is_homogeneous_of_mem {x : A}
  (h : set_like.is_homogeneous 𝒜 x) (hmem : x ∈ I) : x ∈ I.homogeneous_core 𝒜 :=
ideal.subset_span ⟨⟨x, h⟩, hmem, rfl⟩

lemma ideal.is_homogeneous.to_ideal_homogeneous_core_eq_self (h : I.is_homogeneous 𝒜) :
  (I.homogeneous_core 𝒜).to_ideal = I :=
begin
  apply le_antisymm (I.homogeneous_core'_le 𝒜) _,
  intros x hx,
  classical,
  rw ←direct_sum.sum_support_decompose 𝒜 x,
  exact ideal.sum_mem _ (λ j hj, ideal.subset_span ⟨⟨_, is_homogeneous_coe _⟩, h _ hx, rfl⟩)
end

@[simp] lemma homogeneous_ideal.to_ideal_homogeneous_core_eq_self (I : homogeneous_ideal 𝒜) :
  I.to_ideal.homogeneous_core 𝒜 = I :=
by ext1; convert ideal.is_homogeneous.to_ideal_homogeneous_core_eq_self I.is_homogeneous

variables (𝒜 I)

lemma ideal.is_homogeneous.iff_eq : I.is_homogeneous 𝒜 ↔ (I.homogeneous_core 𝒜).to_ideal = I :=
⟨ λ hI, hI.to_ideal_homogeneous_core_eq_self,
  λ hI, hI ▸ (ideal.homogeneous_core 𝒜 I).2 ⟩

lemma ideal.is_homogeneous.iff_exists :
  I.is_homogeneous 𝒜 ↔ ∃ (S : set (homogeneous_submonoid 𝒜)), I = ideal.span (coe '' S) :=
begin
  rw [ideal.is_homogeneous.iff_eq, eq_comm],
  exact ((set.image_preimage.compose (submodule.gi _ _).gc).exists_eq_l _).symm,
end

end is_homogeneous_ideal_defs

/-! ### Operations
In this section, we show that `ideal.is_homogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `homogeneous_ideal`. -/

section operations

section semiring

variables [semiring A] [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ) [graded_ring 𝒜]
include A

namespace ideal.is_homogeneous

lemma bot : ideal.is_homogeneous 𝒜 ⊥ := λ i r hr,
begin
  simp only [ideal.mem_bot] at hr,
  rw [hr, decompose_zero, zero_apply],
  apply ideal.zero_mem
end

lemma top : ideal.is_homogeneous 𝒜 ⊤ :=
λ i r hr, by simp only [submodule.mem_top]

variables {𝒜}

lemma inf {I J : ideal A} (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) :
  (I ⊓ J).is_homogeneous 𝒜 :=
λ i r hr, ⟨HI _ hr.1, HJ _ hr.2⟩

lemma sup {I J : ideal A} (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) :
  (I ⊔ J).is_homogeneous 𝒜 :=
begin
  rw iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  refine ⟨s₁ ∪ s₂, _⟩,
  rw [set.image_union],
  exact (submodule.span_union _ _).symm,
end

protected lemma supr {κ : Sort*} {f : κ → ideal A} (h : ∀ i, (f i).is_homogeneous 𝒜) :
  (⨆ i, f i).is_homogeneous 𝒜 :=
begin
  simp_rw iff_exists at h ⊢,
  choose s hs using h,
  refine ⟨⋃ i, s i, _⟩,
  simp_rw [set.image_Union, ideal.span_Union],
  congr',
  exact funext hs,
end

protected lemma infi {κ : Sort*} {f : κ → ideal A} (h : ∀ i, (f i).is_homogeneous 𝒜) :
  (⨅ i, f i).is_homogeneous 𝒜 :=
begin
  intros i x hx,
  simp only [ideal.mem_infi] at ⊢ hx,
  exact λ j, h _ _ (hx j),
end

lemma supr₂ {κ : Sort*} {κ' : κ → Sort*} {f : Π i, κ' i → ideal A}
  (h : ∀ i j, (f i j).is_homogeneous 𝒜) :
  (⨆ i j, f i j).is_homogeneous 𝒜 :=
is_homogeneous.supr $ λ i, is_homogeneous.supr $ h i

lemma infi₂ {κ : Sort*} {κ' : κ → Sort*} {f : Π i, κ' i → ideal A}
  (h : ∀ i j, (f i j).is_homogeneous 𝒜) :
  (⨅ i j, f i j).is_homogeneous 𝒜 :=
is_homogeneous.infi $ λ i, is_homogeneous.infi $ h i

lemma Sup {ℐ : set (ideal A)} (h : ∀ I ∈ ℐ, ideal.is_homogeneous 𝒜 I) :
  (Sup ℐ).is_homogeneous 𝒜 :=
by { rw Sup_eq_supr, exact supr₂ h }

lemma Inf {ℐ : set (ideal A)} (h : ∀ I ∈ ℐ, ideal.is_homogeneous 𝒜 I) :
  (Inf ℐ).is_homogeneous 𝒜 :=
by { rw Inf_eq_infi, exact infi₂ h }

end ideal.is_homogeneous

variables {𝒜}

namespace homogeneous_ideal

instance : partial_order (homogeneous_ideal 𝒜) := set_like.partial_order

instance : has_top (homogeneous_ideal 𝒜) := ⟨⟨⊤, ideal.is_homogeneous.top 𝒜⟩⟩
instance : has_bot (homogeneous_ideal 𝒜) := ⟨⟨⊥, ideal.is_homogeneous.bot 𝒜⟩⟩
instance : has_sup (homogeneous_ideal 𝒜) := ⟨λ I J, ⟨_, I.is_homogeneous.sup J.is_homogeneous⟩⟩
instance : has_inf (homogeneous_ideal 𝒜) := ⟨λ I J, ⟨_, I.is_homogeneous.inf J.is_homogeneous⟩⟩
instance : has_Sup (homogeneous_ideal 𝒜) :=
⟨λ S, ⟨⨆ s ∈ S, to_ideal s, ideal.is_homogeneous.supr₂ $ λ s _, s.is_homogeneous⟩⟩
instance : has_Inf (homogeneous_ideal 𝒜) :=
⟨λ S, ⟨⨅ s ∈ S, to_ideal s, ideal.is_homogeneous.infi₂ $ λ s _, s.is_homogeneous⟩⟩

@[simp] lemma coe_top : ((⊤ : homogeneous_ideal 𝒜) : set A) = univ := rfl
@[simp] lemma coe_bot : ((⊥ : homogeneous_ideal 𝒜) : set A) = 0 := rfl
@[simp] lemma coe_sup (I J : homogeneous_ideal 𝒜) : ↑(I ⊔ J) = (I + J : set A) :=
submodule.coe_sup _ _
@[simp] lemma coe_inf (I J : homogeneous_ideal 𝒜) : (↑(I ⊓ J) : set A) = I ∩ J := rfl

@[simp] lemma to_ideal_top : (⊤ : homogeneous_ideal 𝒜).to_ideal = (⊤ : ideal A) := rfl
@[simp] lemma to_ideal_bot : (⊥ : homogeneous_ideal 𝒜).to_ideal = (⊥ : ideal A) := rfl

@[simp] lemma to_ideal_sup (I J : homogeneous_ideal 𝒜) :
  (I ⊔ J).to_ideal = I.to_ideal ⊔ J.to_ideal := rfl

@[simp] lemma to_ideal_inf (I J : homogeneous_ideal 𝒜) :
  (I ⊓ J).to_ideal = I.to_ideal ⊓ J.to_ideal := rfl

@[simp] lemma to_ideal_Sup (ℐ : set (homogeneous_ideal 𝒜)) :
  (Sup ℐ).to_ideal = ⨆ s ∈ ℐ, to_ideal s := rfl

@[simp] lemma to_ideal_Inf (ℐ : set (homogeneous_ideal 𝒜)) :
  (Inf ℐ).to_ideal = ⨅ s ∈ ℐ, to_ideal s := rfl

@[simp] lemma to_ideal_supr {κ : Sort*} (s : κ → homogeneous_ideal 𝒜) :
  (⨆ i, s i).to_ideal = ⨆ i, (s i).to_ideal :=
by rw [supr, to_ideal_Sup, supr_range]

@[simp] lemma to_ideal_infi {κ : Sort*} (s : κ → homogeneous_ideal 𝒜) :
  (⨅ i, s i).to_ideal = ⨅ i, (s i).to_ideal :=
by rw [infi, to_ideal_Inf, infi_range]

@[simp] lemma to_ideal_supr₂ {κ : Sort*} {κ' : κ → Sort*} (s : Π i, κ' i → homogeneous_ideal 𝒜) :
  (⨆ i j, s i j).to_ideal = ⨆ i j, (s i j).to_ideal :=
by simp_rw to_ideal_supr

@[simp] lemma to_ideal_infi₂ {κ : Sort*} {κ' : κ → Sort*} (s : Π i, κ' i → homogeneous_ideal 𝒜) :
  (⨅ i j, s i j).to_ideal = ⨅ i j, (s i j).to_ideal :=
by simp_rw to_ideal_infi

@[simp] lemma eq_top_iff (I : homogeneous_ideal 𝒜) : I = ⊤ ↔ I.to_ideal = ⊤ :=
to_ideal_injective.eq_iff.symm

@[simp] lemma eq_bot_iff (I : homogeneous_ideal 𝒜) : I = ⊥ ↔ I.to_ideal = ⊥ :=
to_ideal_injective.eq_iff.symm

instance : complete_lattice (homogeneous_ideal 𝒜) :=
to_ideal_injective.complete_lattice _ to_ideal_sup to_ideal_inf to_ideal_Sup to_ideal_Inf
  to_ideal_top to_ideal_bot

instance : has_add (homogeneous_ideal 𝒜) := ⟨(⊔)⟩

@[simp] lemma to_ideal_add (I J : homogeneous_ideal 𝒜) :
  (I + J).to_ideal = I.to_ideal + J.to_ideal := rfl

instance : inhabited (homogeneous_ideal 𝒜) := { default := ⊥ }

end homogeneous_ideal

end semiring

section comm_semiring
variables [comm_semiring A]
variables [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] {𝒜 : ι → σ} [graded_ring 𝒜]
variable (I : ideal A)
include A

lemma ideal.is_homogeneous.mul {I J : ideal A}
  (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) : (I * J).is_homogeneous 𝒜 :=
begin
  rw ideal.is_homogeneous.iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  rw ideal.span_mul_span',
  exact ⟨s₁ * s₂, congr_arg _ $ (set.image_mul (homogeneous_submonoid 𝒜).subtype).symm⟩,
end

variables {𝒜}

instance : has_mul (homogeneous_ideal 𝒜) :=
{ mul := λ I J, ⟨I.to_ideal * J.to_ideal, I.is_homogeneous.mul J.is_homogeneous⟩ }

@[simp] lemma homogeneous_ideal.to_ideal_mul (I J : homogeneous_ideal 𝒜) :
  (I * J).to_ideal = I.to_ideal * J.to_ideal := rfl

end comm_semiring

end operations

/-! ### Homogeneous core
Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/

section homogeneous_core

open homogeneous_ideal

variables [semiring A] [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ) [graded_ring 𝒜]
variable (I : ideal A)
include A

lemma ideal.homogeneous_core.gc : galois_connection to_ideal (ideal.homogeneous_core 𝒜) :=
λ I J, ⟨
  λ H, I.to_ideal_homogeneous_core_eq_self ▸ ideal.homogeneous_core_mono 𝒜 H,
  λ H, le_trans H (ideal.homogeneous_core'_le _ _)⟩

/--`to_ideal : homogeneous_ideal 𝒜 → ideal A` and `ideal.homogeneous_core 𝒜` forms a galois
coinsertion-/
def ideal.homogeneous_core.gi : galois_coinsertion to_ideal (ideal.homogeneous_core 𝒜) :=
{ choice := λ I HI,
    ⟨I, le_antisymm (I.to_ideal_homogeneous_core_le 𝒜) HI ▸ homogeneous_ideal.is_homogeneous _⟩,
  gc := ideal.homogeneous_core.gc 𝒜,
  u_l_le := λ I, ideal.homogeneous_core'_le _ _,
  choice_eq := λ I H, le_antisymm H (I.to_ideal_homogeneous_core_le _) }

lemma ideal.homogeneous_core_eq_Sup :
  I.homogeneous_core 𝒜 = Sup {J : homogeneous_ideal 𝒜 | J.to_ideal ≤ I} :=
eq.symm $ is_lub.Sup_eq $ (ideal.homogeneous_core.gc 𝒜).is_greatest_u.is_lub

lemma ideal.homogeneous_core'_eq_Sup :
  I.homogeneous_core' 𝒜 = Sup {J : ideal A | J.is_homogeneous 𝒜 ∧ J ≤ I} :=
begin
  refine (is_lub.Sup_eq _).symm,
  apply is_greatest.is_lub,
  have coe_mono : monotone (to_ideal : homogeneous_ideal 𝒜 → ideal A) := λ x y, id,
  convert coe_mono.map_is_greatest (ideal.homogeneous_core.gc 𝒜).is_greatest_u using 1,
  ext,
  rw [mem_image, mem_set_of_eq],
  refine ⟨λ hI, ⟨⟨x, hI.1⟩, ⟨hI.2, rfl⟩⟩, by rintro ⟨x, ⟨hx, rfl⟩⟩; exact ⟨x.is_homogeneous, hx⟩⟩,
end

end homogeneous_core

/-! ### Homogeneous hulls -/

section homogeneous_hull

open homogeneous_ideal

variables [semiring A] [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ) [graded_ring 𝒜]
variable (I : ideal A)
include A

/--For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_hull 𝒜` is
the smallest homogeneous ideal containing `I`. -/
def ideal.homogeneous_hull : homogeneous_ideal 𝒜 :=
⟨ideal.span {r : A | ∃ (i : ι) (x : I), (direct_sum.decompose 𝒜 (x : A) i : A) = r}, begin
  refine ideal.is_homogeneous_span _ _ (λ x hx, _),
  obtain ⟨i, x, rfl⟩ := hx,
  apply set_like.is_homogeneous_coe
end⟩

lemma ideal.le_to_ideal_homogeneous_hull :
  I ≤ (ideal.homogeneous_hull 𝒜 I).to_ideal :=
begin
  intros r hr,
  classical,
  rw [←direct_sum.sum_support_decompose 𝒜 r],
  refine ideal.sum_mem _ _, intros j hj,
  apply ideal.subset_span, use j, use ⟨r, hr⟩, refl,
end

lemma ideal.homogeneous_hull_mono : monotone (ideal.homogeneous_hull 𝒜) := λ I J I_le_J,
begin
  apply ideal.span_mono,
  rintros r ⟨hr1, ⟨x, hx⟩, rfl⟩,
  refine ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩,
end

variables {I 𝒜}

lemma ideal.is_homogeneous.to_ideal_homogeneous_hull_eq_self (h : I.is_homogeneous 𝒜) :
  (ideal.homogeneous_hull 𝒜 I).to_ideal = I :=
begin
  apply le_antisymm _ (ideal.le_to_ideal_homogeneous_hull _ _),
  apply (ideal.span_le).2,
  rintros _ ⟨i, x, rfl⟩,
  exact h _ x.prop,
end

@[simp] lemma homogeneous_ideal.homogeneous_hull_to_ideal_eq_self (I : homogeneous_ideal 𝒜) :
  I.to_ideal.homogeneous_hull 𝒜 = I :=
homogeneous_ideal.to_ideal_injective $ I.is_homogeneous.to_ideal_homogeneous_hull_eq_self

variables (I 𝒜)

lemma ideal.to_ideal_homogeneous_hull_eq_supr :
  (I.homogeneous_hull 𝒜).to_ideal = ⨆ i, ideal.span (graded_ring.proj 𝒜 i '' I) :=
begin
  rw ←ideal.span_Union,
  apply congr_arg ideal.span _,
  ext1,
  simp only [set.mem_Union, set.mem_image, mem_set_of_eq, graded_ring.proj_apply,
    set_like.exists, exists_prop, subtype.coe_mk, set_like.mem_coe],
end

lemma ideal.homogeneous_hull_eq_supr :
  (I.homogeneous_hull 𝒜) =
  ⨆ i, ⟨ideal.span (graded_ring.proj 𝒜 i '' I), ideal.is_homogeneous_span 𝒜 _
    (by {rintros _ ⟨x, -, rfl⟩, apply set_like.is_homogeneous_coe})⟩ :=
by { ext1, rw [ideal.to_ideal_homogeneous_hull_eq_supr, to_ideal_supr], refl }

end homogeneous_hull

section galois_connection

open homogeneous_ideal

variables [semiring A] [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ) [graded_ring 𝒜]
include A

lemma ideal.homogeneous_hull.gc : galois_connection (ideal.homogeneous_hull 𝒜) to_ideal :=
λ I J, ⟨
  le_trans (ideal.le_to_ideal_homogeneous_hull _ _),
  λ H, J.homogeneous_hull_to_ideal_eq_self ▸ ideal.homogeneous_hull_mono 𝒜 H⟩

/-- `ideal.homogeneous_hull 𝒜` and `to_ideal : homogeneous_ideal 𝒜 → ideal A` form a galois
insertion-/
def ideal.homogeneous_hull.gi : galois_insertion (ideal.homogeneous_hull 𝒜) to_ideal :=
{ choice := λ I H, ⟨I, le_antisymm H (I.le_to_ideal_homogeneous_hull 𝒜) ▸ is_homogeneous _⟩,
  gc := ideal.homogeneous_hull.gc 𝒜,
  le_l_u := λ I, ideal.le_to_ideal_homogeneous_hull _ _,
  choice_eq := λ I H, le_antisymm (I.le_to_ideal_homogeneous_hull 𝒜) H}

lemma ideal.homogeneous_hull_eq_Inf (I : ideal A) :
  ideal.homogeneous_hull 𝒜 I = Inf { J : homogeneous_ideal 𝒜 | I ≤ J.to_ideal } :=
eq.symm $ is_glb.Inf_eq $ (ideal.homogeneous_hull.gc 𝒜).is_least_l.is_glb

end galois_connection