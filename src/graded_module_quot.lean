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

At the end, one adds an `graded_ring ℳ` for `ℳ : ι → submodule R A`, an `A`-algebra structure on `M` which is compatible with the `R`-module structure, and the multiplication is compatible with the gradings. 

The case of homogeneous submodules of a graded ring follows.

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

-- variables (ℳ : ι → submodule R A) 

variable (ℳ : ι → submodule R M) 

section graded_module

-- variables [set_like.graded_monoid ℳ] [graded_ring ℳ] [set_like.has_graded_smul ℳ ℳ]

-- example : set_like.has_graded_smul ℳ ℳ := 
-- set_like.has_graded_mul.to_has_graded_smul ℳ

/-  Trop lourd
 class graded_module {ι : Type*}  [decidable_eq ι] [add_monoid ι]
  {A R M : Type*} 
  [comm_semiring R] [comm_semiring A] [add_comm_monoid M] [algebra R A]
  [graded_algebra ℳ]
  [module R M] [module A M] [is_scalar_tower R A M]
  {σ : Type*} [set_like σ A] [add_submonoid_class σ A] [submodule_class σ R A] (ℳ : ι → σ) 
  {τ : Type*} [set_like τ M] [add_submonoid_class τ M] [submodule_class τ R M] (ℳ : ι → τ) :=
(to_decomposition : direct_sum.decomposition ℳ)
(to_graded_smul : set_like.has_graded_smul ℳ ℳ)
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

variable {R}
/- An `N : submodule R M` is homogeneous if for every `r ∈ N`, all homogeneous components
  of `r` are in `N`. -/
def submodule.is_homogeneous [graded_module ℳ] (N : submodule R M): Prop :=
∀ (i : ι) ⦃r : M⦄, r ∈ N → (direct_sum.decompose ℳ r i : M) ∈ N

/-- For any `module R M`, we collect the homogeneous submodules of `M` into a type. -/
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
variable {R}
include M

/-- For any `N : submodule R M`, not necessarily homogeneous, `N.homogeneous_core' ℳ`
is the largest homogeneous submodule of `M` contained in `N`, as a submodule. -/
def submodule.homogeneous_core' (N : submodule R M) : submodule R M :=
submodule.span R (coe '' ((coe : subtype (is_homogeneous ℳ) → M) ⁻¹' N))


lemma submodule.homogeneous_core'_mono : monotone (submodule.homogeneous_core' ℳ) :=
λ N P N_le_P, submodule.span_mono $ set.image_subset _ $ λ x, @N_le_P _

lemma submodule.homogeneous_core'_le : N.homogeneous_core' ℳ ≤ N :=
submodule.span_le.2 $ image_preimage_subset _ _

end homogeneous_core

section is_homogeneous_submodule_defs

-- variables [semiring R] [add_comm_monoid M] [module R M]
-- variables [set_like τ M] [add_submonoid_class τ M] [submodule_class τ R M] (ℳ : ι → τ)
-- variables [decidable_eq ι] [add_monoid ι] [graded_module ℳ]

variable [graded_module ℳ]

variable (N : submodule R M)
variable {R}
include M

lemma submodule.is_homogeneous_iff_forall_subset :
  N.is_homogeneous ℳ ↔ ∀ i, (N : set M) ⊆ graded_module.proj ℳ i ⁻¹' N :=
iff.rfl

lemma submodule.is_homogeneous_iff_subset_Inter :
  N.is_homogeneous ℳ ↔ (N : set M) ⊆ ⋂ i, graded_module.proj ℳ i ⁻¹' ↑N :=
subset_Inter_iff.symm

/- --  Plus tard, lorsqu'il y aura un anneau gradué 
lemma submodule.mul_homogeneous_element_mem_of_mem
  {I : ideal A} (r x : A) (hx₁ : is_homogeneous ℳ x) (hx₂ : x ∈ I) (j : ι) :
  graded_ring.proj ℳ j (r * x) ∈ I :=
begin
  classical,
  rw [←direct_sum.sum_support_decompose ℳ r, finset.sum_mul, map_sum],
  apply ideal.sum_mem,
  intros k hk,
  obtain ⟨i, hi⟩ := hx₁,
  have mem₁ : (direct_sum.decompose ℳ r k : A) * x ∈ ℳ (k + i) := graded_monoid.mul_mem
    (set_like.coe_mem _) hi,
  erw [graded_ring.proj_apply, direct_sum.decompose_of_mem ℳ mem₁,
    coe_of_apply, set_like.coe_mk],
  split_ifs,
  { exact I.mul_mem_left _ hx₂ },
  { exact I.zero_mem },
end -/

lemma submodule.is_homogeneous_span (s : set M) (h : ∀ x ∈ s, is_homogeneous ℳ x) :
  (submodule.span R s).is_homogeneous ℳ :=
begin
  rintros i r hr,
  rw [finsupp.span_eq_range_total, linear_map.mem_range] at hr,
  obtain ⟨f, rfl⟩ := hr,
  rw [finsupp.total_apply, finsupp.sum, decompose_sum, dfinsupp.finset_sum_apply,
    add_submonoid_class.coe_finset_sum],
  refine submodule.sum_mem _ _,
  rintros ⟨z, hz⟩ hz1,
  simp only [decompose_smul, dfinsupp.coe_smul, pi.smul_apply, submodule.coe_smul_of_tower, subtype.coe_mk],
  refine submodule.smul_mem _ _ _,
  obtain ⟨j, hzj⟩ := h z hz, 
  by_cases hij : i = j,
  { rw hij, 
    rw direct_sum.decompose_of_mem_same,
    exact submodule.subset_span hz,
    exact hzj },
  { rw direct_sum.decompose_of_mem_ne ℳ hzj (ne.symm hij),
    exact submodule.zero_mem _,  },
end

/--For any `N : submodule R M`, not necessarily homogeneous, `N.homogeneous_core' R ℳ`
is the largest homogeneous submodule of `M` contained in `N`.-/
def submodule.homogeneous_core : homogeneous_submodule ℳ :=
⟨submodule.homogeneous_core' ℳ N,
  submodule.is_homogeneous_span ℳ _ (λ x h,
  by { rw [subtype.image_preimage_coe, mem_inter_iff, mem_coe] at h,exact h.2, })⟩

lemma submodule.homogeneous_core_mono : monotone (submodule.homogeneous_core ℳ) :=
submodule.homogeneous_core'_mono ℳ

lemma submodule.to_submodule_homogeneous_core_le : (N.homogeneous_core ℳ).to_submodule ≤ N :=
submodule.homogeneous_core'_le ℳ N

variables {ℳ N}

lemma submodule.mem_homogeneous_core_of_is_homogeneous_of_mem {x : M}
  (h : set_like.is_homogeneous ℳ x) (hmem : x ∈ N) : x ∈ N.homogeneous_core ℳ :=
submodule.subset_span ⟨⟨x, h⟩, hmem, rfl⟩

lemma submodule.is_homogeneous.to_submodule_homogeneous_core_eq_self (h : N.is_homogeneous ℳ) :
  (N.homogeneous_core ℳ).to_submodule = N :=
begin
  apply le_antisymm (N.homogeneous_core'_le ℳ) _,
  intros x hx,
  classical,
  rw ←direct_sum.sum_support_decompose ℳ x,
  exact submodule.sum_mem _ (λ j hj, submodule.subset_span ⟨⟨_, is_homogeneous_coe _⟩, h _ hx, rfl⟩)
end

@[simp] lemma homogeneous_submodule.to_submodule_homogeneous_core_eq_self (N : homogeneous_submodule ℳ) :
  N.to_submodule.homogeneous_core ℳ = N :=
by ext1; convert submodule.is_homogeneous.to_submodule_homogeneous_core_eq_self N.is_homogeneous

variables (ℳ N)

lemma submodule.is_homogeneous.iff_eq : N.is_homogeneous ℳ ↔ (N.homogeneous_core ℳ).to_submodule = N :=
⟨ λ hI, hI.to_submodule_homogeneous_core_eq_self,
  λ hI, hI ▸ (submodule.homogeneous_core ℳ N).2 ⟩

def homogeneous_set : set M := {m : M | is_homogeneous ℳ m}

lemma submodule.is_homogeneous.iff_exists :
  N.is_homogeneous ℳ ↔ ∃ (S : set (homogeneous_set ℳ)), N = submodule.span R (coe '' S) :=
begin
  rw [submodule.is_homogeneous.iff_eq, eq_comm],
  exact ((set.image_preimage.compose (submodule.gi _ _).gc).exists_eq_l _).symm,
end

end is_homogeneous_submodule_defs

/-! ### Operations
In this section, we show that `submodule.is_homogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `homogeneous_submodule`. -/

section operations

section semiring

/- 
variables [semiring A] [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (ℳ : ι → σ) [graded_ring ℳ]
include A -/

variable [graded_module ℳ]
variable {R}
include M 

namespace submodule.is_homogeneous

lemma bot : submodule.is_homogeneous ℳ ⊥ := λ i r hr,
begin
  simp only [submodule.mem_bot] at hr,
  rw [hr, decompose_zero, zero_apply],
  apply submodule.zero_mem
end

lemma top : submodule.is_homogeneous ℳ ⊤ :=
λ i r hr, by simp only [submodule.mem_top]

variables {ℳ}

lemma inf {N P : submodule R M} (HN : N.is_homogeneous ℳ) (HP : P.is_homogeneous ℳ) :
  (N ⊓ P).is_homogeneous ℳ :=
λ i r hr, ⟨HN _ hr.1, HP _ hr.2⟩

lemma sup {N P : submodule R M} (HN : N.is_homogeneous ℳ) (HP : P.is_homogeneous ℳ) :
  (N ⊔ P).is_homogeneous ℳ :=
begin
  rw iff_exists at HN HP ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HN, HP⟩,
  refine ⟨s₁ ∪ s₂, _⟩,
  rw [set.image_union],
  exact (submodule.span_union _ _).symm,
end

protected lemma supr {κ : Sort*} {f : κ → submodule R M} (h : ∀ i, (f i).is_homogeneous ℳ) :
  (⨆ i, f i).is_homogeneous ℳ :=
begin
  simp_rw iff_exists at h ⊢,
  choose s hs using h,
  refine ⟨⋃ i, s i, _⟩,
  simp_rw [set.image_Union, submodule.span_Union],
  congr',
  exact funext hs,
end

protected lemma infi {κ : Sort*} {f : κ → submodule R M} (h : ∀ i, (f i).is_homogeneous ℳ) :
  (⨅ i, f i).is_homogeneous ℳ :=
begin
  intros i x hx,
  simp only [submodule.mem_infi] at ⊢ hx,
  exact λ j, h _ _ (hx j),
end

lemma supr₂ {κ : Sort*} {κ' : κ → Sort*} {f : Π i, κ' i → submodule R M}
  (h : ∀ i j, (f i j).is_homogeneous ℳ) :
  (⨆ i j, f i j).is_homogeneous ℳ :=
is_homogeneous.supr $ λ i, is_homogeneous.supr $ h i

lemma infi₂ {κ : Sort*} {κ' : κ → Sort*} {f : Π i, κ' i → submodule R M}
  (h : ∀ i j, (f i j).is_homogeneous ℳ) :
  (⨅ i j, f i j).is_homogeneous ℳ :=
is_homogeneous.infi $ λ i, is_homogeneous.infi $ h i

lemma Sup {𝒩 : set (submodule R M)} (h : ∀ N ∈ 𝒩, submodule.is_homogeneous ℳ N) :
  (Sup 𝒩).is_homogeneous ℳ :=
by { rw Sup_eq_supr, exact supr₂ h }

lemma Inf {𝒩 : set (submodule R M)} (h : ∀ N ∈ 𝒩, submodule.is_homogeneous ℳ N) :
  (Inf 𝒩).is_homogeneous ℳ :=
by { rw Inf_eq_infi, exact infi₂ h }

end submodule.is_homogeneous

variables {ℳ}

namespace homogeneous_submodule

instance : partial_order (homogeneous_submodule ℳ) := set_like.partial_order

instance : has_top (homogeneous_submodule ℳ) := ⟨⟨⊤, submodule.is_homogeneous.top ℳ⟩⟩
instance : has_bot (homogeneous_submodule ℳ) := ⟨⟨⊥, submodule.is_homogeneous.bot ℳ⟩⟩
instance : has_sup (homogeneous_submodule ℳ) := ⟨λ I J, ⟨_, I.is_homogeneous.sup J.is_homogeneous⟩⟩
instance : has_inf (homogeneous_submodule ℳ) := ⟨λ I J, ⟨_, I.is_homogeneous.inf J.is_homogeneous⟩⟩
instance : has_Sup (homogeneous_submodule ℳ) :=
⟨λ S, ⟨⨆ s ∈ S, to_submodule s, submodule.is_homogeneous.supr₂ $ λ s _, s.is_homogeneous⟩⟩
instance : has_Inf (homogeneous_submodule ℳ) :=
⟨λ S, ⟨⨅ s ∈ S, to_submodule s, submodule.is_homogeneous.infi₂ $ λ s _, s.is_homogeneous⟩⟩

@[simp] lemma coe_top : ((⊤ : homogeneous_submodule ℳ) : set M) = univ := rfl
@[simp] lemma coe_bot : ((⊥ : homogeneous_submodule ℳ) : set M) = 0 := rfl
@[simp] lemma coe_sup (I J : homogeneous_submodule ℳ) : ↑(I ⊔ J) = (I + J : set M) :=
submodule.coe_sup _ _
@[simp] lemma coe_inf (I J : homogeneous_submodule ℳ) : (↑(I ⊓ J) : set M) = I ∩ J := rfl

@[simp] lemma to_submodule_top : (⊤ : homogeneous_submodule ℳ).to_submodule = (⊤ : submodule R M) := rfl
@[simp] lemma to_submodule_bot : (⊥ : homogeneous_submodule ℳ).to_submodule = (⊥ : submodule R M) := rfl

@[simp] lemma to_submodule_sup (I J : homogeneous_submodule ℳ) :
  (I ⊔ J).to_submodule = I.to_submodule ⊔ J.to_submodule := rfl

@[simp] lemma to_submodule_inf (I J : homogeneous_submodule ℳ) :
  (I ⊓ J).to_submodule = I.to_submodule ⊓ J.to_submodule := rfl

@[simp] lemma to_submodule_Sup (ℐ : set (homogeneous_submodule ℳ)) :
  (Sup ℐ).to_submodule = ⨆ s ∈ ℐ, to_submodule s := rfl

@[simp] lemma to_submodule_Inf (ℐ : set (homogeneous_submodule ℳ)) :
  (Inf ℐ).to_submodule = ⨅ s ∈ ℐ, to_submodule s := rfl

@[simp] lemma to_submodule_supr {κ : Sort*} (s : κ → homogeneous_submodule ℳ) :
  (⨆ i, s i).to_submodule = ⨆ i, (s i).to_submodule :=
by rw [supr, to_submodule_Sup, supr_range]

@[simp] lemma to_submodule_infi {κ : Sort*} (s : κ → homogeneous_submodule ℳ) :
  (⨅ i, s i).to_submodule = ⨅ i, (s i).to_submodule :=
by rw [infi, to_submodule_Inf, infi_range]

@[simp] lemma to_submodule_supr₂ {κ : Sort*} {κ' : κ → Sort*} (s : Π i, κ' i → homogeneous_submodule ℳ) :
  (⨆ i j, s i j).to_submodule = ⨆ i j, (s i j).to_submodule :=
by simp_rw to_submodule_supr

@[simp] lemma to_submodule_infi₂ {κ : Sort*} {κ' : κ → Sort*} (s : Π i, κ' i → homogeneous_submodule ℳ) :
  (⨅ i j, s i j).to_submodule = ⨅ i j, (s i j).to_submodule :=
by simp_rw to_submodule_infi

@[simp] lemma eq_top_iff (I : homogeneous_submodule ℳ) : I = ⊤ ↔ I.to_submodule = ⊤ :=
to_submodule_injective.eq_iff.symm

@[simp] lemma eq_bot_iff (I : homogeneous_submodule ℳ) : I = ⊥ ↔ I.to_submodule = ⊥ :=
to_submodule_injective.eq_iff.symm

instance : complete_lattice (homogeneous_submodule ℳ) :=
to_submodule_injective.complete_lattice _ to_submodule_sup to_submodule_inf to_submodule_Sup to_submodule_Inf
  to_submodule_top to_submodule_bot

instance : has_add (homogeneous_submodule ℳ) := ⟨(⊔)⟩

@[simp] lemma to_submodule_add (I J : homogeneous_submodule ℳ) :
  (I + J).to_submodule = I.to_submodule + J.to_submodule := rfl

instance : inhabited (homogeneous_submodule ℳ) := { default := ⊥ }

end homogeneous_submodule

end semiring

section comm_semiring

variable [comm_semiring R]
variables [comm_semiring A]
variables [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] {𝒜 : ι → σ} [graded_ring 𝒜]

variable [module A M]
variables (I : ideal A) (N : submodule R M)

variable [graded_module ℳ]
include A

lemma ideal.is_homogeneous.mul {I : ideal A}
  (HI : I.is_homogeneous 𝒜) (HN : N.is_homogeneous ℳ) : (I • N).is_homogeneous ℳ :=
begin
  rw ideal.is_homogeneous.iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  rw ideal.span_mul_span',
  exact ⟨s₁ * s₂, congr_arg _ $ (set.image_mul (homogeneous_submonoid ℳ).subtype).symm⟩,
end

variables {ℳ}

instance : has_mul (homogeneous_ideal ℳ) :=
{ mul := λ I J, ⟨I.to_ideal * J.to_ideal, I.is_homogeneous.mul J.is_homogeneous⟩ }

@[simp] lemma homogeneous_ideal.to_ideal_mul (I J : homogeneous_ideal ℳ) :
  (I * J).to_ideal = I.to_ideal * J.to_ideal := rfl

end comm_semiring

end operations

/-! ### Homogeneous core
Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/

section homogeneous_core

open homogeneous_ideal

variables [semiring A] [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (ℳ : ι → σ) [graded_ring ℳ]
variable (I : ideal A)
include A

lemma ideal.homogeneous_core.gc : galois_connection to_ideal (ideal.homogeneous_core ℳ) :=
λ I J, ⟨
  λ H, I.to_ideal_homogeneous_core_eq_self ▸ ideal.homogeneous_core_mono ℳ H,
  λ H, le_trans H (ideal.homogeneous_core'_le _ _)⟩

/--`to_ideal : homogeneous_ideal ℳ → ideal A` and `ideal.homogeneous_core ℳ` forms a galois
coinsertion-/
def ideal.homogeneous_core.gi : galois_coinsertion to_ideal (ideal.homogeneous_core ℳ) :=
{ choice := λ I HI,
    ⟨I, le_antisymm (I.to_ideal_homogeneous_core_le ℳ) HI ▸ homogeneous_ideal.is_homogeneous _⟩,
  gc := ideal.homogeneous_core.gc ℳ,
  u_l_le := λ I, ideal.homogeneous_core'_le _ _,
  choice_eq := λ I H, le_antisymm H (I.to_ideal_homogeneous_core_le _) }

lemma ideal.homogeneous_core_eq_Sup :
  I.homogeneous_core ℳ = Sup {J : homogeneous_ideal ℳ | J.to_ideal ≤ I} :=
eq.symm $ is_lub.Sup_eq $ (ideal.homogeneous_core.gc ℳ).is_greatest_u.is_lub

lemma ideal.homogeneous_core'_eq_Sup :
  I.homogeneous_core' ℳ = Sup {J : ideal A | J.is_homogeneous ℳ ∧ J ≤ I} :=
begin
  refine (is_lub.Sup_eq _).symm,
  apply is_greatest.is_lub,
  have coe_mono : monotone (to_ideal : homogeneous_ideal ℳ → ideal A) := λ x y, id,
  convert coe_mono.map_is_greatest (ideal.homogeneous_core.gc ℳ).is_greatest_u using 1,
  ext,
  rw [mem_image, mem_set_of_eq],
  refine ⟨λ hI, ⟨⟨x, hI.1⟩, ⟨hI.2, rfl⟩⟩, by rintro ⟨x, ⟨hx, rfl⟩⟩; exact ⟨x.is_homogeneous, hx⟩⟩,
end

end homogeneous_core

/-! ### Homogeneous hulls -/

section homogeneous_hull

open homogeneous_ideal

variables [semiring A] [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (ℳ : ι → σ) [graded_ring ℳ]
variable (I : ideal A)
include A

/--For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_hull ℳ` is
the smallest homogeneous ideal containing `I`. -/
def ideal.homogeneous_hull : homogeneous_ideal ℳ :=
⟨ideal.span {r : A | ∃ (i : ι) (x : I), (direct_sum.decompose ℳ (x : A) i : A) = r}, begin
  refine ideal.is_homogeneous_span _ _ (λ x hx, _),
  obtain ⟨i, x, rfl⟩ := hx,
  apply set_like.is_homogeneous_coe
end⟩

lemma ideal.le_to_ideal_homogeneous_hull :
  I ≤ (ideal.homogeneous_hull ℳ I).to_ideal :=
begin
  intros r hr,
  classical,
  rw [←direct_sum.sum_support_decompose ℳ r],
  refine ideal.sum_mem _ _, intros j hj,
  apply ideal.subset_span, use j, use ⟨r, hr⟩, refl,
end

lemma ideal.homogeneous_hull_mono : monotone (ideal.homogeneous_hull ℳ) := λ I J I_le_J,
begin
  apply ideal.span_mono,
  rintros r ⟨hr1, ⟨x, hx⟩, rfl⟩,
  refine ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩,
end

variables {I ℳ}

lemma ideal.is_homogeneous.to_ideal_homogeneous_hull_eq_self (h : I.is_homogeneous ℳ) :
  (ideal.homogeneous_hull ℳ I).to_ideal = I :=
begin
  apply le_antisymm _ (ideal.le_to_ideal_homogeneous_hull _ _),
  apply (ideal.span_le).2,
  rintros _ ⟨i, x, rfl⟩,
  exact h _ x.prop,
end

@[simp] lemma homogeneous_ideal.homogeneous_hull_to_ideal_eq_self (I : homogeneous_ideal ℳ) :
  I.to_ideal.homogeneous_hull ℳ = I :=
homogeneous_ideal.to_ideal_injective $ I.is_homogeneous.to_ideal_homogeneous_hull_eq_self

variables (I ℳ)

lemma ideal.to_ideal_homogeneous_hull_eq_supr :
  (I.homogeneous_hull ℳ).to_ideal = ⨆ i, ideal.span (graded_ring.proj ℳ i '' I) :=
begin
  rw ←ideal.span_Union,
  apply congr_arg ideal.span _,
  ext1,
  simp only [set.mem_Union, set.mem_image, mem_set_of_eq, graded_ring.proj_apply,
    set_like.exists, exists_prop, subtype.coe_mk, set_like.mem_coe],
end

lemma ideal.homogeneous_hull_eq_supr :
  (I.homogeneous_hull ℳ) =
  ⨆ i, ⟨ideal.span (graded_ring.proj ℳ i '' I), ideal.is_homogeneous_span ℳ _
    (by {rintros _ ⟨x, -, rfl⟩, apply set_like.is_homogeneous_coe})⟩ :=
by { ext1, rw [ideal.to_ideal_homogeneous_hull_eq_supr, to_ideal_supr], refl }

end homogeneous_hull

section galois_connection

open homogeneous_ideal

variables [semiring A] [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (ℳ : ι → σ) [graded_ring ℳ]
include A

lemma ideal.homogeneous_hull.gc : galois_connection (ideal.homogeneous_hull ℳ) to_ideal :=
λ I J, ⟨
  le_trans (ideal.le_to_ideal_homogeneous_hull _ _),
  λ H, J.homogeneous_hull_to_ideal_eq_self ▸ ideal.homogeneous_hull_mono ℳ H⟩

/-- `ideal.homogeneous_hull ℳ` and `to_ideal : homogeneous_ideal ℳ → ideal A` form a galois
insertion-/
def ideal.homogeneous_hull.gi : galois_insertion (ideal.homogeneous_hull ℳ) to_ideal :=
{ choice := λ I H, ⟨I, le_antisymm H (I.le_to_ideal_homogeneous_hull ℳ) ▸ is_homogeneous _⟩,
  gc := ideal.homogeneous_hull.gc ℳ,
  le_l_u := λ I, ideal.le_to_ideal_homogeneous_hull _ _,
  choice_eq := λ I H, le_antisymm (I.le_to_ideal_homogeneous_hull ℳ) H}

lemma ideal.homogeneous_hull_eq_Inf (I : ideal A) :
  ideal.homogeneous_hull ℳ I = Inf { J : homogeneous_ideal ℳ | I ≤ J.to_ideal } :=
eq.symm $ is_glb.Inf_eq $ (ideal.homogeneous_hull.gc ℳ).is_least_l.is_glb

end galois_connection