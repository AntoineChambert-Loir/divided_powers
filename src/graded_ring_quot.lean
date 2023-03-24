-- import algebra.module.graded_module
import ring_theory.graded_algebra.homogeneous_ideal
import ring_theory.ideal.quotient

section direct_sum

variables {ι : Type*} [decidable_eq ι]

lemma direct_sum.mk_apply {β : ι → Type*} [Π i, add_comm_monoid (β i)] 
  (s : finset ι) (f : Π (i : s), β ↑i) (i : ι): 
  direct_sum.mk β s f i = dite (i ∈ s) (λ h, f ⟨i, h⟩) (λ h, 0) := rfl

def direct_sum.map {β γ : ι → Type*} [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)] (h : Π i, β i →+ γ i): 
  direct_sum ι β →+ direct_sum ι γ :=
 direct_sum.to_add_monoid (λ i, add_monoid_hom.comp (direct_sum.of γ i) (h i))

def direct_sum.component' {β : ι → Type* } [Π i, add_comm_monoid (β i)] (i : ι):
  direct_sum ι β →+ β i := {
to_fun := λ x, x i,
map_zero' := direct_sum.zero_apply β i,
map_add' := λ x y, direct_sum.add_apply  x y i, }

lemma direct_sum.component'_eq {β : ι → Type* } [Π i, add_comm_monoid (β i)] 
(x : direct_sum ι β) (i : ι):
  direct_sum.component' i x = x i := rfl

lemma direct_sum.eq_iff_component'_eq {β : ι → Type* } [Π i, add_comm_monoid (β i)] (x y : direct_sum ι β) : x = y ↔  ∀ i, direct_sum.component' i x = direct_sum.component' i y := by simp only [dfinsupp.ext_iff, direct_sum.component'_eq]

lemma direct_sum.mk_eq_sum' {β : ι → Type*} [Π i, add_comm_monoid (β i)]
  [Π (i : ι) (x : β i), decidable (x ≠ 0)] (s : finset ι) (f : Π i, β i) :
  direct_sum.mk β s (λ (i : ↥↑s), f i) = s.sum (λ i, direct_sum.of β i (f i)) := 
begin
  ext i,
  rw direct_sum.mk_apply,
  rw ← direct_sum.component'_eq,  rw map_sum,
  split_ifs with hi hi,
  { rw finset.sum_eq_single_of_mem i hi,
    { rw direct_sum.component'_eq, 
      rw direct_sum.of_eq_same, refl, },
    { intros j hj hij, 
      rw direct_sum.component'_eq,
      rw direct_sum.of_eq_of_ne,
      exact hij, }, },
  { apply symm, apply finset.sum_eq_zero, 
    intros j hj,
    rw direct_sum.component'_eq, 
    rw direct_sum.of_eq_of_ne,
    intro hij, apply hi, rw ← hij, exact hj, },
end

lemma dfinsupp.mk_eq_sum {β : ι → Type*} [Π i, add_comm_monoid (β i)]
  [Π (i : ι) (x : β i), decidable (x ≠ 0)] (s : finset ι) (f : Π i, β i) :
  dfinsupp.mk s (λ (i : ↥↑s), f i) = s.sum (λ i, direct_sum.of β i (f i)) := 
begin
  ext i,
  simp only [dfinsupp.mk_apply, dfinsupp.finset_sum_apply], 
  split_ifs with hi hi,
  { rw finset.sum_eq_single_of_mem i hi,
    rw direct_sum.of_eq_same, refl,
    intros j hj hij, 
    rw direct_sum.of_eq_of_ne,
    exact hij, },
  { apply symm, apply finset.sum_eq_zero, 
    intros j hj,
    rw direct_sum.of_eq_of_ne,
    intro hij, apply hi, rw ← hij, exact hj, },
end

def direct_sum.map_to {β : ι → Type*} [Π  i, add_comm_monoid (β i)]
 {γ : Type*} [add_comm_monoid γ] (h : Π i, β i →+ γ) :
  direct_sum ι β →+ γ := direct_sum.to_add_monoid h

lemma direct_sum.mk_eq_sum {β : ι → Type*} [Π  i, add_comm_monoid (β i)]
 [Π (i : ι) (x : β i), decidable (x ≠ 0)] 
 (s : finset ι) (x : Π (i : s), β i):
 direct_sum.mk β s x 
 = s.sum (λ i, direct_sum.of β i (dite (i ∈ s) (λ hi, x ⟨i, hi⟩) (λ hi, 0) )) :=
begin
  ext i,
  conv_rhs { rw ← direct_sum.component'_eq, },
  rw map_sum,
  rw direct_sum.mk_apply,
  split_ifs with hi hi,
  { rw finset.sum_eq_single i, rw direct_sum.component'_eq, 
    simp only [direct_sum.of_eq_same, dif_pos hi],
    intros j hjs hji,
    rw direct_sum.component'_eq, rw direct_sum.of_eq_of_ne, exact hji,
    intro his, rw direct_sum.component'_eq, rw direct_sum.of_eq_same,
      rw dif_neg his, },
  { apply symm, apply finset.sum_eq_zero, 
    intros j hj, 
    rw direct_sum.component'_eq, rw direct_sum.of_eq_of_ne,
    intro hji, apply hi, rw ← hji, exact hj, },

end

lemma direct_sum.to_add_monoid_mk {β : ι → Type*} [Π  i, add_comm_monoid (β i)]
 {γ : Type*} [add_comm_monoid γ] 
 [Π (i : ι) (x : β i), decidable (x ≠ 0)] [Π (x : γ), decidable (x ≠ 0)]
 (ψ : Π i, (β i →+ γ)) (s : finset ι)
 (x : Π (i : s), β i) : direct_sum.to_add_monoid ψ (direct_sum.mk β s x)
  = s.sum (λ i, ψ i (dite (i ∈ s) (λ hi, x ⟨i, hi⟩) (λ hi, 0))) :=
begin
  rw [direct_sum.mk_eq_sum, map_sum], 
  apply finset.sum_congr rfl,
  intros i hi,
  rw direct_sum.to_add_monoid_of,
end

lemma direct_sum.map_of {β γ : ι → Type*} [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
[Π (i : ι) (x : β i), decidable (x ≠ 0)] 
[Π (i : ι) (x : γ i), decidable (x ≠ 0)]
(h : Π i, β i →+ γ i) (i : ι) (x : β i) : 
  direct_sum.map h (direct_sum.of β i x) = 
  direct_sum.of γ i (h i x) := 
begin
  dsimp only [direct_sum.map],
  rw direct_sum.to_add_monoid_of , 
  simp only [add_monoid_hom.coe_comp],
end

lemma direct_sum.map_apply' {β γ : ι → Type*} [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
[Π (i : ι) (x : β i), decidable (x ≠ 0)] 
[Π (i : ι) (x : γ i), decidable (x ≠ 0)]
(h : Π i, β i →+ γ i) (x : direct_sum ι β) : 
  direct_sum.map h x = direct_sum.mk γ (x.support) (λ i, h i (x i)) := 
begin
  conv_lhs {rw ← direct_sum.sum_support_of β x, },
  rw map_sum,
  simp_rw direct_sum.map_of, 
  apply symm,
  convert direct_sum.mk_eq_sum (x.support) (λ i, (h i) (x i)),
  apply funext, 
  intro i, 
  dsimp, 
  apply congr_arg,
  split_ifs with hi, 
  refl,
  rw dfinsupp.not_mem_support_iff at hi,
  rw hi, simp only [map_zero],
end

lemma direct_sum.map_apply {β γ : ι → Type*} [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
[Π (i : ι) (x : β i), decidable (x ≠ 0)] 
[Π (i : ι) (x : γ i), decidable (x ≠ 0)]
(h : Π i, β i →+ γ i) (x : direct_sum ι β) (i : ι): 
  direct_sum.map h x i = h i (x i) :=
begin
 /-  rw direct_sum.map_apply',
  rw ← direct_sum.component'_eq, 
  rw direct_sum.mk_eq_sum, 
  rw map_sum, 
  simp_rw direct_sum.component'_eq,  
-/
 -- Ci-dessous : preuve qui marche
  rw direct_sum.map_apply',
  simp only [direct_sum.mk, dfinsupp.mk_apply, add_monoid_hom.coe_mk],
  simp only [dfinsupp.mem_support_to_fun, ne.def],
  split_ifs with hi hi,
  rw hi, rw map_zero,
  refl, 
end

lemma direct_sum.map_apply_2 {β γ : ι → Type*} [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
[Π (i : ι) (x : β i), decidable (x ≠ 0)] 
[Π (i : ι) (x : γ i), decidable (x ≠ 0)]
(h : Π i, β i →+ γ i) (x : direct_sum ι β) (i : ι): 
  direct_sum.map h x i = h i (x i) :=
begin
  rw direct_sum.to_add_monoid.unique, 
  have this : (λ j, (direct_sum.map h).comp (direct_sum.of β j)) 
    = λ j, ((direct_sum.of γ j).comp (h j)), 
  { apply funext,
    intro j, 
    ext y,
    simp only [add_monoid_hom.comp_apply, direct_sum.map_of], },
  rw this, 
  
--  have := direct_sum.sum_support_of β x,
  conv_lhs {rw ← direct_sum.sum_support_of β x, },
  rw map_sum, 
  rw finset.sum_eq_single i,
  rw direct_sum.to_add_monoid_of,
  rw add_monoid_hom.comp_apply,
  rw direct_sum.of_eq_same , 
  intros j hjx hji, 

end

end direct_sum



section graded_quot

variables {ι : Type*} [decidable_eq ι] [add_monoid ι]
variables {A : Type*} [comm_ring A] [decidable_eq A]
variables {σ : Type*} [set_like σ A] [add_submonoid_class σ A] 

variable (𝒜 : ι → σ)
variable (rel : A → A → Prop) 

-- open_locale big_operators


/- 
def weights [graded_ring 𝒜] [Π (i : ι) (x : ↥(𝒜 i)), decidable (x ≠ 0)] (a : A) := 
dfinsupp.support (direct_sum.decompose 𝒜 a)

def is_homogenous [graded_ring 𝒜] [Π (i : ι) (x : ↥(𝒜 i)), decidable (x ≠ 0)] (a : A) :=
subsingleton (weights 𝒜 a)
-/

example (R S : Type*) [comm_ring R] [comm_ring S] (f : R →+* S)
 (I : submonoid R) : submonoid S :=  submonoid.map f I

example (R : Type*) [comm_ring R] (I : ideal R) (M : ideal R) : ideal (R ⧸ I) := ideal.map (ideal.quotient.mk I) M

example (R S : Type*) [comm_ring R] [comm_ring S] (f : R →+* S)
 (I : ideal R) : ideal S := ideal.map f I

variables (I : ideal A) [h𝒜 : graded_ring 𝒜] (hI: ideal.is_homogeneous 𝒜 I)

def graded_quot_submonoid : ι → add_submonoid (A ⧸ I) :=
λ i, add_submonoid.map (ideal.quotient.mk I) ⟨𝒜 i, λ _ _, add_mem, zero_mem _⟩

instance (i : ι) : add_comm_monoid (graded_quot_submonoid 𝒜 I i) := 
infer_instance

noncomputable
def quot_some : A ⧸ I → A := function.surj_inv (ideal.quotient.mk_surjective)

example (a : A ⧸ I) : ideal.quotient.mk I (quot_some I a) = a := 
  function.surj_inv_eq _ _


noncomputable
def toto := λ a i, ideal.quotient.mk I ((h𝒜.decompose' (quot_some I a)) i)


noncomputable
def tata := λ a, dfinsupp.support (h𝒜.decompose' (quot_some I a))



noncomputable 
example [Π (x : A), decidable (x ≠ 0)] 
 [Π (i : ι) (x : ↥(graded_quot_submonoid 𝒜 I i)), decidable (x ≠ 0)]
 [decidable_pred (λ x, x ∈ I)]: 
  direct_sum.decomposition (graded_quot_submonoid 𝒜 I) := {
decompose'  := λ a, direct_sum.mk 
  (λ i, (graded_quot_submonoid 𝒜 I i)) 
  (dfinsupp.support (h𝒜.decompose' (quot_some I a))) 
  (λ i, ⟨ideal.quotient.mk I ((h𝒜.decompose' (quot_some I a)) i), 
   add_submonoid.mem_map_of_mem _ (by 
    simp only [subtype.val_eq_coe, add_submonoid.mem_mk, set_like.mem_coe, set_like.coe_mem])⟩),
left_inv    := λ a,
begin
  have : ideal.quotient.mk I (quot_some I a) = a := 
  function.surj_inv_eq _ _,
  conv_rhs { rw ← this, rw ← h𝒜.left_inv (quot_some I a), },

  dsimp only,
  
  generalize : direct_sum.decomposition.decompose' (quot_some I a) = b, 
  resetI,
  
  rw [direct_sum.to_add_monoid.unique], 
  rw ← add_monoid_hom.comp_apply,  
  have : (ideal.quotient.mk I) ((direct_sum.coe_add_monoid_hom 𝒜) b) = (ideal.quotient.mk I).to_add_monoid_hom.comp (direct_sum.coe_add_monoid_hom 𝒜) b,
  rw add_monoid_hom.comp_apply, refl,
  rw this, 
  conv_rhs {rw direct_sum.to_add_monoid.unique},
  dsimp,

simp_rw direct_sum.to_add_monoid_mk, 

  have : ∀ i, (direct_sum.coe_add_monoid_hom (graded_quot_submonoid 𝒜 I)).comp
  (direct_sum.of (λ (i : ι), ↥(graded_quot_submonoid 𝒜 I i)) i) = _, sorry,


end,
right_inv   := λ a,
begin
  dsimp,
  ext i,
  sorry, 
end }


def graded_ring_quot : graded_ring (graded_quot_submonoid 𝒜 I hI) :=
sorry 

#check graded_quot

example (I : ideal A) [graded_ring 𝒜] (hI: ideal.is_homogeneous 𝒜 I) : graded_algebra (graded_quot 𝒜 I hI) := 
begin
end

end graded_quot

