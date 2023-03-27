import algebra.module.linear_map
-- import algebra.module.graded_module
import ring_theory.graded_algebra.homogeneous_ideal
import ring_theory.ideal.quotient

section Nat_module

example {β : Type*} [add_comm_monoid β] : module ℕ β := add_comm_monoid.nat_module

example {β γ : Type*} [add_comm_monoid β] [add_comm_monoid γ] (f : β →+ γ) : β →ₗ[ℕ] γ :=  
{ to_fun := f,
  map_add' := f.map_add, 
  map_smul' := λ r x, by simp only [map_nsmul, eq_nat_cast, nat.cast_id] }

example {β γ : Type*} [add_comm_monoid β] [add_comm_monoid γ] (f : β →+ γ) : β →ₗ[ℕ] γ := 
f.to_nat_linear_map 

end Nat_module

section Int_module

example {β : Type*} [add_comm_group β]: module ℤ β := add_comm_group.int_module β

example {β γ : Type*} [add_comm_group β] [add_comm_group γ] (f : β →+ γ) : β →ₗ[ℤ] γ :=
{ to_fun := f,
  map_add' := f.map_add, 
  map_smul' := λ r x, by simp only [eq_int_cast, int.cast_id, map_zsmul f r x] }

example {β γ : Type*} [add_comm_group β] [add_comm_group γ] (f : β →+ γ) : β →ₗ[ℤ] γ :=
f.to_int_linear_map 

end Int_module

section direct_sum

variables {ι : Type*} [decidable_eq ι]

variables {R : Type*} [comm_semiring R]

lemma direct_sum.mk_apply {β : ι → Type*} [Π i, add_comm_monoid (β i)] (s : finset ι)
  (f : Π (i : s), β ↑i) (i : ι) : direct_sum.mk β s f i = dite (i ∈ s) (λ h, f ⟨i, h⟩) (λ h, 0) :=
rfl

-- Three versions of a direct sum of maps (for add_monoid_hom, stuff with classes, and linear maps,
-- which should be upgraded to classes as well)
def direct_sum.map {β γ : ι → Type*} [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  (h : Π i, β i →+ γ i) : direct_sum ι β →+ direct_sum ι γ :=
direct_sum.to_add_monoid (λ i, add_monoid_hom.comp (direct_sum.of γ i) (h i))

def direct_sum.map' {β γ : ι → Type*} [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  {F : Π (i : ι), Type*} [Π i, add_monoid_hom_class (F i) (β i) (γ i)] (h : Π i, F i) : 
  direct_sum ι β →+ direct_sum ι γ :=
direct_sum.to_add_monoid (λ i, add_monoid_hom.comp (direct_sum.of γ i) (h i))

example {β γ : ι → Type*} [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  (h : Π i, β i →+ γ i) : direct_sum.map' h = direct_sum.map h :=  rfl

def direct_sum.lmap {β γ : ι → Type*} [Π i, add_comm_monoid (β i)] [Π i, module R (β i)]
  [Π i, add_comm_monoid (γ i)] [Π i, module R (γ i)] (h : Π i, β i →ₗ[R] γ i) : 
  direct_sum ι β →ₗ[R] direct_sum ι γ :=
direct_sum.to_module R ι _ (λ i, linear_map.comp (direct_sum.lof R ι γ i) (h i))

lemma direct_sum.lmap_eq_map {β γ : ι → Type*} [Π i, add_comm_monoid (β i)] [Π i, module R (β i)]
  [Π i, add_comm_monoid (γ i)] [Π i, module R (γ i)] (h : Π i, β i →ₗ[R] γ i) : 
(direct_sum.lmap h).to_add_hom = direct_sum.map (λ i, (h i).to_add_monoid_hom) := rfl

def direct_sum.lmap' {β γ : ι → Type*} [Π i, add_comm_monoid (β i)] [Π i, module R (β i)]
  [Π i, add_comm_monoid (γ i)] [Π i, module R (γ i)] {F : Π (i : ι), Type*}
  [Π i, linear_map_class (F i) R (β i) (γ i)] (h : Π i, F i) :
  direct_sum ι β →ₗ[R] direct_sum ι γ :=
direct_sum.to_module R ι (direct_sum ι γ)
  (λ i, linear_map.comp (direct_sum.lof R ι γ i)⟨h i, map_add _, map_smulₛₗ _⟩)

example {β : Type*} [add_comm_monoid β] : module ℕ β := add_comm_monoid.nat_module

example {β γ : Type*} [add_comm_monoid β] [add_comm_monoid γ] (f : β →+ γ) : β →ₗ[ℕ] γ :=
{ to_fun := f,
  map_add' := f.map_add, 
  map_smul' := λ r x, by simp only [map_nsmul, eq_nat_cast, nat.cast_id] }

example {β : Type*} [add_comm_group β]: module ℤ β := 
  add_comm_group.int_module β

example {β γ : Type*} [add_comm_group β] [add_comm_group γ] (f : β →+ γ) : β →ₗ[ℤ] γ :=
{ to_fun := f,
  map_add' := f.map_add, 
  map_smul' := λ r x, by simp only [eq_int_cast, int.cast_id, map_zsmul f r x] }

-- I want this as a linear map, as well
/- def direct_sum.component' {β : ι → Type* } [Π i, add_comm_monoid (β i)] (i : ι) :
  direct_sum ι β →ₗ[ℕ] β i := 
direct_sum.component ℕ ι β i  -/

-- I think this is `direct_sum.apply_eq_component`
/- lemma direct_sum.component'_eq {β : ι → Type* } [Π i, add_comm_monoid (β i)] 
(x : direct_sum ι β) (i : ι):
  direct_sum.component' i x = x i := rfl -/


-- This is direct_sum.ext_iff (except that Lean doesn't know which ring it should use)
/- lemma direct_sum.eq_iff_component'_eq {β : ι → Type* } [Π i, add_comm_monoid (β i)]
  (x y : direct_sum ι β) : x = y ↔  ∀ i, direct_sum.component' i x = direct_sum.component' i y :=
by simp only [dfinsupp.ext_iff, direct_sum.component'_eq]  -/

lemma direct_sum.mk_eq_sum' {β : ι → Type*} [Π i, add_comm_monoid (β i)]
  [Π (i : ι) (x : β i), decidable (x ≠ 0)] (s : finset ι) (f : Π i, β i) :
  direct_sum.mk β s (λ (i : ↥↑s), f i) = s.sum (λ i, direct_sum.of β i (f i)) := 
begin
  ext i,
  rw [direct_sum.mk_apply, dfinsupp.finset_sum_apply],
  split_ifs with hi hi,
  { rw finset.sum_eq_single_of_mem i hi,
    { rw [← direct_sum.lof_eq_of ℕ, direct_sum.lof_apply],
      refl },
    { intros j hj hij,
      exact direct_sum.of_eq_of_ne _ _ _ _ hij }},
  { apply symm,
    apply finset.sum_eq_zero,
    intros j hj, 
    exact direct_sum.of_eq_of_ne _ _ _ _ (ne_of_mem_of_not_mem hj hi) },
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

def direct_sum.map_to {β : ι → Type*} [Π  i, add_comm_monoid (β i)] {γ : Type*} [add_comm_monoid γ]
  (h : Π i, β i →+ γ) : direct_sum ι β →+ γ :=
direct_sum.to_add_monoid h

lemma direct_sum.mk_eq_sum {β : ι → Type*} [Π  i, add_comm_monoid (β i)]
  [Π (i : ι) (x : β i), decidable (x ≠ 0)] (s : finset ι) (x : Π (i : s), β i) :
  direct_sum.mk β s x 
    = s.sum (λ i, direct_sum.of β i (dite (i ∈ s) (λ hi, x ⟨i, hi⟩) (λ hi, 0) )) :=
begin
  ext i,
  rw [dfinsupp.finset_sum_apply, direct_sum.mk_apply],
  split_ifs with hi hi,
  { rw finset.sum_eq_single i, 
    { rw [direct_sum.of_eq_same, dif_pos hi] },
    { intros j hjs hji,
      exact direct_sum.of_eq_of_ne _ _ _ _ hji},
    { intro his,
      rw [direct_sum.of_eq_same, dif_neg his] }},
  { apply symm, apply finset.sum_eq_zero, 
    intros j hj, 
    rw direct_sum.of_eq_of_ne  _ _ _ _ (ne_of_mem_of_not_mem hj hi) },
end

lemma direct_sum.to_add_monoid_mk {β : ι → Type*} [Π  i, add_comm_monoid (β i)] {γ : Type*}
  [add_comm_monoid γ] [Π (i : ι) (x : β i), decidable (x ≠ 0)] [Π (x : γ), decidable (x ≠ 0)]
  (ψ : Π i, (β i →+ γ)) (s : finset ι) (x : Π (i : s), β i) :
  direct_sum.to_add_monoid ψ (direct_sum.mk β s x)
    = s.sum (λ i, ψ i (dite (i ∈ s) (λ hi, x ⟨i, hi⟩) (λ hi, 0))) :=
begin
  rw [direct_sum.mk_eq_sum, map_sum], 
  apply finset.sum_congr rfl,
  intros i hi,
  rw direct_sum.to_add_monoid_of,
end

lemma direct_sum.map_of {β γ : ι → Type*} [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  [Π (i : ι) (x : β i), decidable (x ≠ 0)] [Π (i : ι) (x : γ i), decidable (x ≠ 0)]
  (h : Π i, β i →+ γ i) (i : ι) (x : β i) : 
  direct_sum.map h (direct_sum.of β i x) = direct_sum.of γ i (h i x) := 
begin
  dsimp only [direct_sum.map],
  rw direct_sum.to_add_monoid_of , 
  simp only [add_monoid_hom.coe_comp],
end

lemma direct_sum.map_apply' {β γ : ι → Type*} [Π i, add_comm_monoid (β i)]
  [Π i, add_comm_monoid (γ i)] [Π (i : ι) (x : β i), decidable (x ≠ 0)] 
  [Π (i : ι) (x : γ i), decidable (x ≠ 0)] (h : Π i, β i →+ γ i) (x : direct_sum ι β) : 
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

lemma direct_sum.map_apply {β γ : ι → Type*} [Π i, add_comm_monoid (β i)]
  [Π i, add_comm_monoid (γ i)] [Π (i : ι) (x : β i), decidable (x ≠ 0)] 
  [Π (i : ι) (x : γ i), decidable (x ≠ 0)] (h : Π i, β i →+ γ i) (x : direct_sum ι β) (i : ι) : 
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

lemma direct_sum.lmap_apply {β γ : ι → Type*} [Π i, add_comm_monoid (β i)] [Π i, module R (β i)]
  [Π i, add_comm_monoid (γ i)] [Π i, module R (γ i)] [Π (i : ι) (x : β i), decidable (x ≠ 0)]
  [Π (i : ι) (x : γ i), decidable (x ≠ 0)] (h : Π i, β i →ₗ[R] γ i) (x : direct_sum ι β) (i : ι) : 
  direct_sum.lmap h x i = h i (x i) :=
begin
  have h_map : direct_sum.lmap h x = (direct_sum.lmap h).to_add_hom x := rfl,
  rw [h_map, direct_sum.lmap_eq_map, add_monoid_hom.coe_eq_to_add_hom, 
    add_monoid_hom.to_add_hom_coe, direct_sum.map_apply],
  refl,
end

-- I'll skip this sorry since we have a proof above
lemma direct_sum.map_apply_2 {β γ : ι → Type*} [Π i, add_comm_monoid (β i)]
  [Π i, add_comm_monoid (γ i)] [Π (i : ι) (x : β i), decidable (x ≠ 0)] 
  [Π (i : ι) (x : γ i), decidable (x ≠ 0)] (h : Π i, β i →+ γ i) (x : direct_sum ι β) (i : ι) : 
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
  sorry, sorry
end

end direct_sum

section graded_quot

variables {ι : Type*} [decidable_eq ι] [add_monoid ι]
variables {A : Type*} [comm_ring A] [decidable_eq A]
variables {σ : Type*} [set_like σ A] [add_submonoid_class σ A] 

-- Is this not the way to do it ?
-- variables (𝒜 : ι → σ ) 
variables (𝒜 : ι → submodule ℤ A) [h𝒜 : graded_ring 𝒜] 

variables (I : ideal A) (hI: ideal.is_homogeneous 𝒜 I)

-- It seems I start understanding what I'm doing
instance : semilinear_map_class (A →+* A ⧸ I) (ring_hom.id ℤ) _ _ :=
{ coe            := λ f a, f a,
  coe_injective' := λ f g hfg, ring_hom.ext (λ x, function.funext_iff.mp hfg x),
  map_add        := map_add, 
  map_smulₛₗ     := λ f r a, 
                    by simp only [zsmul_eq_mul, map_mul, map_int_cast, eq_int_cast, int.cast_id] }

/-- The graded pieces of A ⧸ I -/
def quot_submodule : ι → submodule ℤ (A ⧸ I) := λ i, submodule.map (ideal.quotient.mk I) (𝒜 i)

-- I think this one can be erased, since we have the laux version
/-- The decomposition at the higher level -/
def quot_decompose_aux [graded_ring 𝒜] :
  A → direct_sum ι (λ (i : ι), ↥(quot_submodule 𝒜 I i)) := λ a,
begin
  refine (direct_sum.map _) (direct_sum.decompose 𝒜 a),
  exact λ i, {
  to_fun := λu, ⟨ideal.quotient.mk I ↑u,
  begin
    simp [quot_submodule, submodule.mem_map],
    exact ⟨↑u, u.prop, rfl⟩,
  end⟩,
  map_zero' := by simp only [←subtype.coe_inj, submodule.coe_zero, map_zero, submodule.coe_mk],
  map_add' := λ u v, by simp only [←subtype.coe_inj, submodule.coe_add, map_add,
                add_mem_class.mk_add_mk] },
end

def quot_comp_map (i : ι) : ↥(𝒜 i) →ₗ[ℤ] ↥(quot_submodule 𝒜 I i) := 
{ to_fun    := λ u, ⟨ideal.quotient.mk I ↑u,
                 by rw [quot_submodule,submodule.mem_map]; exact ⟨↑u, u.prop, rfl⟩⟩,
  map_add'  := λ u v, by simp only [←subtype.coe_inj, submodule.coe_add, map_add,
                 add_mem_class.mk_add_mk],
  map_smul' := λ r u, by simp only [submodule.coe_smul_of_tower, zsmul_eq_mul, map_mul,
                 map_int_cast, eq_int_cast, int.cast_id, set_like.mk_smul_mk] }

--lemma quot_comp_map_surjective (i : ι) : function.surjective (quot_comp_map 𝒜 I i) := sorry

/-- The decomposition at the higher level -/
def quot_decompose_laux [graded_ring 𝒜] :
  A →ₗ[ℤ] direct_sum ι (λ (i : ι), ↥(quot_submodule 𝒜 I i)) :=
linear_map.comp (direct_sum.lmap (quot_comp_map 𝒜 I)) 
  (direct_sum.decompose_alg_equiv 𝒜).to_linear_map


lemma test [graded_ring 𝒜] 
  [Π (i : ι) (x : ↥(quot_submodule 𝒜 I i)), decidable (x ≠ 0)] : 
  add_subgroup.to_int_submodule (submodule.to_add_subgroup I) ≤
    linear_map.ker (quot_decompose_laux 𝒜 I) := 
begin
  intros x hx,
  rw [linear_map.mem_ker, quot_decompose_laux, linear_map.comp_apply],
  ext i,
  rw [set_like.coe_eq_coe, direct_sum.lmap_apply, alg_equiv.to_linear_map_apply,
    direct_sum.decompose_alg_equiv_apply, direct_sum.zero_apply,  quot_comp_map,
    linear_map.coe_mk, submodule.mk_eq_zero],
  change (ideal.quotient.mk I) ((direct_sum.decompose 𝒜) x i : A) = 0, --TODO: remove
  rw ideal.quotient.eq_zero_iff_mem,
  --simp only,
    --change ((direct_sum.decompose 𝒜).symm.symm x i : A) ∈ I
  sorry
end

-- I have no idea why this is so slow
/-- The decomposition at the higher level -/
def quot_decompose [graded_ring 𝒜]
  [Π (i : ι) (x : ↥(quot_submodule 𝒜 I i)), decidable (x ≠ 0)] :
  A ⧸ I →ₗ[ℤ] direct_sum ι (λ (i : ι), ↥(quot_submodule 𝒜 I i)) :=
begin
  apply submodule.liftq (I.to_add_subgroup).to_int_submodule (quot_decompose_laux 𝒜 I),
  apply test 𝒜 I,
end 

example : decidable_eq (A ⧸ I) := 
begin
  intros x y,
  sorry
end

def quot_decomposition [graded_ring 𝒜]
  [Π (i : ι) (x : ↥(quot_submodule 𝒜 I i)), decidable (x ≠ 0)] :
  direct_sum.decomposition (quot_submodule 𝒜 I) :=
{ decompose' := quot_decompose 𝒜 I,
  left_inv   := sorry,
  right_inv  := sorry }

def graded_quot_alg [decidable_eq (A ⧸ I)] [graded_ring 𝒜] :
  graded_algebra (quot_submodule 𝒜 I) :=
{ to_decomposition  := quot_decomposition 𝒜 I,
  to_graded_monoid  :=
  { one_mem := by rw [quot_submodule, submodule.mem_map]; exact ⟨1, set_like.one_mem_graded 𝒜, rfl⟩,
    mul_mem := sorry }}

-- variable (rel : A → A → Prop) 

-- open_locale big_operators


/- 
def weights [graded_ring 𝒜] [Π (i : ι) (x : ↥(𝒜 i)), decidable (x ≠ 0)] (a : A) := 
dfinsupp.support (direct_sum.decompose 𝒜 a)

def is_homogenous [graded_ring 𝒜] [Π (i : ι) (x : ↥(𝒜 i)), decidable (x ≠ 0)] (a : A) :=
subsingleton (weights 𝒜 a)
-/

example (R S : Type*) [comm_ring R] [comm_ring S] (f : R →+* S)
 (I : submonoid R) : submonoid S :=  submonoid.map f I

example (R : Type*) [comm_ring R] (I : ideal R) (M : ideal R) : ideal (R ⧸ I) :=
ideal.map (ideal.quotient.mk I) M

example (R S : Type*) [comm_ring R] [comm_ring S] (f : R →+* S)
 (I : ideal R) : ideal S := ideal.map f I

def graded_quot_submonoid (𝒜 : ι → σ) : ι → add_submonoid (A ⧸ I) :=
λ i, add_submonoid.map (ideal.quotient.mk I) ⟨𝒜 i, λ _ _, add_mem, zero_mem _⟩

def graded_quot_submonoid' (𝒜 : ι → submodule ℤ A) : ι → add_submonoid (A ⧸ I) :=
begin
  sorry
  --haveI : 
  --exact λ i, submodule.map (ideal.quotient.mk I) (𝒜 i)
end

example (i : ι) : add_comm_monoid (graded_quot_submonoid I 𝒜 i) := 
infer_instance

noncomputable
def quot_some : A ⧸ I → A := function.surj_inv (ideal.quotient.mk_surjective)

example (a : A ⧸ I) : ideal.quotient.mk I (quot_some I a) = a := 
  function.surj_inv_eq _ _


noncomputable
def toto := λ a i, ideal.quotient.mk I ((h𝒜.decompose' (quot_some I a)) i)


noncomputable
def tata := λ a, dfinsupp.support (h𝒜.decompose' (quot_some I a))

lemma direct_sum.comp_to_add_monoid {ι : Type*} [dec_ι : decidable_eq ι] {β : ι → Type*}
  [Π (i : ι), add_comm_monoid (β i)] {γ δ : Type*} [add_comm_monoid γ] [add_comm_monoid δ]
  (f : γ →+ δ) (φ : Π (i : ι), β i →+ γ) :
  f.comp (direct_sum.to_add_monoid φ) = direct_sum.to_add_monoid (λ i, f.comp (φ i)) :=
begin
  apply direct_sum.add_hom_ext,
  intros i y,
  simp only [direct_sum.to_add_monoid_of, add_monoid_hom.coe_comp, function.comp_app],
end

example {ι : Type*} [dec_ι : decidable_eq ι] {β : ι → Type*} [Π (i : ι), add_comm_monoid (β i)]
  {γ δ : Type*} [add_comm_monoid γ] [add_comm_monoid δ] (f : γ →+ δ) (φ : Π (i : ι), β i →+ γ)
  (x : direct_sum ι β) :
  f (direct_sum.to_add_monoid φ x) = direct_sum.to_add_monoid (λ i, f.comp (φ i)) x :=
by rw [← add_monoid_hom.comp_apply, direct_sum.comp_to_add_monoid]

instance asdf : Π (i : ι), add_comm_monoid ((λ (i : ι), ↥(graded_quot_submonoid I 𝒜 i)) i) := sorry
example  [Π (x : A), decidable (x ≠ 0)] 
  [Π (i : ι) (x : ↥(graded_quot_submonoid I 𝒜 i)), decidable (x ≠ 0)]
  [decidable_pred (λ x, x ∈ I)] :
  -- [h𝒜 : graded_ring 𝒜] :
  A → direct_sum ι (λ (i : ι), ↥(graded_quot_submonoid I 𝒜 i)) := λ a,
begin
  haveI : Π i, add_comm_monoid (𝒜 i), intro i, apply_instance,
  suffices hh : direct_sum ι (λ i, 𝒜 i) →+ direct_sum ι (λ i, graded_quot_submonoid I 𝒜 i),

  sorry,
  -- exact hh (direct_sum.decompose 𝒜 a),
   
  apply direct_sum.map,
  /- intro i,
  let h : Π i, (𝒜 i) →+ graded_quot_submonoid 𝒜 I i := 
  -/
  exact λ i, {
  to_fun := λu,  
  begin
    use ideal.quotient.mk I ↑u,
    simp only [graded_quot_submonoid, add_submonoid.mem_map, add_submonoid.mem_mk, set_like.mem_coe,
      exists_prop],
    exact ⟨↑u, u.prop, rfl⟩,
  end,
  map_zero' := 
  begin
    rw ←subtype.coe_inj, 
    simp only [add_submonoid.coe_zero, map_zero, set_like.coe_mk],
    sorry

--    simp only [zero_mem_class.coe_eq_zero],

--    simp only [zero_mem_class.coe_zero, map_zero, set_like.coe_mk],
  end,
  map_add' := λ u v, 
  begin
    rw ←subtype.coe_inj, 
    sorry --simp only [add_mem_class.coe_add, map_add, add_submonoid.mk_add_mk],
  end, },
  /- haveI : Π i, add_comm_monoid (𝒜 i), intro i, apply_instance,
  have hh : direct_sum ι (λ i, 𝒜 i) →+ direct_sum ι (λ i, graded_quot_submonoid 𝒜 I i),
  apply direct_sum.map, -/

end


example [Π (x : A), decidable (x ≠ 0)] 
 [Π (i : ι) (x : ↥(graded_quot_submonoid I 𝒜 i)), decidable (x ≠ 0)]
 [decidable_pred (λ x, x ∈ I)] : 
  direct_sum.decomposition (graded_quot_submonoid I 𝒜) := sorry/-  {
decompose'  :=  
/- direct_sum.mk 
  (λ i, (graded_quot_submonoid 𝒜 I i)) 
  (dfinsupp.support (h𝒜.decompose' (quot_some I a))) 
  (λ i, ⟨ideal.quotient.mk I ((h𝒜.decompose' (quot_some I a)) i), 
   add_submonoid.mem_map_of_mem _ (by 
    simp only [subtype.val_eq_coe, add_submonoid.mem_mk, set_like.mem_coe, set_like.coe_mem])⟩), -/
  begin
    sorry
  end,

left_inv    := λ a,
begin
  /- have : ideal.quotient.mk I (quot_some I a) = a := 
  function.surj_inv_eq _ _,
  conv_rhs { rw ← this, rw ← h𝒜.left_inv (quot_some I a), },

  dsimp only,
  
  generalize : direct_sum.decomposition.decompose' (quot_some I a) = b, 
  resetI,
  rw [direct_sum.to_add_monoid.unique], 

  rw ← add_monoid_hom.comp_apply,  
  have : (ideal.quotient.mk I) ((direct_sum.coe_add_monoid_hom 𝒜) b) =
    (ideal.quotient.mk I).to_add_monoid_hom.comp (direct_sum.coe_add_monoid_hom 𝒜) b,
  rw add_monoid_hom.comp_apply, refl,
  rw this, 

  dsimp,

simp_rw direct_sum.to_add_monoid_mk, 

  have : ∀ i, (direct_sum.coe_add_monoid_hom (graded_quot_submonoid 𝒜 I)).comp
  (direct_sum.of (λ (i : ι), ↥(graded_quot_submonoid 𝒜 I i)) i) = _,  -/sorry,


end,
right_inv   := λ a,
begin
  dsimp,
  ext i,
  sorry, 
end } -/

--sorry
/- def graded_ring_quot : graded_ring (graded_quot_submonoid 𝒜 I hI) :=
sorry 

#check graded_quot

example (I : ideal A) [graded_ring 𝒜] (hI: ideal.is_homogeneous 𝒜 I) :
  graded_algebra (graded_quot 𝒜 I hI) := 
begin
end -/

end graded_quot