import algebra.module.linear_map
-- import algebra.module.graded_module
import ring_theory.graded_algebra.homogeneous_ideal
import algebra.ring_quot
import ring_theory.ideal.quotient
import ring_theory.ideal.quotient_operations

section classes

section linear_map

variables {R : Type*} [semiring R]
variables {β γ : Type*} 
  [add_comm_monoid β] [module R β] 
  [add_comm_monoid γ] [module R γ]
  
instance {F : Type*} [linear_map_class F R β γ] : has_coe_t F (β →ₗ[R] γ) := 
{ coe := λ h, ⟨h, map_add h, map_smulₛₗ h⟩ }

lemma linear_map.coe_coe {F : Type*} [linear_map_class F R β γ] (f : F) :
 ((f : β →ₗ[R] γ) : β → γ) = f := rfl 

lemma linear_map.coe_coe' {F : Type*} [linear_map_class F R β γ] (f : F) :
 ((f : β →ₗ[R] γ) : β →+ γ) = f := rfl 

example {F : Type*} [linear_map_class F R β γ] (h : F) (b : β): (h : β →ₗ[R] γ) b = h b := rfl


end linear_map

section alg_hom 

variables {R : Type*} [comm_semiring R]
variables {β γ : Type*} 
  [semiring β] [algebra R β] 
  [semiring γ] [algebra R γ]

lemma alg_hom.to_linear_map_coe_coe {F : Type*} [alg_hom_class F R β γ] (h : F) : ((h : β →ₗ[R] γ) : β → γ) = h := rfl

end alg_hom


section Nat_module

example {β : Type*} [add_comm_monoid β] : module ℕ β := add_comm_monoid.nat_module

example {β γ : Type*} [add_comm_monoid β] [add_comm_monoid γ] (f : β →+ γ) : β →ₗ[ℕ] γ :=  
{ to_fun := f,
  map_add' := f.map_add, 
  map_smul' := λ r x, by simp only [map_nsmul, eq_nat_cast, nat.cast_id] }

example {β γ : Type*} [add_comm_monoid β] [add_comm_monoid γ] (f : β →+ γ) : β →ₗ[ℕ] γ := 
f.to_nat_linear_map 

example {β γ : Type*} [add_comm_monoid β] [add_comm_monoid γ] (f : β →ₗ[ℕ] γ) : β →+ γ := 
f.to_add_monoid_hom 

example {β γ : Type*} [add_comm_monoid β] [add_comm_monoid γ] (f : β →ₗ[ℕ] γ) :
 f =  f.to_add_monoid_hom.to_nat_linear_map  := 
linear_map.ext (λ _, eq.refl _)

example {β γ : Type*} [add_comm_monoid β] [add_comm_monoid γ] (f : β →+ γ) :
  f = f.to_nat_linear_map.to_add_monoid_hom :=
add_monoid_hom.ext (λ _, eq.refl _) 

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

variables {R : Type*} [semiring R]

/-- The components of a direct sum, as add_monoid_hom -/
def direct_sum.component' {β : ι → Type* } 
  [Π i, add_comm_monoid (β i)] (i : ι) : direct_sum ι β →+ β i := 
direct_sum.component ℕ ι β i 

lemma direct_sum.component'_eq {β : ι → Type* } 
  [Π i, add_comm_monoid (β i)] (x : direct_sum ι β) (i : ι):
  direct_sum.component' i x = x i := rfl 

lemma direct_sum.eq_iff_component'_eq {β : ι → Type* } 
  [Π i, add_comm_monoid (β i)] (x y : direct_sum ι β) : 
  x = y ↔  ∀ i, direct_sum.component' i x = direct_sum.component' i y :=
direct_sum.ext_iff ℕ 

-- add_monoid_hom from a direct_sum to an add_comm_monoid 
example {β : ι → Type*} [Π  i, add_comm_monoid (β i)] {γ : Type*} [add_comm_monoid γ]
  (h : Π i, β i →+ γ) : direct_sum ι β →+ γ :=
direct_sum.to_add_monoid h

-- linear_map from a direct_sum to a module
example {β : ι → Type*} 
  [Π  i, add_comm_monoid (β i)] [Π i, module R (β i)] 
  {γ : Type*} [add_comm_monoid γ] [module R γ]
  (h : Π i, β i →ₗ[R] γ) : direct_sum ι β →ₗ[R] γ :=
direct_sum.to_module R ι γ h

-- linear_map, with classes :
example {β : ι → Type*} 
  [Π  i, add_comm_monoid (β i)] [Π i, module R (β i)] 
  {γ : Type*} [add_comm_monoid γ] [module R γ]
  {F : Π (i : ι), Type*} [Π i, linear_map_class (F i) R (β i) γ] 
  (h : Π i, F i) : direct_sum ι β →ₗ[R] γ :=
direct_sum.to_module R ι γ (λ i, h i)
-- ⟨h i, map_add _, map_smulₛₗ _⟩

example {β : ι → Type*} 
  [Π  i, add_comm_monoid (β i)] [Π i, module R (β i)] 
  {γ : Type*} [add_comm_monoid γ] [module R γ]
  {F : Π (i : ι), Type*} [Π i, linear_map_class (F i) R (β i) γ] 
  (h : Π i, F i) : direct_sum ι β →ₗ[R] γ :=
direct_sum.to_module R ι γ (λ i, h i)

/- Four versions of a direct sum of maps 
   direct_sum.map' : for add_monoid_hom 
   direct_sum.lmap'  : for linear_map
   the unprimed versions are defined in terms of classes 
   In principle, the latter should suffice. -/

/-- Linear_maps from a direct sum to a direct sum given by families of linear_maps-/

def direct_sum.map {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  {F : Π (i : ι), Type*} [Π i, add_monoid_hom_class (F i) (β i) (γ i)] 
  (h : Π i, F i) : 
  direct_sum ι β →+ direct_sum ι γ :=
direct_sum.to_add_monoid (λ i, add_monoid_hom.comp (direct_sum.of γ i) (h i))

def direct_sum.lmap {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, module R (β i)]
  [Π i, add_comm_monoid (γ i)] [Π i, module R (γ i)] 
  {F : Π (i : ι), Type*} [Π i, linear_map_class (F i) R (β i) (γ i)] 
  (h : Π i, F i) :
  direct_sum ι β →ₗ[R] direct_sum ι γ :=
direct_sum.to_module R ι (direct_sum ι γ)
  (λ i, linear_map.comp (direct_sum.lof R ι γ i) (h i : β i →ₗ[R] γ i))

def direct_sum.map' {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  (h : Π i, β i →+ γ i) : direct_sum ι β →+ direct_sum ι γ :=
direct_sum.to_add_monoid (λ i, add_monoid_hom.comp (direct_sum.of γ i) (h i))

example {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  (h : Π i, β i →+ γ i) : direct_sum.map' h = direct_sum.map h :=  rfl

def direct_sum.lmap' {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, module R (β i)]
  [Π i, add_comm_monoid (γ i)] [Π i, module R (γ i)] 
  (h : Π i, β i →ₗ[R] γ i) : 
  direct_sum ι β →ₗ[R] direct_sum ι γ :=
direct_sum.to_module R ι _ (λ i, linear_map.comp (direct_sum.lof R ι γ i) (h i))

example {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] -- [Π i, module R (β i)]
  [Π i, add_comm_monoid (γ i)] -- [Π i, module R (γ i)] 
  (h : Π i, β i →+ γ i) : direct_sum ι β →+ direct_sum ι γ :=
direct_sum.map' h

example {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] -- [Π i, module ℕ (β i)]
  [Π i, add_comm_monoid (γ i)] -- [Π i, module ℕ (γ i)] 
  (h : Π i, (β i) →+ (γ i)) : direct_sum ι β →+ direct_sum ι γ :=
direct_sum.lmap' (λ i, ((h i).to_nat_linear_map : (β i) →ₗ[ℕ] (γ i)))

lemma direct_sum.map'_eq_lmap'_to_add_monoid_hom {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] -- [Π i, module R (β i)]
  [Π i, add_comm_monoid (γ i)] -- [Π i, module R (γ i)] 
  (h : Π i, β i →+ γ i) : direct_sum.map' h 
= (direct_sum.lmap' (λ i, (h i).to_nat_linear_map)).to_add_monoid_hom := rfl

lemma direct_sum.lmap'_to_add_monoid_hom_eq_map' {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, module R (β i)]
  [Π i, add_comm_monoid (γ i)] [Π i, module R (γ i)] 
  (h : Π i, β i →ₗ[R] γ i) : 
(direct_sum.lmap' h).to_add_monoid_hom = direct_sum.map' (λ i, (h i).to_add_monoid_hom) := rfl

example {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, module R (β i)]
  [Π i, add_comm_monoid (γ i)] [Π i, module R (γ i)] 
  (h : Π i, β i →ₗ[R] γ i) : 
(direct_sum.lmap' h) = direct_sum.lmap (h) := 
begin
  refl,
end

/- Lemmas to help computation -/

lemma direct_sum.map_of {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  {F : Π i, Type*} [Π i, add_monoid_hom_class (F i) (β i) (γ i)] 
  (h : Π i, F i) (i : ι) (x : β i) : 
  direct_sum.map h (direct_sum.of β i x) = direct_sum.of γ i (h i x) := 
by simp only [direct_sum.map, direct_sum.to_add_monoid_of, add_monoid_hom.coe_comp, add_monoid_hom.coe_coe]

/- unknown constant…
lemma direct_sum.map_apply {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  {F : Π i, Type*} [Π i, add_monoid_hom_class (F i) (β i) (γ i)] 
  (h : Π i, F i) (x : direct_sum ι β) (i : ι) : 
  direct_sum.map h x i = h i (x i) :=
begin
  let f : direct_sum ι β →+ γ i := 
  { to_fun := λ x, direct_sum.map' h x i,
    map_zero' := by simp, 
    map_add' := by simp, },
  let g : direct_sum ι β →+ γ i := 
  { to_fun := λ y, h i (y i), 
    map_zero' := by simp,
    map_add' := by simp, } ,
  change f x = g x,
  suffices : f = g, 
  rw this, 
  apply direct_sum.add_hom_ext , 
  intros j y,
  simp [f, g, direct_sum.map'_of], 
  by_cases hj : j = i,
  { rw ← hj, simp only [direct_sum.of_eq_same], },
  { simp only [direct_sum.of_eq_of_ne _ j i _ hj, map_zero], },
end
-/


lemma direct_sum.map'_of {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  (h : Π i, β i →+ γ i) (i : ι) (x : β i) : 
  direct_sum.map' h (direct_sum.of β i x) = direct_sum.of γ i (h i x) := 
begin
  dsimp only [direct_sum.map'],
  rw direct_sum.to_add_monoid_of , 
  simp only [add_monoid_hom.coe_comp],
end


lemma direct_sum.lmap'_lof {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  [Π i, module R (β i)] [Π i, module R (γ i)]
  (h : Π i, β i →ₗ[R] γ i) (i : ι) (x : β i) : 
  direct_sum.lmap' h (direct_sum.lof R ι β i x) = direct_sum.lof R ι γ i (h i x) := 
begin
  dsimp only [direct_sum.lmap'],
  rw direct_sum.to_module_lof, 
  simp only [linear_map.coe_comp],
end


lemma direct_sum.lmap'_apply {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)] 
  [Π i, module R (β i)] [Π i, module R (γ i)]
  (h : Π i, β i →ₗ[R] γ i) (x : direct_sum ι β) (i : ι) : 
  direct_sum.lmap' h x i = h i (x i) := 
begin
  simp only [direct_sum.apply_eq_component R],
  rw ← linear_map.comp_apply,
  rw ← linear_map.comp_apply, 
  revert x, rw ← linear_map.ext_iff,
  apply direct_sum.linear_map_ext , 
  intro j, ext y,
  simp only [linear_map.comp_apply],
  rw [direct_sum.lmap'_lof ],
  simp only [direct_sum.lof_eq_of],
  simp only [←direct_sum.apply_eq_component],  
  by_cases hji : j = i, 
  { rw ← hji, simp only [direct_sum.of_eq_same], },
  { simp only [direct_sum.of_eq_of_ne _ j i _ hji, map_zero], },
end

lemma direct_sum.to_module_comp_lmap'_eq 
  {β γ: ι → Type*} {δ : Type*}
  [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)] [add_comm_monoid δ]
  [Π i, module R (β i)] [Π i, module R (γ i)] [module R δ]
  (h : Π i, β i →ₗ[R] γ i) 
  (f : Π i, γ i →ₗ[R] δ)
  (x : direct_sum ι β) : 
  direct_sum.to_module R ι δ f (direct_sum.lmap' h x) = 
  direct_sum.to_module R ι δ (λ i, (f i).comp (h i)) x := 
begin
  rw ← linear_map.comp_apply,
  revert x,
  rw ← linear_map.ext_iff, 
  apply direct_sum.linear_map_ext , 
  intro i, 
  apply linear_map.ext, 
  intro b, 
  simp, 
  rw direct_sum.lmap'_lof, 
  rw direct_sum.to_module_lof,
end


lemma direct_sum.map'_apply {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)] 
  [Π (i : ι) (x : β i), decidable (x ≠ 0)] 
  [Π (i : ι) (x : γ i), decidable (x ≠ 0)] 
  (h : Π i, β i →+ γ i) (x : direct_sum ι β) (i : ι) : 
  direct_sum.map' h x i = h i (x i) :=
begin
  let f : direct_sum ι β →+ γ i := 
  { to_fun := λ x, direct_sum.map' h x i,
    map_zero' := by simp only [map_zero, direct_sum.zero_apply], 
    map_add' := by simp only [map_add, direct_sum.add_apply, eq_self_iff_true, forall_const], },
  let g : direct_sum ι β →+ γ i := 
  { to_fun := λ y, h i (y i), 
    map_zero' := by simp only [direct_sum.zero_apply, map_zero],
    map_add' := by simp only [direct_sum.add_apply, map_add, eq_self_iff_true, forall_const], } ,
  change f x = g x,
  suffices : f = g, 
  rw this, 
  apply direct_sum.add_hom_ext , 
  intros j y,
  simp [f, g, direct_sum.map'_of], 
  by_cases hj : j = i,
  { rw ← hj, simp only [direct_sum.of_eq_same], },
  { simp only [direct_sum.of_eq_of_ne _ j i _ hj, map_zero], },
end


/- Lemmas using direct_sum.mk   : could probably be removed -/
lemma direct_sum.mk_apply {β : ι → Type*} [Π i, add_comm_monoid (β i)] (s : finset ι)
  (f : Π (i : s), β ↑i) (i : ι) : direct_sum.mk β s f i = dite (i ∈ s) (λ h, f ⟨i, h⟩) (λ h, 0) :=
rfl

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

lemma direct_sum.map'_apply'_old {β γ : ι → Type*} [Π i, add_comm_monoid (β i)]
  [Π i, add_comm_monoid (γ i)] [Π (i : ι) (x : β i), decidable (x ≠ 0)] 
  [Π (i : ι) (x : γ i), decidable (x ≠ 0)] (h : Π i, β i →+ γ i) (x : direct_sum ι β) : 
  direct_sum.map' h x = direct_sum.mk γ (x.support) (λ i, h i (x i)) := 
begin
  conv_lhs {rw ← direct_sum.sum_support_of β x, },
  rw map_sum,
  simp_rw direct_sum.map'_of, 
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

def zoto 
{β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  [Π (i : ι) (x : β i), decidable (x ≠ 0)] 
  [Π (i : ι) (x : γ i), decidable (x ≠ 0)]
  {F : Π i, Type*} [Π i, add_monoid_hom_class (F i) (β i) (γ i)] 
  (h : Π i, F i) 
  (B : direct_sum ι β) : Π i : (B.support : set ι), (γ i) := λ i, (h i) (B i)

lemma direct_sum.map_apply' {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  [Π (i : ι) (x : β i), decidable (x ≠ 0)] 
  [Π (i : ι) (x : γ i), decidable (x ≠ 0)]
  {F : Π i, Type*} [Π i, add_monoid_hom_class (F i) (β i) (γ i)] 
  (h : Π i, F i) (x : direct_sum ι β) :
   direct_sum.map h x = direct_sum.mk γ (x.support) 
   (zoto h x) :=
   -- (λ i, (h i) (x i))  gives `unknown fresh 0._ ` error
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

end direct_sum

section graded_quot

variables (R : Type*) [comm_ring R]
variables {ι : Type*} [decidable_eq ι] [add_monoid ι]
variables {A : Type*} [comm_ring A] [decidable_eq A] [algebra R A]

/- -- graded_algebra does not work with `submodule_class`

variables {σ : Type*} [set_like σ A] [add_submonoid_class σ A] 
[submodule_class σ R A] 

variable (𝒜 : ι → σ) [h𝒜 : graded_algebra 𝒜]
-/

section
variables {σ : Type*} [set_like σ A] [add_submonoid_class σ A] [smul_mem_class σ R A] 

#check graded_algebra

variables (ℬ : ι → σ) 

@[reducible]
def graded_algebra' := @graded_ring _ A _ _ _ _ _ _ ℬ

variable [hℬ : graded_algebra' ℬ]

end


variables (𝒜 : ι → submodule R A)

section ideal 

variable (I : ideal A) 

-- variables [h𝒜 : graded_algebra 𝒜] (hI: ideal.is_homogeneous 𝒜 I)

-- It seems I start understanding what I'm doing
example : semilinear_map_class (A →+* A ⧸ I) (ring_hom.id ℤ) _ _ :=
{ coe            := λ f a, f a,
  coe_injective' := λ f g hfg, ring_hom.ext (λ x, function.funext_iff.mp hfg x),
  map_add        := map_add, 
  map_smulₛₗ     := λ f r a, by simp only [zsmul_eq_mul, map_mul, map_int_cast, eq_int_cast, int.cast_id], }

-- This will probably be useless in the end, because I "R-modulify" everything

-- ideal.quotient.mk vs ideal.quotient.mkₐ  
example (I : ideal A) (r : R) (a : A) : 
  r • (ideal.quotient.mk I a) = ideal.quotient.mk I (r • a) := 
  map_smul (ideal.quotient.mkₐ R I) r a

/-- The graded pieces of A ⧸ I -/
def quot_submodule : ι → submodule R (A ⧸ I) := λ i, submodule.map (ideal.quotient.mkₐ R I) (𝒜 i)

/- broken by the passage to modules…
-- I think this one can be erased, since we have the laux version
/-- The decomposition at the higher level -/
def quot_decompose_aux [graded_ring 𝒜] :
  A → direct_sum ι (λ (i : ι), ↥(quot_submodule R 𝒜 I i)) := λ a,
begin
  refine (direct_sum.map _) (direct_sum.decompose_linear_equiv 𝒜 a),
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
-/

def quot_comp_map (i : ι) : ↥(𝒜 i) →ₗ[R] ↥(quot_submodule R 𝒜 I i) := 
{ to_fun    := λ u, ⟨ideal.quotient.mkₐ R I ↑u,
                 by rw [quot_submodule,submodule.mem_map]; exact ⟨↑u, u.prop, rfl⟩⟩,
  map_add'  := λ u v, by simp only [←subtype.coe_inj, submodule.coe_add, map_add,
                 add_mem_class.mk_add_mk],
  map_smul' := λ r u, by simp only [submodule.coe_smul_of_tower, ring_hom.id_apply, set_like.mk_smul_mk, subtype.mk_eq_mk, map_smul], }

-- lemma quot_comp_map_surjective (i : ι) : function.surjective (quot_comp_map R 𝒜 I i) := sorry

example : submodule R A := I.restrict_scalars R

/-- The decomposition at the higher level -/
def quot_decompose_laux [graded_algebra 𝒜]:
  A →ₗ[R] direct_sum ι (λ (i : ι), ↥(quot_submodule R 𝒜 I i)) :=
linear_map.comp (direct_sum.lmap' (quot_comp_map R 𝒜 I)) 
  (direct_sum.decompose_alg_equiv 𝒜).to_linear_map


lemma quot_decompose_laux_of_mem_eq_zero [graded_algebra 𝒜] (hI : I.is_homogeneous 𝒜) (x : A) (hx : x ∈ I) (i : ι) :
((quot_decompose_laux R 𝒜 I) x) i = 0 :=
begin
  rw [quot_decompose_laux,linear_map.comp_apply,direct_sum.lmap'_apply, quot_comp_map],
  simp only [ideal.quotient.mkₐ_eq_mk, alg_equiv.to_linear_map_apply,
    direct_sum.decompose_alg_equiv_apply, linear_map.coe_mk, 
    submodule.mk_eq_zero],
  rw ideal.quotient.eq_zero_iff_mem,
  exact hI i hx, 
end

lemma quot_decompose_laux_ker [graded_algebra 𝒜] (hI : I.is_homogeneous 𝒜) : 
  I.restrict_scalars R ≤ (quot_decompose_laux R 𝒜 I).ker := 
begin
  intros x hx,
  simp only [submodule.restrict_scalars_mem] at hx, 

  rw [linear_map.mem_ker], 
  ext i,
  rw [direct_sum.zero_apply, submodule.coe_zero, submodule.coe_eq_zero],
  apply quot_decompose_laux_of_mem_eq_zero,
  exact hI, exact hx,
end

/-- The decomposition at the higher level -/
def quot_decompose [graded_algebra 𝒜] (hI : I.is_homogeneous 𝒜) : 
A ⧸ I →ₗ[R] direct_sum ι (λ (i : ι), ↥(quot_submodule R 𝒜 I i)) :=
begin
  apply @submodule.liftq R A _ _ _ (I.restrict_scalars R) R
    (direct_sum ι (λ i, quot_submodule R 𝒜 I i) ) _ _ _ (ring_hom.id R) (quot_decompose_laux R 𝒜 I), 
 -- without explicit arguments, it is too slow
 -- apply submodule.liftq (I.restrict_scalars R) (quot_decompose_laux R 𝒜 I),
  apply quot_decompose_laux_ker R 𝒜 I hI, 
end 

lemma quot_decompose_laux_apply_mk [graded_algebra 𝒜] (hI : I.is_homogeneous 𝒜) (a : A): 
quot_decompose R 𝒜 I hI (ideal.quotient.mk I a) = quot_decompose_laux R 𝒜 I a := 
begin
  rw [quot_decompose],
  have : ideal.quotient.mk I a = submodule.quotient.mk a := rfl,
  rw this, 
  -- with explicit arguments, it times out
  -- exact submodule.liftq_apply (I.restrict_scalars R) (quot_decompose_laux R 𝒜 I) a, 
  -- apply works 
  apply submodule.liftq_apply, 
end

def quot_decomposition_left_inv [graded_algebra 𝒜] (hI : I.is_homogeneous 𝒜) : function.left_inverse 
(direct_sum.coe_add_monoid_hom (quot_submodule R 𝒜 I)) (quot_decompose R 𝒜 I hI) := λ a, 
begin
  obtain ⟨a, rfl⟩ := (ideal.quotient.mk I).is_surjective a, 

  rw quot_decompose_laux_apply_mk,
  rw quot_decompose_laux, 
  simp only [linear_map.comp_apply],

  let h𝒜 : direct_sum.decomposition 𝒜  := by apply_instance,
  let ha := h𝒜.left_inv a,
  have : (direct_sum.decompose_alg_equiv 𝒜).to_linear_map a
    = direct_sum.decomposition.decompose' a, 
    refl, 
  rw this, 
  conv_rhs {rw ← h𝒜.left_inv a},


  change _ = submodule.mkq (I.restrict_scalars R)  (_),
  simp only [←linear_map.to_add_monoid_hom_coe], 

  rw direct_sum.lmap'_to_add_monoid_hom_eq_map',
  simp only [← add_monoid_hom.comp_apply],
  generalize : direct_sum.decomposition.decompose' a = b,
  revert b,
  rw ← add_monoid_hom.ext_iff, 
  apply direct_sum.add_hom_ext,
  intros i y,
  simp only [add_monoid_hom.coe_comp, function.comp_app, linear_map.to_add_monoid_hom_coe, direct_sum.coe_add_monoid_hom_of,
  submodule.mkq_apply],
  rw direct_sum.map'_of,
  rw direct_sum.coe_add_monoid_hom_of,
  simp only [linear_map.to_add_monoid_hom_coe],
  rw [quot_comp_map],
  simp only [ideal.quotient.mkₐ_eq_mk, linear_map.coe_mk, submodule.coe_mk],
  refl,
end

def quot_decomposition_right_inv [graded_algebra 𝒜] (hI : I.is_homogeneous 𝒜) : function.right_inverse 
(direct_sum.coe_add_monoid_hom (quot_submodule R 𝒜 I)) (quot_decompose R 𝒜 I hI) := λ x, 
begin
  simp only [←linear_map.to_add_monoid_hom_coe], 
  rw ← add_monoid_hom.comp_apply,
  conv_rhs {rw ← add_monoid_hom.id_apply _ x},
  revert x,
  rw ← add_monoid_hom.ext_iff,
  apply direct_sum.add_hom_ext,
  intros i y,
  obtain ⟨x, hx, hxy⟩ := y.prop,

  simp only [add_monoid_hom.coe_comp, linear_map.to_add_monoid_hom_coe, function.comp_app, direct_sum.coe_add_monoid_hom_of,
  add_monoid_hom.id_apply],
  rw ←hxy,
  rw ideal.quotient.mkₐ_eq_mk,
  rw quot_decompose_laux_apply_mk,

  rw quot_decompose_laux,
  simp only [linear_map.coe_comp, function.comp_app, alg_equiv.to_linear_map_apply, direct_sum.decompose_alg_equiv_apply],

  change direct_sum.lmap' _ (direct_sum.decompose 𝒜 x) = _,
  suffices : direct_sum.decompose 𝒜 x = direct_sum.lof R ι (λ i, 𝒜 i) i (⟨x, hx⟩ : 𝒜 i), 
  rw this, 
  rw direct_sum.lmap'_lof,
  rw direct_sum.lof_eq_of, 
  apply congr_arg2 _ rfl,
  rw quot_comp_map,
  simp only [ideal.quotient.mkₐ_eq_mk, submodule.coe_mk, linear_map.coe_mk],
  rw [←subtype.coe_inj, subtype.coe_mk],
  rw ←hxy, 
  simp only [ideal.quotient.mkₐ_eq_mk], 

  conv_lhs {rw ← subtype.coe_mk x hx },
  rw direct_sum.decompose_coe,
  rw direct_sum.lof_eq_of, 
end 


def quot_decomposition [graded_algebra 𝒜] (hI : I.is_homogeneous 𝒜) :
  direct_sum.decomposition (quot_submodule R 𝒜 I) :=
{ decompose' := quot_decompose R 𝒜 I hI,
  left_inv   := quot_decomposition_left_inv R 𝒜 I hI,
  right_inv  := quot_decomposition_right_inv R 𝒜 I hI }
  

lemma mem_quot_submodule_iff (i : ι) (g : A ⧸ I):
  g ∈ quot_submodule R 𝒜 I i ↔ ∃ (a : A), a ∈ 𝒜 i ∧ideal.quotient.mk I a = g   := 
by rw [quot_submodule, submodule.mem_map, ideal.quotient.mkₐ_eq_mk]

/-- The quotient of a graded algebra by a homogeneous ideal, as a graded algebra -/
def graded_quot_alg [graded_algebra 𝒜] 
  (hI : I.is_homogeneous 𝒜) :
  graded_algebra (quot_submodule R 𝒜 I) :=
{ to_decomposition  := quot_decomposition R 𝒜 I hI,
  to_graded_monoid  :=
  { one_mem := by rw [quot_submodule, submodule.mem_map]; exact ⟨1, set_like.one_mem_graded 𝒜, rfl⟩,
    mul_mem := λ i j gi gj hgi hgj, 
    begin
    rw mem_quot_submodule_iff at hgi hgj ⊢,
    obtain ⟨ai, hai, rfl⟩ := hgi,
    obtain ⟨aj, haj, rfl⟩ := hgj,
    exact ⟨ai * aj, set_like.mul_mem_graded hai haj,
    map_mul _ _ _⟩,
    end
    }}

end ideal

section rel

/- THIS SECTION IS A MESS
ITS GOAL IS TO TRANSFER THE GRADED ALGEBRA STRUCTURE TO
THE CASE WHERE THE QUOTIENT IS DEFINED VIA A RELATION 
-/
variable (r : A → A → Prop)

variable {R}

/-- A relation is homogeneous iff r a b implies that a and b 
are homogeneous of the same degree -/
def rel_is_homogeneous := 
  ∀ (a b : A) (hab : r a b), ∃ i, a ∈ 𝒜 i ∧ b ∈ 𝒜 i 

/-- Adding the alg_hom component to the natural ring_equiv -/
def ring_quot_equiv_alg_ideal_quotient : ring_quot r ≃ₐ[R] A ⧸ ideal.of_rel r := { commutes' := λ s, 
begin
  rw [ring_equiv.to_fun_eq_coe,
    ← alg_hom.commutes (ring_quot.mk_alg_hom R r), 
    ← alg_hom.commutes (ideal.quotient.mkₐ R (ideal.of_rel r)),
    ideal.quotient.mkₐ_eq_mk,
    ← ring_quot.ring_quot_to_ideal_quotient_apply r _,
    ←ring_quot.mk_alg_hom_coe R r],
  refl,
end,
  .. ring_quot.ring_quot_equiv_ideal_quotient  r
}

/- example [decidable_eq (submodule R A)] (i : ι) : 
quot_submodule R 𝒜 (ideal.of_rel r) i = submodule.map ((ideal.quotient.mkₐ  R _).comp 
  (ring_quot.mk_alg_hom R r)) i :=
begin

end -/

def graded_quot_alg_rel [graded_algebra 𝒜] [decidable_eq (submodule R A)]
  (hr : rel_is_homogeneous 𝒜 r) : graded_algebra 
  (λ i, submodule.map (ring_quot.mk_alg_hom R r) i) :=
  sorry

end rel



#exit
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