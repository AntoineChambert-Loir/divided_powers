import topology.algebra.ring.basic
import ring_theory.ideal.basic
import topology.algebra.nonarchimedean.bases
import mv_power_series.topology


section complements

lemma topological_space_eq_iff_nhds_eq {α : Type*} (τ τ': topological_space α) : 
  τ = τ' ↔
  (∀ (a : α) (s : set α) (has : a ∈ s), s ∈ @nhds α τ a ↔ s ∈ @nhds α τ' a) :=
begin
  split, 
  { intros h a s has, rw h, },
  intro h, ext s, 
  simp only [is_open_iff_mem_nhds],
  apply forall_congr, intro a, 
  apply imp_congr_right, exact h a s,
end

lemma topological_space_le_iff_nhds_le {α : Type*} (τ τ': topological_space α) : 
  τ ≤ τ' ↔
  (∀ (a : α) (s : set α) (has : a ∈ s), s ∈ @nhds α τ' a → s ∈ @nhds α τ a) :=
begin
  rw topological_space.le_def, 
  split, 
  { intros h a s has,
    simp only [mem_nhds_iff],
    apply exists_imp_exists, intro t, 
    apply exists_imp_exists, intro ht,
    rintro ⟨ht_open, h'⟩, exact ⟨h t ht_open, h'⟩, },
  intro h, 
  intros s,
  simp only [is_open_iff_mem_nhds],
  intros hs a has,
  exact h a s has (hs a has),
end

lemma mem_nhds_add_iff {α : Type*}
  [add_group α] [topological_space α] [topological_add_group α] 
  (V : set α) (a b : α) : V ∈ nhds (a + b) ↔ (has_add.add a) ⁻¹' V ∈ nhds (b) :=
begin
  split,
  exact λ hV, (continuous_add_left a).continuous_at hV,
  { intro hV,
    suffices : V = has_add.add (-a) ⁻¹' ((has_add.add a) ⁻¹' V),
    rw this,
    apply (continuous_add_left (-a)).continuous_at,
    simp only [neg_add_cancel_left],
    exact hV,
    rw set.preimage_preimage,
    simp only [add_neg_cancel_left, set.preimage_id'],},
end

end complements


/-- A family of ideals of a ring `α` is an `ideals_basis` if the ideals 
  are both left- and right-ideals, 
  and if every intersection of two of them contains another one. -/
structure ideals_basis {α : Type*} [ring α] {ι : Type*}
  (B : ι → ideal α) : Prop  :=
(inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j)
(mul_right : ∀ i a r, a ∈ B i → a * r ∈ B i)

namespace ideals_basis 

variables {α : Type*} [ring α] 

/-- An `ideals_basis` on a `comm_ring` -/
def of_comm {α : Type*} [comm_ring α] {ι : Type*} {B : ι → ideal α} 
(inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j) :  ideals_basis B :=
{ inter := inter,
  mul_right := λ i a r h, 
  by { rw mul_comm, refine ideal.mul_mem_left (B i) r h, } }

/- def to_submodules_ring_basis {α  : Type*} [comm_ring α] {ι : Type*} {B : ι → ideal α} (hB : ideals_basis B) :
  submodules_ring_basis B := sorry 
 -/

def to_ring_subgroups_basis {ι : Type*} {B : ι → ideal α} (hB : ideals_basis B) : 
  ring_subgroups_basis (λ i, (B i).to_add_subgroup) := { 
  inter := hB.inter, 
  mul := λ i, ⟨i, λ u, by { 
    rintro ⟨x, y, hx, hy, rfl⟩, 
    apply ideal.mul_mem_left, exact hy, }⟩,
  left_mul := λ a i, ⟨i, by { 
    intros x hx, rw set.mem_preimage, 
    simp only [submodule.coe_to_add_subgroup, set_like.mem_coe] at hx ⊢,
    apply ideal.mul_mem_left, exact hx, },⟩,
  right_mul := λ a i, ⟨i, by { 
    intros y hy, rw set.mem_preimage, 
    apply hB.mul_right, exact hy, }⟩ }

def to_ring_filter_basis {ι : Type*} [nonempty ι] {B : ι → ideal α} (hB : ideals_basis B) : 
  ring_filter_basis α := hB.to_ring_subgroups_basis.to_ring_filter_basis 

def topology {ι : Type*} {B : ι → ideal α} [nonempty ι] (hB : ideals_basis B) :
  topological_space α := (to_ring_filter_basis hB).topology

lemma to_topological_ring {ι : Type*} {B : ι → ideal α} [nonempty ι] (hB : ideals_basis B) :
  @topological_ring α hB.topology _ :=  hB.to_ring_filter_basis.is_topological_ring


/-  Junk

structure linear_topological_ring (α : Type*)[comm_ring α] [topological_space α] : Prop :=
(to_has_ideal_basis : has_submodules_basis α α)


def has_ring_subgroups_basis 
  (α : Type*) [comm_ring α] [H : topological_space α] : Prop :=
∃ (ι : Type*) [nonempty ι] (B : ι → add_subgroup α) (hB : ring_subgroups_basis B), 
by exactI H = ring_subgroups_basis.topology hB
 

def has_submodules_basis 
  (α : Type*) [comm_ring α] [topological_space α] 
  (M : Type*) [add_comm_group M] [module α M] [H : topological_space M] : Prop :=
∃ (ι : Type*) [nonempty ι] (B : ι → submodule α M) (hB : submodules_basis B), 
by exactI H = submodules_basis.topology hB

structure linear_topological_module 
  (α : Type*) [comm_ring α] [topological_space α] 
  (M : Type*) [add_comm_group M] [module α M] [H : topological_space M] : Prop := 
(to_has_submodules_basis : has_submodules_basis α M) -/

end ideals_basis 

section mv_power_series

variable (σ : Type*) 

namespace mv_power_series

section ideals 

variables (α : Type*) [comm_ring α] 
-- [_root_.topological_ring α]
-- [_root_.uniform_ring α] 
-- [_root_.topological_add_group α]
-- [_root_.uniform_add_group α]

def J : (σ →₀ ℕ) → ideal (mv_power_series σ α) := λ d, 
{ carrier := {f | ∀ e ≤ d, coeff α e f = 0},
  zero_mem' := by {rw set.mem_set_of, intros e he, rw coeff_zero, },
  add_mem' := λ f g hf hg, by { 
    rw set.mem_set_of at hf hg ⊢, 
    intros e he, rw [map_add, hf e he, hg e he, add_zero], },
  smul_mem' := λ f g hg, by {
    rw set.mem_set_of at hg ⊢, 
    intros e he, rw [smul_eq_mul, coeff_mul], 
    apply finset.sum_eq_zero,
    rintros uv huv, 
    convert mul_zero _,
    apply hg, 
    apply le_trans _ he,
    rw [finsupp.mem_antidiagonal] at huv, 
    rw le_iff_exists_add', exact ⟨uv.fst, huv.symm⟩, } }

lemma mem_J (f : mv_power_series σ α) (d : σ →₀ ℕ) : 
  f ∈ J σ α d ↔ ∀ e ≤ d, coeff α e f = 0 := by 
simp only [J, submodule.mem_mk, set.mem_set_of_eq]
  
lemma J_le {e d : σ →₀ ℕ} (hed : e ≤ d) : J σ α d ≤ J σ α e :=
begin
  intro f, 
  simp only [mem_J],
  refine forall_imp _,
  intros a h ha, exact h (le_trans ha hed),
end

lemma J_le_iff [nontrivial α] (d e : σ →₀ ℕ) : J σ α d ≤ J σ α e ↔ e ≤ d := 
begin
  split,
  { simp only [J, submodule.mk_le_mk, set.set_of_subset_set_of], 
    intro h,
    rw ← inf_eq_right,
    apply le_antisymm, exact inf_le_right,
    by_contradiction h',
    specialize h (monomial α e 1) _,
    intros e' he', rw coeff_monomial_ne, intro hee', 
    apply h',
    rw le_inf_iff, apply and.intro _ le_rfl,
    simpa [hee'] using he',
    apply one_ne_zero' α,
    convert h e le_rfl, rw coeff_monomial_same, },
  apply J_le,
end

lemma J_antitone : antitone (J σ α) := λ d e h, J_le σ α h

lemma ideals_basis : ideals_basis (J σ α) := 
  ideals_basis.of_comm (λ d e, by { use d ⊔ e, apply antitone.map_sup_le (J_antitone σ α), })

lemma to_ring_subgroups_basis : ring_subgroups_basis (λ d, (J σ α d).to_add_subgroup) := 
  (ideals_basis σ α).to_ring_subgroups_basis 

end ideals

section discrete_topology

variables (α : Type*) [comm_ring α] [topological_space α] 

lemma J_mem_nhds_zero [discrete_topology α] (d : σ →₀ ℕ) : ↑(J σ α d) ∈ nhds (0 : mv_power_series σ α) := 
begin
  classical,
  rw nhds_pi, rw filter.mem_pi,
  use finset.Iic d, 
  split,
  apply finset.finite_to_set,
  let t : (σ →₀ ℕ) → set α := (λ e, ite (e ≤ d) {0} set.univ), 
  use t,
  split, 
  { intros e, simp only [t], 
    split_ifs with h,
    simp only [pi.zero_apply, nhds_discrete, filter.pure_zero, filter.mem_zero,
      set.mem_singleton], 
    simp only [filter.univ_mem], }, 
  { intros f,
    simp only [mem_J, finset.coe_Iio, set.mem_pi, set.mem_Iio, set.mem_ite_univ_right, set.mem_singleton_iff, set_like.mem_coe],
    refine forall_imp _,
    simp only [finset.coe_Iic, set.mem_Iic], intros e h,
    intro he, exact h he he, },
end

lemma has_ideals_basis_topolgy [discrete_topology α] : 
  mv_power_series.topological_space σ α = (to_ring_subgroups_basis σ α).topology := 
begin
  let τ := mv_power_series.topological_space σ α,
  let τ' := (to_ring_subgroups_basis σ α).topology, 
  change τ = τ', 
  rw topological_space_eq_iff_nhds_eq, 
  suffices : ∀ s, s ∈ @nhds _ τ 0 ↔ s ∈ @nhds _ τ' 0,
  -- mv nhds from 0 to a
  { intros a s ha, 
    rw ← add_zero a, 
    haveI := (topological_ring σ α), rw mem_nhds_add_iff,
    rw mem_nhds_add_iff, 
    apply this, },
  -- neighborhoods of 0
  intro s,
  rw (ring_subgroups_basis.has_basis_nhds (to_ring_subgroups_basis σ α) 0).mem_iff,
  simp only [sub_zero, submodule.mem_to_add_subgroup, exists_true_left],
  split,
  { rw nhds_pi, rw filter.mem_pi,
    rintro ⟨D, hD, t, ht, ht'⟩,
    use finset.sup hD.to_finset id,
    apply subset_trans _ ht', 
    intros f hf, 
    rw set.mem_pi, intros e he, 
    change f ∈ J σ α _ at hf, 
    rw ← coeff_eq_apply f e, rw hf e, 
    exact mem_of_mem_nhds (ht e), 
    convert finset.le_sup _,
    simp only [id.def], 
    simp only [set.finite.mem_to_finset], exact he, },
  { rintro ⟨d, hd⟩,
    exact (nhds 0).sets_of_superset (J_mem_nhds_zero σ α d) hd,}  
end

/- 

lemma to_submodules_basis [discrete_topology α] : submodules_basis (J σ α) := submodules_basis.mk 
  (λ d e, by {
    use d + e, rw le_inf_iff, 
    split,
    apply J_antitone, rw le_iff_exists_add, exact ⟨e, rfl⟩, 
    apply J_antitone, rw le_iff_exists_add', exact ⟨d, rfl⟩, })
  (λ f d, by { rw filter.eventually_iff_exists_mem, 
    use ↑(J σ α d), apply and.intro (J_mem_nhds_zero σ α d),
    intros g hg, 
    rw [smul_eq_mul, mul_comm], 
    refine ideal.mul_mem_left _ f _, 
    simpa only [set_like.mem_coe] using hg, } )

lemma has_submodules_basis_topology [discrete_topology α] : mv_power_series.topological_space σ α = (to_submodules_basis σ α).topology := 
begin
  let τ := mv_power_series.topological_space σ α,
  let τ' := (to_submodules_basis σ α).topology, 
  suffices : τ = τ', exact this,
  rw topological_space_eq_iff_nhds_eq, 
  suffices : ∀ s, s ∈ @nhds _ τ 0 ↔ s ∈ @nhds _ τ' 0,
  -- mv nhds from 0 to a
  { intros a s ha, 
    rw ← add_zero a, 
    haveI := (topological_ring σ α), rw mem_nhds_add_iff,
    rw mem_nhds_add_iff, 
    apply this, },
  -- neighborhoods of 0
  intro s,
  rw (ring_subgroups_basis.has_basis_nhds (to_ring_subgroups_basis σ α) 0).mem_iff,
  simp only [sub_zero, submodule.mem_to_add_subgroup, exists_true_left],
  split,
  { rw nhds_pi, rw filter.mem_pi,
    rintro ⟨D, hD, t, ht, ht'⟩,
    use finset.sup hD.to_finset id,
    apply subset_trans _ ht', 
    intros f hf, 
    rw set.mem_pi, intros e he, 
    change f ∈ J σ α _ at hf, 
    rw ← coeff_eq_apply f e, rw hf e, 
    exact mem_of_mem_nhds (ht e), 
    convert finset.le_sup _,
    simp only [id.def], 
    simp only [set.finite.mem_to_finset], exact he, },
  { rintro ⟨d, hd⟩,
    exact (nhds 0).sets_of_superset (J_mem_nhds_zero σ α d) hd,}  
end
 -/

end discrete_topology

end mv_power_series

end mv_power_series

/- 
example {α : Type*} [comm_ring α] [topological_space α] [topological_ring α] 
  (V : set α) (a b : α) (hV : V ∈ nhds (a + b)) : (has_add.add a) ⁻¹' V ∈ nhds b :=
begin
    rw [(homeomorph.add_left a).nhds_eq_comap],
    exact filter.preimage_mem_comap hV,
end
 -/