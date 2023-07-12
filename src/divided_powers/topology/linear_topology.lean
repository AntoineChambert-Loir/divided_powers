import topology.algebra.ring.basic
import ring_theory.ideal.basic
import topology.algebra.nonarchimedean.bases


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


/-  -- TODO : faire marcher ça !
section linear_topology


variables (α : Type *) [comm_ring α]

structure has_linear_topology  [τ : topological_space α] : Prop :=
(to_linear_topology : ∃ (ι : Type*) [nonempty ι] 
  (J : ι → ideal α) (hJ : ideals_basis J),  
  by exactI τ = hJ.to_ring_subgroups_basis.topology)

lemma has_linear_topology.to_topological_ring [τ : topological_space α] 
  (h : has_linear_topology α) : 
  topological_ring α := 
begin
  sorry
end

end linear_topology
 -/