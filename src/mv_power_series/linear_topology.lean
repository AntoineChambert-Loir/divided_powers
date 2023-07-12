import topology.algebra.ring.basic
import ring_theory.ideal.basic
import topology.algebra.nonarchimedean.bases
import mv_power_series.topology

def has_submodules_basis 
  (α : Type*) [comm_ring α] [topological_space α] 
  (M : Type*) [add_comm_group M] [module α M] [H : topological_space M] : Prop :=
∃ (ι : Type*) [nonempty ι] (B : ι → submodule α M) (hB : submodules_basis B), 
by exactI H = submodules_basis.topology hB

structure linear_topological_module 
  (α : Type*) [comm_ring α] [topological_space α] 
  (M : Type*) [add_comm_group M] [module α M] [H : topological_space M] : Prop := 
(to_has_submodules_basis : has_submodules_basis α M)

def has_ideals_basis 
  (α : Type*) [comm_ring α] [H : topological_space α] : Prop :=
∃ (ι : Type*) [nonempty ι] (B : ι → ideal α) (hB : submodules_basis B), 
by exactI H = submodules_basis.topology hB

structure linear_topological_ring (α : Type*)[comm_ring α] [topological_space α] : Prop :=
(to_has_ideal_basis : has_submodules_basis α α)

section mv_power_series

variable (σ : Type*) 
lemma finsupp.le_iff_exists_add (d e : σ →₀ ℕ) : d ≤ e ↔  ∃ d', d + d' = e :=
begin
  split,
  { intro h, use e - d,
    ext i, simp only [finsupp.coe_add, finsupp.coe_tsub, pi.add_apply, pi.sub_apply], 
    rw finsupp.le_def at h, 
    rw nat.add_sub_of_le (h i),},
  { rintro ⟨d', rfl⟩, rw finsupp.le_def, intro i,
    simp only [finsupp.coe_add, pi.add_apply, le_add_iff_nonneg_right, zero_le'],}
end

namespace mv_power_series

section ideals 

variables (α : Type*) [comm_ring α] [topological_space α] 
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
    rw [finsupp.mem_antidiagonal, add_comm] at huv, 
    rw finsupp.le_iff_exists_add, exact ⟨uv.fst, huv⟩, } }

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

lemma J_mem_nhds_zero [discrete_topology α] (d : σ →₀ ℕ) : 
  ↑(J σ α d) ∈ nhds (0 : mv_power_series σ α) := 
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

lemma to_ring_subgroups_basis : ring_subgroups_basis (λ d, (J σ α d).to_add_subgroup) := 
  ring_subgroups_basis.of_comm _
  (λ d e, by { use d ⊔ e, apply antitone.map_sup_le (J_antitone σ α), })
  (λ d, by { 
    use d, intro f, rintro ⟨f, g, hf, hg, rfl⟩, 
    simp only [submodule.coe_to_add_subgroup, set_like.mem_coe] at hf hg ⊢,
    refine ideal.mul_mem_left _ _ hg, })
  (λ f d, by { 
    use d, intros g hg, rw set.mem_preimage, 
    simp only [mem_J, submodule.coe_to_add_subgroup, set_like.mem_coe] at hg ⊢,
    intros e he, rw coeff_mul,
    apply finset.sum_eq_zero,
    intros uv huv, convert mul_zero _, apply hg, 
    rw finsupp.mem_antidiagonal at huv,
    apply le_trans _ he, rw ← huv,
    rw finsupp.le_iff_exists_add, use uv.fst, rw add_comm, })

end ideals

section discrete_topology

variables (α : Type*) [comm_ring α] [uniform_space α] [_root_.uniform_add_group α]
variable [discrete_topology α]

lemma to_submodule_basis : submodules_basis (J σ α) := submodules_basis.mk 
  (λ d e, by {
    use d + e, rw le_inf_iff, 
    split,
    apply J_antitone, rw finsupp.le_iff_exists_add, exact ⟨e, rfl⟩, 
    apply J_antitone, rw [finsupp.le_iff_exists_add, add_comm], exact ⟨d, rfl⟩, })
  (λ f d, by { rw filter.eventually_iff_exists_mem, 
    use ↑(J σ α d), apply and.intro (J_mem_nhds_zero σ α d),
    intros g hg, 
    rw [smul_eq_mul, mul_comm], 
    refine ideal.mul_mem_left _ f _, 
    simpa only [set_like.mem_coe] using hg, } )

@[ext]
lemma _root_.topological_space_eq_iff_nhds_eq {α : Type*} (τ τ': topological_space α) : 
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

example : mv_power_series.topological_space σ α = (to_submodule_basis σ α).topology := 
begin
  let τ := mv_power_series.topological_space σ α,
  let τ' := (to_submodule_basis σ α).topology, 
  suffices : τ = τ', exact this,
  rw topological_space_eq_iff_nhds_eq, 
  suffices : ∀ s, s ∈ @nhds _ τ 0 ↔ s ∈ @nhds _ τ' 0,
  -- mv nhds from 0 to a
  sorry, 
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
    rw ← coeff_eq_apply f e, rw hf e, -- (hd e he), 
    exact mem_of_mem_nhds (ht e), 
    convert finset.le_sup _,
    simp only [id.def], 
    simp only [set.finite.mem_to_finset], exact he, },
  { rintro ⟨d, hd⟩,
    exact (nhds 0).sets_of_superset (J_mem_nhds_zero σ α d) hd,}  
end

end discrete_topology

end mv_power_series

end mv_power_series

#exit

example {α : Type*} [comm_ring α] [topological_space α] [topological_ring α] 
  (V : set α) (a b : α) : V ∈ nhds (a + b) ↔ (has_add.add a) ⁻¹' V ∈ nhds b :=
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

example {α : Type*} [comm_ring α] [topological_space α] [topological_ring α] 
  (V : set α) (a b : α) (hV : V ∈ nhds (a + b)) : (has_add.add a) ⁻¹' V ∈ nhds b :=
begin
    rw [(homeomorph.add_left a).nhds_eq_comap],
    exact filter.preimage_mem_comap hV,
end
