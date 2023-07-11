import topology.algebra.ring.basic
import ring_theory.ideal.basic
import topology.algebra.nonarchimedean.bases
import mv_power_series.topology
α
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

namespace mv_power_series

variables (σ α : Type*) [comm_ring α] [topological_space α] [_root_.topological_ring α] [discrete_topology α] 

variable {σ}
noncomputable def S : (σ →₀ ℕ) → ideal (mv_power_series σ α) := λ d, ideal.span {monomial α d 1}

lemma S_le_iff [nontrivial α] (d e : σ →₀ ℕ) : S α d ≤ S α e ↔ e ≤ d := 
begin
  simp only [S, ideal.span_le, set.singleton_subset_iff, ideal.mem_span_singleton, set_like.mem_coe],
  split,
  { rintro ⟨f, hf⟩, 
    rw ext_iff at hf, specialize hf d,
    simp only [coeff_monomial_same, coeff_monomial_mul] at hf,
    by_cases h : e ≤ d,
    exact h,
    rw if_neg h at hf, 
    exfalso,
    simpa only [one_ne_zero] using hf, },
  { intro h,
    suffices : ∃ e', e + e' = d, 
    obtain ⟨e', rfl⟩ := this,
    use monomial α e' 1,
    rw mv_power_series.monomial_mul_monomial, rw mul_one,
    use d - e,
     sorry, },
end


example : submodules_basis (S σ α) := submodules_basis.mk 
  (λ d e, by {
    use d + e, sorry})
  ({sorry})


example : has_ideals_basis (mv_power_series σ α) := sorry

example (σ α : Type*) [comm_ring α] [topological_space α] [discrete_topology α] 
  :
    linear_topological_ring (mv_power_series σ α) :=
{ to_has_ideal_basis := sorry }
sorry

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
