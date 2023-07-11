import topology.algebra.ring.basic
import ring_theory.ideal.basic
import topology.algebra.nonarchimedean.bases
import mv_power_series.topology

def has_submodules_basis (R : Type*) [comm_ring R] [topological_space R] 
  (M : Type*) [add_comm_group M] [module R M] [H : topological_space M] : Prop :=
∃ (ι : Type*) [nonempty ι] (B : ι → submodule R M) (hB : submodules_basis B), 
by exactI H = submodules_basis.topology hB

structure linear_topological_module {R : Type*} [comm_ring R] [topological_space R] 
  (M : Type*) [add_comm_group M] [module R M] [H : topological_space M]
(to_has_submodules_basis : has_submodules_basis R M)

structure linear_topological_ring (R : Type*)[comm_ring R] [topological_space R]
(to_has_ideal_basis : has_submodules_basis R R)

example (σ R : Type*) [comm_ring R] [topological_space R] [discrete_topology R] 
  :
  linear_topological_ring (mv_power_series σ R) :=
sorry


#exit

example {R : Type*} [comm_ring R] [topological_space R] [topological_ring R] 
  (V : set R) (a b : R) : V ∈ nhds (a + b) ↔ (has_add.add a) ⁻¹' V ∈ nhds b :=
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

example {R : Type*} [comm_ring R] [topological_space R] [topological_ring R] 
  (V : set R) (a b : R) (hV : V ∈ nhds (a + b)) : (has_add.add a) ⁻¹' V ∈ nhds b :=
begin
    rw [(homeomorph.add_left a).nhds_eq_comap],
    exact filter.preimage_mem_comap hV,
end
