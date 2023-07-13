import mv_power_series.linear_topology

/- # Substitutions in power series 

We follow Bourbaki, Algèbre, chap. 4, §4, n° 3 -/

variables (α : Type*) [comm_ring α] 

variables (R : Type*) [comm_ring R] [algebra α R] 

-- variables {ι : Type*} [nonempty ι] {J : ι → ideal R} (hJ : ideals_basis J)

-- instance zz1 : topological_space R := ideals_basis.topology hJ

-- instance zz2 := ideals_basis.to_topological_ring hJ
  
variables [topological_space R] [topological_ring R]
variables [topological_space α] [topological_ring α]
variables (σ : Type*) 


open mv_power_series

-- set_option trace.class_instances true

example {α β γ : Type*} (φ : α → β) (ψ : β → γ) (f : filter α) (g : filter β) (h : filter γ) (hφ : filter.tendsto φ f g) (hψ : filter.tendsto ψ g h) :
  filter.tendsto (ψ ∘ φ) f h := 
begin
refine filter.tendsto.comp hψ hφ,
end

lemma continuous.tendsto_apply_pow_of_constant_coeff_zero (φ : mv_power_series σ α →ₐ[α] R) 
  (hφ : continuous φ) (s : σ):
  filter.tendsto (λ n : ℕ, φ((X s) ^ n)) filter.at_top (nhds 0) := 
begin
  rw ← φ.map_zero, 
  refine filter.tendsto.comp hφ.continuous_at _, 
  apply tendsto_pow_of_constant_coeff_zero, 
  simp only [constant_coeff_X],
end

lemma continuous.apply_variables (φ : mv_power_series σ α →ₐ[α] R) 
  (hφ : continuous φ) (s : σ):
  filter.tendsto (λ s : σ, φ(X s)) filter.cofinite (nhds 0) := 
begin
  rw ← φ.map_zero, 
  refine filter.tendsto.comp hφ.continuous_at _, 
  exact variables_tendsto_zero,
end
