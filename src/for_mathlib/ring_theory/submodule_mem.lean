import ring_theory.ideal.operations 



theorem submodule.mem_span_iff_exists_sum {R : Type*} {M : Type*} 
  [comm_semiring R] [add_comm_monoid M] [module R M] 
  {ι : Type*} (f : ι → M) (x : M) :
x ∈ submodule.span R (set.range f) ↔ 
∃ (a : ι →₀ R), a.sum (λ (i : ι) (c : R), c • f i) = x :=
begin
  rw ← submodule.top_smul (submodule.span R (set.range f)),  
  rw submodule.mem_ideal_smul_span_iff_exists_sum,
  apply exists_congr,
  exact λ a, ⟨λ ⟨ha, h⟩, h, λ h, ⟨λ i, submodule.mem_top, h⟩⟩,
end

theorem submodule.mem_span_iff_exists_sum' {R : Type*} {M : Type*} 
  [comm_semiring R] [add_comm_monoid M] [module R M] 
  {ι : Type*} (s : set ι) (f : ι → M) (x : M) :
x ∈ submodule.span R (f '' s) ↔ 
∃ (a : ↥s →₀ R), a.sum (λ (i : ↥s) (c : R), c • f ↑i) = x :=
begin
  rw ← submodule.top_smul (submodule.span R (f '' s)),  
  rw submodule.mem_ideal_smul_span_iff_exists_sum',
  apply exists_congr,
  exact λ a, ⟨λ ⟨ha, h⟩, h, λ h, ⟨λ i, submodule.mem_top, h⟩⟩,
end

theorem submodule.mem_span_set_iff_exists_sum {R : Type*} {M : Type*} 
  [comm_semiring R] [add_comm_monoid M] [module R M] 
  (s : set M) (x : M) :
x ∈ submodule.span R s ↔ 
∃ (a : s →₀ R), a.sum (λ (i : s) (c : R), c • ↑i) = x :=
begin
  conv_lhs {rw ← set.image_id s},
  rw ← submodule.top_smul (submodule.span R (id '' s)),  
  rw submodule.mem_ideal_smul_span_iff_exists_sum',
  apply exists_congr,
  exact λ a, ⟨λ ⟨ha, h⟩, h, λ h, ⟨λ i, submodule.mem_top, h⟩⟩,
end