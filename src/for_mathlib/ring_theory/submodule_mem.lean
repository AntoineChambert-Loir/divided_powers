import ring_theory.ideal.operations

namespace submodule

theorem mem_span_iff_exists_sum {R : Type*} [comm_semiring R] {M : Type*} [add_comm_monoid M] 
  [module R M] {ι : Type*} (f : ι → M) (x : M) :
  x ∈ span R (set.range f) ↔ ∃ (a : ι →₀ R), a.sum (λ (i : ι) (c : R), c • f i) = x :=
begin
  rw [← top_smul (span R (set.range f)), mem_ideal_smul_span_iff_exists_sum],
  exact exists_congr (λ a, ⟨λ ⟨ha, h⟩, h, λ h, ⟨λ i, mem_top, h⟩⟩),
end

theorem mem_span_iff_exists_sum' {R : Type*} [comm_semiring R] {M : Type*} [add_comm_monoid M]
  [module R M] {ι : Type*} (s : set ι) (f : ι → M) (x : M) :
  x ∈ span R (f '' s) ↔ ∃ (a : ↥s →₀ R), a.sum (λ (i : ↥s) (c : R), c • f ↑i) = x :=
begin
  rw [← top_smul (span R (f '' s)), mem_ideal_smul_span_iff_exists_sum'],
  exact exists_congr (λ a, ⟨λ ⟨ha, h⟩, h, λ h, ⟨λ i, mem_top, h⟩⟩)
end

theorem mem_span_set_iff_exists_sum {R : Type*} [comm_semiring R] {M : Type*} [add_comm_monoid M]
  [module R M] (s : set M) (x : M) :
  x ∈ span R s ↔ ∃ (a : s →₀ R), a.sum (λ (i : s) (c : R), c • ↑i) = x :=
begin
  conv_lhs {rw ← set.image_id s},
  rw [← top_smul (span R (id '' s)), mem_ideal_smul_span_iff_exists_sum'],
  exact exists_congr (λ a, ⟨λ ⟨ha, h⟩, h, λ h, ⟨λ i, mem_top, h⟩⟩),
end

end submodule