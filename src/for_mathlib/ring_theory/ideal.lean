import ring_theory.ideal.basic
import ring_theory.ideal.operations

lemma ideal.image_eq_map_of_surjective {A B : Type*} [semiring A]
  [semiring B] (f : A →+* B) (I : ideal A) (hf: function.surjective f) : 
  f '' I = I.map f:=
begin
  apply le_antisymm,
  rintros b ⟨a, ha, rfl⟩, 
  simp only [set_like.mem_coe],
  exact ideal.mem_map_of_mem f ha, 
  intros b hb,
  simp only [set_like.mem_coe] at hb,
  apply submodule.span_induction hb, 
  { exact λ x hx, hx, },
  { use 0, simp only [set_like.mem_coe, submodule.zero_mem, map_zero, eq_self_iff_true, and_self], },
  { rintros x y ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩, 
    use x + y,  
    simp only [set_like.mem_coe] at hx hy ⊢,
    simp only [I.add_mem hx hy, map_add, eq_self_iff_true, and_self], },
  { rintros b x ⟨x, hx, rfl⟩, 
    obtain ⟨a, rfl⟩ := hf b,
    use a • x, 
    split,
    exact I.smul_mem a (set_like.mem_coe.mp hx),
    simp only [smul_eq_mul, map_mul], },
end