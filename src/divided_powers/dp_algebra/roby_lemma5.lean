
import ...for_mathlib.ring_theory.tensor_product
import ring_theory.ideal.quotient_operations
import algebra.algebra.subalgebra.basic
import divided_powers.dp_algebra.roby_lemma9

-- import ...generalisation.generalisation_linter



open_locale tensor_product
local notation  M ` ⊗[`:100 R `] `:0 N:100 := tensor_product R M N

variables {A : Type*} [comm_ring A] {R S R' S' : Type*} 
  [comm_ring R] [comm_ring S] [comm_ring R'] [comm_ring S']
  [algebra A R] [algebra A S] [algebra A R'] [algebra A S'] 
  (f : R →ₐ[A] R') (g : S →ₐ[A] S')

private def I : ideal (R ⊗[A] S) := 
  f.to_ring_hom.ker.map (algebra.tensor_product.include_left : R →ₐ[A] (R ⊗[A] S))
  ⊔ (g.to_ring_hom.ker.map (algebra.tensor_product.include_right : S →ₐ[A] (R ⊗[A] S)))

private lemma I_le_ker : I f g ≤  ring_hom.ker (algebra.tensor_product.map f g) := 
begin
    simp only [I, sup_le_iff,ideal.map_le_iff_le_comap],
    split,
    intros x hx, 
    simp only [alg_hom.to_ring_hom_eq_coe, ring_hom.mem_ker, alg_hom.coe_to_ring_hom] at hx,
    rw [ideal.mem_comap, algebra.tensor_product.include_left_apply, ring_hom.mem_ker,
      algebra.tensor_product.map_tmul, map_one, hx, tensor_product.zero_tmul],

    intros y hy,
    simp only [alg_hom.to_ring_hom_eq_coe, ring_hom.mem_ker, alg_hom.coe_to_ring_hom] at hy,
    rw [ideal.mem_comap, algebra.tensor_product.include_right_apply, ring_hom.mem_ker,
      algebra.tensor_product.map_tmul, map_one, hy, tensor_product.tmul_zero], 
end

variable {f}


private noncomputable def inv_f_fun (hf : function.surjective f) :=
λ r, ideal.quotient.mkₐ A (I f g) (algebra.tensor_product.include_left ((hf r).some))

private lemma hinv_f (hf : function.surjective f) : 
  ∀ r, (inv_f_fun g hf) (f r) = ideal.quotient.mkₐ A (I f g) (algebra.tensor_product.include_left r) := 
begin
  intro r, 
  simp only [inv_f_fun], 
  dsimp,
  rw ideal.quotient.eq,
  rw ← tensor_product.sub_tmul,
  simp only [I],
  apply ideal.mem_sup_left,
  apply ideal.mem_map_of_mem,
  rw [ring_hom.mem_ker, map_sub, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom,
  (hf (f r)).some_spec, sub_self],
end

private noncomputable def inv_f (hf : function.surjective f) : 
  R' →ₐ[A] (R ⊗[A] S ⧸ (I f g)):= {
to_fun := inv_f_fun g hf, 
map_one' := by rw [← f.map_one, hinv_f g hf]; 
  exact map_one (ideal.quotient.mkₐ A (I f g)),
map_mul' := λ x' y', 
begin
  obtain ⟨x, rfl⟩ := hf x', obtain ⟨y, rfl⟩ := hf y', 
  rw ← f.map_mul, 
  simp only [hinv_f g hf], 
  rw ← map_mul, apply congr_arg, rw map_mul, 
end,
map_add' := λ x' y', 
begin
  obtain ⟨x, rfl⟩ := hf x', obtain ⟨y, rfl⟩ := hf y', 
  rw ← f.map_add, 
  simp only [hinv_f g hf],
  rw ← map_add, apply congr_arg, rw map_add, 
end,
map_zero' := 
begin 
  rw [← f.map_zero, hinv_f g hf], apply congr_arg, rw map_zero,
end,
commutes' := λ a,
begin
  rw [← f.commutes a, hinv_f g hf],
  rw (algebra.tensor_product.include_left).commutes,
  rw (ideal.quotient.mkₐ A (I f g)).commutes,
end }

variable (f) 
variable {g}

private noncomputable def inv_g_fun (hg : function.surjective g) :=
λ s, ideal.quotient.mkₐ A (I f g) (algebra.tensor_product.include_right ((hg s).some))

private lemma hinv_g (hg : function.surjective g) : 
  ∀ s, (inv_g_fun f hg) (g s) = ideal.quotient.mkₐ A (I f g) (algebra.tensor_product.include_right s) := 
begin
  intro s,
  simp only [inv_g_fun], 
  dsimp,
  rw ideal.quotient.eq,
  rw ← tensor_product.tmul_sub,
  simp only [I],
  apply ideal.mem_sup_right,
  apply ideal.mem_map_of_mem,
  rw [ring_hom.mem_ker, map_sub, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom,
  (hg (g s)).some_spec, sub_self],
end


private noncomputable def inv_g (hg : function.surjective g) : 
  S' →ₐ[A] (R ⊗[A] S ⧸ (I f g)):= {
to_fun := inv_g_fun f hg, 
map_one' := by rw [← g.map_one, hinv_g f hg]; 
  exact map_one (ideal.quotient.mkₐ A (I f g)),
map_mul' := λ x' y', 
begin
  obtain ⟨x, rfl⟩ := hg x', obtain ⟨y, rfl⟩ := hg y', 
  rw ← map_mul, 
  simp only [hinv_g f hg], 
  rw ← map_mul, apply congr_arg, rw map_mul, 
end,
map_add' := λ x' y', 
begin
  obtain ⟨x, rfl⟩ := hg x', obtain ⟨y, rfl⟩ := hg y', 
  rw ← g.map_add, 
  simp only [hinv_g f hg],
  rw ← map_add, apply congr_arg, rw map_add, 
end,
map_zero' := 
begin 
  rw [← g.map_zero, hinv_g f hg], apply congr_arg, rw map_zero,
end,
commutes' := λ a,
begin
  rw [← g.commutes a, hinv_g f hg],
  rw (algebra.tensor_product.include_right).commutes,
  rw (ideal.quotient.mkₐ A (I f g)).commutes,
end }

variables {f g}
private lemma hinv_f_tens_g (hf : function.surjective f) (hg : function.surjective g) 
(r : R) (s : S) : (inv_f g hf) (f r) * (inv_g f hg) (g s) 
  = (ideal.quotient.mk (I f g)) (r ⊗ₜ[A] s) := 
begin
  simp only [inv_f, inv_g],
  dsimp,
  rw hinv_f g hf, rw hinv_g f hg, rw ← map_mul,
  rw ideal.quotient.mkₐ_eq_mk,
  apply congr_arg, 
  simp only [algebra.tensor_product.include_left_apply, algebra.tensor_product.include_right_apply,
  algebra.tensor_product.tmul_mul_tmul, mul_one, one_mul],
end


/- example (hf : function.surjective f) (hg : function.surjective g)  : 
function.left_inverse (algebra.tensor_product.product_map
  (inv_f f g hf) (inv_g f g hg)) id := sorry
 -/

-- Roby, lemma 5
lemma ker_tens (hf : function.surjective f) (hg : function.surjective g) : 
  ring_hom.ker (algebra.tensor_product.map f g) 
  = (f.to_ring_hom.ker.map (algebra.tensor_product.include_left : R →ₐ[A] (R ⊗[A] S))) 
  ⊔ ((g.to_ring_hom.ker.map (algebra.tensor_product.include_right : S →ₐ[A] (R ⊗[A] S)))) :=
begin  
  change _ = I f g,
  rw alg_hom.ker_eq_ideal_iff,
  use I_le_ker f g, 
  suffices : function.left_inverse (algebra.tensor_product.product_map
  (inv_f g hf) (inv_g f hg)) _,
  apply function.left_inverse.injective this,
  rw function.left_inverse_iff_comp, 
  rw ← alg_hom.coe_comp _ _,
  have : @id (R ⊗[A] S ⧸ I f g) = alg_hom.id A _, 
  { ext, rw alg_hom.id_apply, refl, },
  rw this,
  apply congr_arg, 
  apply ideal.quotient.alg_hom_ext, 
  apply fun_like.coe_injective,
  simp only [alg_hom.coe_comp, ideal.quotient.mkₐ_eq_mk, alg_hom.id_comp], 
  rw ←ideal.quotient.mkₐ_eq_mk A (I f g), 
  simp only [← alg_hom.coe_comp],
  apply congr_arg,
  apply algebra.tensor_product.ext, 
  intros r s,
  simp only [alg_hom.comp_apply],
  rw [ideal.quotient.liftₐ_apply, ideal.quotient.mkₐ_eq_mk, ideal.quotient.lift_mk (I f g)  _ _, alg_hom.coe_to_ring_hom, algebra.tensor_product.map_tmul, algebra.tensor_product.product_map_apply_tmul], 
  exact hinv_f_tens_g hf hg r s,
end


