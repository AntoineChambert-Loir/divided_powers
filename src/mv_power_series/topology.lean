import ring_theory.power_series.basic
import mv_power_series.order
-- import topology.algebra.infinite_sum.basic
import ..infinite_sum.basic
import topology.algebra.ring.basic
import topology.uniform_space.basic
import topology.uniform_space.pi
import topology.uniform_space.separation
import topology.order.basic
import data.set.finite

import ..antidiagonal

lemma finset.prod_one_add {ι α: Type*} [comm_ring α] {f : ι → α} (s : finset ι) :
  s.prod (λ i, 1 + f i) = s.powerset.sum (λ t, t.prod f) := 
begin
  simp_rw add_comm,
  rw finset.prod_add,
  congr,
  ext t,
  convert mul_one _,
  apply finset.prod_eq_one,
  intros i hi, refl,
end

lemma mv_power_series.coeff_eq_apply {σ α :Type*} [semiring α] 
  (f : mv_power_series σ α) (d : σ →₀ ℕ) :
  mv_power_series.coeff α d f = f d := rfl


namespace mv_power_series

open function

variables (σ : Type*) (α : Type*) 


section topological

variable [topological_space α] 

/-- The pointwise topology on mv_power_series -/
instance : topological_space (mv_power_series σ α) := 
Pi.topological_space 

/-- Components are continuous -/
lemma continuous_component :
  ∀  (d : σ →₀ ℕ), continuous (λ a : mv_power_series σ α, a d) :=
continuous_pi_iff.mp continuous_id

variables {σ α} 
/-- coeff are continuous-/
lemma continuous_coeff [semiring α] (d : σ →₀ ℕ) : continuous (mv_power_series.coeff α d) :=
continuous_component σ α d

/-- constant_coeff is continuous -/
lemma continuous_constant_coeff [semiring α] : continuous (constant_coeff σ α) :=
continuous_component σ α 0

/-- A family of power series converges iff it converges coefficientwise -/
lemma tendsto_iff_coeff_tendsto [semiring α] {ι : Type*} (f : ι → mv_power_series σ α)
  (u : filter ι) (g : mv_power_series σ α) :
  filter.tendsto f u (nhds g) ↔ 
  ∀ (d : σ →₀ ℕ), filter.tendsto (λ i, coeff α d (f i)) u (nhds (coeff α d g)) :=
begin
  rw nhds_pi, rw filter.tendsto_pi, 
  apply forall_congr,
  intro d,
  refl,
end

variables (σ α)
/-- The semiring topology on mv_power_series of a topological semiring -/
lemma topological_semiring [semiring α] [topological_semiring α] :
  topological_semiring (mv_power_series σ α) := 
{  to_has_continuous_add := 
  begin
    apply has_continuous_add.mk,
    apply continuous_pi , 
    intro d, 
    simp only [pi.add_apply],
    change continuous ((λ (u : α × α), u.fst + u.snd) 
      ∘ λ (a : mv_power_series σ α × mv_power_series σ α), 
        (a.fst d, a.snd d)), 
    apply continuous.comp,
    exact continuous_add,
    apply continuous.prod_mk,
    exact continuous.fst' (continuous_component σ α d),
    exact continuous.snd' (continuous_component σ α d),
  end,
  to_has_continuous_mul := 
  begin
    apply has_continuous_mul.mk,
    apply continuous_pi,
    intro d,
    change continuous (λ (a : mv_power_series σ α × mv_power_series σ α),
      d.antidiagonal.sum (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)), a.fst x.fst * a.snd x.snd)), 
    apply continuous_finset_sum,
    intros i hi, 
    change continuous ((λ (u : α × α), u.fst * u.snd) 
      ∘ λ (a : mv_power_series σ α × mv_power_series σ α), 
        (a.fst i.fst, a.snd i.snd)), 
    apply continuous.comp,
    exact continuous_mul,
    apply continuous.prod_mk,
    exact continuous.fst' (continuous_component σ α i.fst),
    exact continuous.snd' (continuous_component σ α i.snd),
  end }

/-- The ring topology on mv_power_series of a topological ring -/
lemma topological_ring [ring α] [topological_ring α] :
  topological_ring (mv_power_series σ α) := 
{ to_topological_semiring := topological_semiring σ α,
  to_has_continuous_neg := 
  begin
    apply has_continuous_neg.mk,
    apply continuous_pi,
    intro d,
    change continuous ((λ u : α, - u) ∘ (λ a : mv_power_series σ α, a d)),
    apply continuous.comp, 
    exact continuous_neg,
    exact continuous_component σ α d,
  end  }

/-- mv_power_series on a t2_space form a t2_space -/
lemma t2_space [t2_space α] :
  t2_space (mv_power_series σ α) := 
begin
  apply t2_space.mk,
  intros x y h, 
  rw function.ne_iff at h,
  obtain ⟨d, h⟩ := h,
  obtain ⟨u, v, huv⟩ := t2_separation h,
  use (λ x, x d) ⁻¹' u,
  use (λ x, x d) ⁻¹' v,
  split,
  exact is_open.preimage (continuous_component σ α d) huv.1,
  split,
  exact is_open.preimage (continuous_component σ α d) huv.2.1,
  split,
  simp only [set.mem_preimage], exact huv.2.2.1,
  split,
  simp only [set.mem_preimage], exact huv.2.2.2.1,
  exact disjoint.preimage _ huv.2.2.2.2,
end

end topological

section uniform

variable [uniform_space α]

/-- The componentwise uniformity on mv_power_series -/
instance uniform_space : uniform_space (mv_power_series σ α) := 
Pi.uniform_space (λ (i : σ →₀ ℕ), α)

/-- Components are uniformly continuous -/
lemma uniform_continuous_component :
  ∀  (d : σ →₀ ℕ), uniform_continuous (λ a : mv_power_series σ α, a d) :=
uniform_continuous_pi.mp uniform_continuous_id

/-- The uniform_add_group structure on mv_power_series of a uniform_add_group -/
lemma uniform_add_group [add_group α] [uniform_add_group α] :
  uniform_add_group (mv_power_series σ α) :=
begin
  apply uniform_add_group.mk,
  rw uniform_continuous_pi,
  intros d,
  let g : mv_power_series σ α × mv_power_series σ α → α := 
  (λ (u : α × α) , u.fst - u.snd) ∘ (λ x, (x.fst d, x.snd d)),
  change uniform_continuous g,
  apply uniform_continuous.comp,
  exact uniform_continuous_sub,
  apply uniform_continuous.prod_mk,

  change uniform_continuous ((λ x : mv_power_series σ α, x d) ∘ (λ a : mv_power_series σ α × mv_power_series σ α, a.fst)), 
  apply uniform_continuous.comp,
  apply uniform_continuous_component,
  exact uniform_continuous_fst,

  change uniform_continuous ((λ x : mv_power_series σ α, x d) ∘ (λ a : mv_power_series σ α × mv_power_series σ α, a.snd)), 
  apply uniform_continuous.comp,
  apply uniform_continuous_component,
  exact uniform_continuous_snd,
end

/-- Completeness of the uniform structure on mv_power_series -/
lemma complete_space [add_group α] [complete_space α] :
complete_space (mv_power_series σ α) :=
begin
  apply complete_space.mk,
  intros f hf, 
  suffices : ∀ d, ∃ x, f.map (λ a, a d) ≤ nhds x,
  use (λ d, (this d).some),
  rw [nhds_pi, filter.le_pi], 
  intro d, 
  exact (this d).some_spec,
  intro d,
  use Lim (f.map (λ a, a d)), 
  exact (cauchy.map hf (uniform_continuous_component σ α d)).le_nhds_Lim, 
end

/-- Separation of the uniform structure on mv_power_series -/
lemma separated_space [_root_.separated_space α] :
  separated_space (mv_power_series σ α) := 
begin
  rw separated_iff_t2,
  haveI : _root_.t2_space α, rw ← separated_iff_t2, apply_instance,
  exact t2_space σ α,
  /-  rw separated_def,
      intros x y hr,
      ext d,
      exact uniform_space.eq_of_separated_of_uniform_continuous
        (uniform_continuous_component σ α d) hr, -/
end

lemma uniform_topological_ring [ring α] [_root_.uniform_add_group α] [_root_.topological_ring α] : 
  _root_.topological_ring (mv_power_series σ α) :=
{ to_has_continuous_add := 
  begin
    haveI := uniform_add_group σ α ,
    apply has_continuous_add.mk,
    apply uniform_continuous.continuous, 
    exact uniform_continuous_add , 
  end,
  to_has_continuous_mul := 
  begin
    apply has_continuous_mul.mk,
    apply continuous_pi,
    intro d,
    change continuous (λ (a : mv_power_series σ α × mv_power_series σ α),
      d.antidiagonal.sum (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)), a.fst x.fst * a.snd x.snd)), 
    apply continuous_finset_sum,
    intros i hi, 
    change continuous ((λ (u : α × α), u.fst * u.snd) 
      ∘ λ (a : mv_power_series σ α × mv_power_series σ α), 
        (a.fst i.fst, a.snd i.snd)), 
    apply continuous.comp,
    exact continuous_mul,
    apply continuous.prod_mk,
    exact continuous.fst' (continuous_component σ α i.fst),
    exact continuous.snd' (continuous_component σ α i.snd),
  end,
  to_has_continuous_neg := 
  begin
    haveI := uniform_add_group σ α ,
    apply has_continuous_neg.mk,
    apply uniform_continuous.continuous, 
    exact uniform_continuous_neg,   
  end }

end uniform

example [σ_ne : nonempty σ]: no_max_order (σ →₀ ℕ) :=
begin
  apply no_max_order.mk,
  intro a, 
  use a + finsupp.single σ_ne.some 1, 
  simp only [lt_iff_le_and_ne, zero_le, le_add_iff_nonneg_right, ne.def, self_eq_add_right, finsupp.single_eq_zero,
    nat.one_ne_zero, not_false_iff, and_self],
end


section

variables {σ α}
variables [topological_space α] [comm_ring α] [_root_.topological_ring α]

theorem pow_tendsto_zero_of_is_nilpotent 
  (f : mv_power_series σ α)
  (hf : is_nilpotent (constant_coeff σ α f)) :
  filter.tendsto (λ (n : ℕ), f ^ n)  filter.at_top (nhds 0) := 
begin
  classical,
  obtain⟨m, hm⟩ := hf,
  rw mv_power_series.tendsto_iff_coeff_tendsto,
  intro d,
  simp only [coeff_zero], 
  apply tendsto_at_top_of_eventually_const,
  intros n hn, 
  exact coeff_eq_zero_of_constant_coeff_nilpotent f m hm d n hn, 
end

/-- Bourbaki, Algèbre, chap. 4, §4, n°2, corollaire de la prop. 3 -/
theorem pow_tendsto_zero_iff_is_nilpotent [discrete_topology α] 
  (f : mv_power_series σ α) :
  filter.tendsto (λ (n : ℕ), f ^ n)  filter.at_top (nhds 0)
  ↔ is_nilpotent (constant_coeff σ α f) :=
begin
  split,
  { intro h, 
    suffices : filter.tendsto (λ (n : ℕ), constant_coeff σ α (f ^ n))  filter.at_top (nhds 0),
    simp only [filter.tendsto_def] at this,
    specialize this {0} _,
    suffices : ∀ x : α, {x} ∈ nhds x, exact this 0,
    rw ← discrete_topology_iff_singleton_mem_nhds, apply_instance,
    simp only [map_pow, filter.mem_at_top_sets, ge_iff_le, set.mem_preimage, set.mem_singleton_iff] at this,
    obtain ⟨m, hm⟩ := this,
    use m, apply hm m (le_refl m), 

    rw ← filter.tendsto_map'_iff ,
    simp only [filter.tendsto, filter.map_le_iff_le_comap] at h ⊢,
    apply le_trans h,
    apply filter.comap_mono,
    rw ← filter.map_le_iff_le_comap,
    exact continuous_constant_coeff.continuous_at,  },
  exact pow_tendsto_zero_of_is_nilpotent f, 
end

end

section summable

variables [semiring α] [topological_space α]

variables {σ α}

/-- A power series is the sum (in the sense of summable families) of its monomials -/
lemma has_sum_of_monomials_self (f : mv_power_series σ α): 
  has_sum (λ (d : σ →₀ ℕ), monomial α d (coeff α d f)) f := 
begin
  rw pi.has_sum,
  intro d,
  convert has_sum_single d _,
  { rw [← coeff_apply f d, ← coeff_apply (monomial α d (coeff α d f)) d, coeff_apply],
    rw [coeff_monomial_same], },
  { intros b h,
    change coeff α d ((monomial α b) ((coeff α b) f)) = 0,
    rw coeff_monomial_ne (ne.symm h), },
end  

/-- If the coefficient space is T2, then the power series is `tsum` of its monomials -/
lemma as_tsum [_root_.t2_space α] (f : mv_power_series σ α) :
  f = tsum (λ (d : σ →₀ ℕ), monomial α d (coeff α d f)) := 
begin
  classical,
  haveI := mv_power_series.t2_space σ α, 
  simp only [tsum, dif_pos f.has_sum_of_monomials_self.summable],
  exact has_sum.unique f.has_sum_of_monomials_self (classical.some_spec _),
end

/-- A power series is the sum (in the sense of summable families) of its monomials -/
lemma has_sum_of_homogeneous_components_self (w : σ → ℕ) (f : mv_power_series σ α) :
  has_sum (λ p, homogeneous_component w p f) f := 
begin
  rw pi.has_sum,
  intro d,
  convert has_sum_single (weight w d) _,
  { rw ← coeff_apply f d, 
    rw ← coeff_apply (homogeneous_component w (weight w d) f) d, 
    rw coeff_homogeneous_component,
    simp only [eq_self_iff_true, if_true], },
  { intros p h,
    rw ← coeff_apply (homogeneous_component w p f) d, 
    rw coeff_homogeneous_component,
    rw if_neg (ne.symm h), },
end  

lemma homogeneous_components_self_summable (w : σ → ℕ) (f : mv_power_series σ α) :
  summable (λ p, homogeneous_component w p f) := 
(has_sum_of_homogeneous_components_self w f).summable 

lemma as_tsum_of_homogeneous_components_self [_root_.t2_space α] (w : σ → ℕ) (f : mv_power_series σ α) :
  f = tsum (λ p, homogeneous_component w p f) := 
begin
  classical,
  haveI := t2_space σ α,
  apply has_sum.unique (has_sum_of_homogeneous_components_self w f),
  simp only [tsum, dif_pos (homogeneous_components_self_summable w f)],
  apply classical.some_spec _,
end

end summable

end mv_power_series