import divided_powers.dp_algebra.init
import ring_theory.power_series.basic
import topology.algebra.infinite_sum.basic
import topology.algebra.ring.basic
import topology.uniform_space.basic
import topology.uniform_space.pi

section mv_power_series

variables (σ : Type*)
variables (α : Type*) [topological_space α] 

instance : topological_space (mv_power_series σ α) := 
Pi.topological_space 

lemma mv_power_series.continuous_component (d : σ →₀ ℕ) :
  continuous (λ a : mv_power_series σ α, a d) :=
begin
  revert d,
  rw ← continuous_pi_iff,
  exact continuous_id,
end

instance mv_power_series.topological_semiring [semiring α] [topological_semiring α] :
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
    exact continuous.fst' (mv_power_series.continuous_component σ α d),
    exact continuous.snd' (mv_power_series.continuous_component σ α d),
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
    exact continuous.fst' (mv_power_series.continuous_component σ α i.fst),
    exact continuous.snd' (mv_power_series.continuous_component σ α i.snd),
  end }

instance mv_power_series.topological_ring [ring α] [topological_ring α] :
  topological_ring (mv_power_series σ α) := 
{ to_topological_semiring := mv_power_series.topological_semiring σ α,
  to_has_continuous_neg := 
  begin
    apply has_continuous_neg.mk,
    apply continuous_pi,
    intro d,
    change continuous ((λ u : α, - u) ∘ (λ a : mv_power_series σ α, a d)),
    apply continuous.comp, 
    exact continuous_neg,
    exact mv_power_series.continuous_component σ α d,
  end  }

instance [ring α] [uniform_space α] [uniform_add_group α][topological_ring α] : uniform_space (mv_power_series σ α) := 
topological_add_group.to_uniform_space (mv_power_series σ α)

example [ring α] [uniform_space α] [uniform_add_group α][topological_ring α] [complete_space α] :
complete_space (mv_power_series σ α) :=
begin
  apply complete_space.mk,
  intros f hf, 
  let φ : (σ →₀ ℕ)→ filter α := λ d, f.map (mv_power_series.coeff α d),
  -- suffices hφ : ∀ d, cauchy (φ d),
  suffices : ∀ d, ∃ x, φ d ≤ nhds x,
  let ξ := (λ d, (this d).some),
  use ξ,
  -- suffices : f.tendsto ξ, 
  rw nhds_pi, 
  rw filter.le_pi , 
  intro d, 
--  simp only [ξ],
  exact (this d).some_spec,
  intro d,
  suffices : cauchy (φ d),
--   haveI : (φ d).ne_bot, sorry,
  use Lim (φ d), sorry, -- exact this.le_nhds_Lim,
  simp only [φ],
  rw cauchy_map_iff,
  split,
  rw cauchy_iff at hf, exact hf.1,
end



example [σ_ne : nonempty σ]: no_max_order (σ →₀ ℕ) :=
begin
  apply no_max_order.mk,
  intro a, 
  use a + finsupp.single σ_ne.some 1, 
  simp only [lt_iff_le_and_ne, zero_le, le_add_iff_nonneg_right, ne.def, self_eq_add_right, finsupp.single_eq_zero,
    nat.one_ne_zero, not_false_iff, and_self],
end

example (σ : Type*) [σ_ne : nonempty σ] (f : mv_power_series σ α) : summable f := 
begin
  /- apply summable_of_ne_finset_zero ,
  swap,
  exact {0},
  intros b hb, simp only [finset.mem_singleton] at hb,
   -/
haveI : no_max_order (finset (σ →₀ ℕ)), sorry,
use 0,
simp only [has_sum],
intros x hx,
simp only [filter.mem_map],
-- have := filter.Ioi_mem_at_top (0 : σ →₀ ℕ), 
apply filter.sets_of_superset, 
apply filter.Ioi_mem_at_top ∅,
apply_instance,apply_instance,
intros s hs, simp only [set.mem_preimage], 
simp only [set.mem_Ioi, finset.lt_eq_subset, finset.empty_ssubset] at hs, 
end

end mv_power_series

section exponential

variables (R : Type*) [comm_ring R]

def is_exponential (f : power_series R) : Prop :=


end exponential