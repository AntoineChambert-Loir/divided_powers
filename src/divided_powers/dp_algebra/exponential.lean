import divided_powers.dp_algebra.init
import ring_theory.power_series.basic
import topology.algebra.infinite_sum.basic
import topology.algebra.ring.basic
import topology.uniform_space.basic
import topology.uniform_space.pi
import topology.uniform_space.separation

section mv_power_series

variables (σ : Type*)
variables (α : Type*) 

section topological

variable [topological_space α] 

/-- The pointwise topology on mv_power_series -/
instance : topological_space (mv_power_series σ α) := 
Pi.topological_space 

/-- Components are continuous -/
lemma mv_power_series.continuous_component :
  ∀  (d : σ →₀ ℕ), continuous (λ a : mv_power_series σ α, a d) :=
continuous_pi_iff.mp continuous_id

/-- The semiring topology on mv_power_series of a topological semiring -/
def mv_power_series.topological_semiring [semiring α] [topological_semiring α] :
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

/-- The ring topology on mv_power_series of a topological ring -/
def mv_power_series.topological_ring [ring α] [topological_ring α] :
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

end topological

section uniform

variable [uniform_space α]

/-- The componentwise uniformity on mv_power_series -/
instance mv_power_series.uniform_space [uniform_space α] : uniform_space (mv_power_series σ α) := 
Pi.uniform_space (λ (i : σ →₀ ℕ), α)

/-- Components are uniformly continuous -/
lemma mv_power_series.uniform_continuous_component :
  ∀  (d : σ →₀ ℕ), uniform_continuous (λ a : mv_power_series σ α, a d) :=
uniform_continuous_pi.mp uniform_continuous_id

/-- The uniform_add_group structure on mv_power_series of a uniform_add_group -/
def mv_power_series.uniform_add_group [add_group α] [uniform_space α]
  [uniform_add_group α] : uniform_add_group (mv_power_series σ α) :=
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
  apply mv_power_series.uniform_continuous_component,
  exact uniform_continuous_fst,

  change uniform_continuous ((λ x : mv_power_series σ α, x d) ∘ (λ a : mv_power_series σ α × mv_power_series σ α, a.snd)), 
  apply uniform_continuous.comp,
  apply mv_power_series.uniform_continuous_component,
  exact uniform_continuous_snd,
end

/-- Completeness of the uniform structure on mv_power_series -/
lemma mv_power_series.complete_space [add_group α] [uniform_space α] [uniform_add_group α] [complete_space α] :
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
  exact (cauchy.map hf (mv_power_series.uniform_continuous_component σ α d)).le_nhds_Lim, 
end

/-- Separation of the uniform structure on mv_power_series -/
lemma mv_power_series.separated_space [add_group α] [uniform_space α]
  [uniform_add_group α] [separated_space α] :
  separated_space (mv_power_series σ α) := 
begin
  rw separated_def,
  intros x y hr,
  ext d,
  exact uniform_space.eq_of_separated_of_uniform_continuous
    (mv_power_series.uniform_continuous_component σ α d) hr,
end

lemma mv_power_series.uniform_topological_ring [ring α] [uniform_space α]
  [uniform_add_group α] [topological_ring α] : 
  topological_ring (mv_power_series σ α) :=
{ to_has_continuous_add := 
  begin
    haveI := mv_power_series.uniform_add_group σ α ,
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
    exact continuous.fst' (mv_power_series.continuous_component σ α i.fst),
    exact continuous.snd' (mv_power_series.continuous_component σ α i.snd),
  end,
  to_has_continuous_neg := 
  begin
    haveI := mv_power_series.uniform_add_group σ α ,
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