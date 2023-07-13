import mv_power_series.strongly_summable.basic
import mv_power_series.topology


namespace mv_power_series

open function

variables {σ α : Type*}

namespace strongly_summable

variables {ι : Type*}

section semiring 

variable [semiring α]

lemma has_sum [topological_space α] {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) : _root_.has_sum f hf.sum :=  
pi.has_sum.mpr (hf.has_sum_coeff)

lemma summable [topological_space α] {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) : summable f := ⟨hf.sum, hf.has_sum⟩

lemma sum_eq_tsum [topological_space α] [_root_.t2_space α] {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) : hf.sum = tsum f :=
begin
  classical,
  ext d,
  simp only [tsum, dif_pos hf.summable],
  exact has_sum.unique (hf.has_sum_coeff d) 
    (has_sum.map (classical.some_spec hf.summable) _ (continuous_component σ α d)),
end

end semiring

section ring 

variable [ring α]
/- 
# Comparisons of the various convergences on `mv_power_series σ α`

Ref. : Bourbaki, *Algèbre*, IV, §4, n°2, Lemme 1.

* pour toute topologie : 
support fini => sommable : `strongly_summable.summable`
sommable => tend vers 0  : `tendsto_zero_of_summable` 

* pour topologie discrète : 
tend vers 0 => support fini : `summable.tendsto_cofinite_zero`
-/

example [topological_space α] {f : ι → mv_power_series σ α} :
  (strongly_summable f) → (_root_.summable f) := 
strongly_summable.summable 

-- TODO (?): replace topological_ring instance by topological_add_group…
example [topological_space α] [_root_.topological_ring α] {f : ι → mv_power_series σ α} :
  (_root_.summable f) → filter.tendsto f filter.cofinite (nhds 0) := 
by haveI := topological_ring σ α; exact tendsto_zero_of_summable

lemma iff_summable [topological_space α] [discrete_topology α]  {f : ι → mv_power_series σ α} : 
  (strongly_summable f) ↔ (_root_.summable f) :=
⟨summable, λ hf d, finite_support_of_summable (hf.map _ (continuous_component σ α d))⟩

lemma iff_summable' [topological_space α] [discrete_topology α] {f : ι → mv_power_series σ α} : 
  (strongly_summable f) ↔ filter.tendsto f filter.cofinite (nhds 0):=
begin
  haveI := topological_ring σ α,
  refine ⟨λ hf, hf.summable.tendsto_cofinite_zero, _⟩,
  rw [strongly_summable, nhds_pi, filter.tendsto_pi],
  exact forall_imp (λ d, finite_support_of_tendsto_zero),
end

end ring

end strongly_summable

section summable

variables [semiring α] [topological_space α]

/-- A family of power series is summable if their weighted orders tend to infinity. -/
lemma summable_of_weighted_order_tendsto_top {ι : Type*} (w : σ → ℕ) (f : ι → mv_power_series σ α) 
  (hf : filter.tendsto (λ i, weighted_order w (f i)) filter.cofinite (nhds ⊤)) : 
  summable f :=
(strongly_summable.of_weighted_order_tendsto_top w f hf).summable 

lemma summable_of_order_tendsto_top {ι : Type*} (f : ι → mv_power_series σ α) 
  (hf : filter.tendsto (λ i, order (f i)) filter.cofinite (nhds ⊤)) : summable f :=
(strongly_summable.of_order_tendsto_top f hf).summable

end summable

section strongly_multipliable

variables {ι : Type*} {f : ι → mv_power_series σ α} [comm_ring α] 

namespace strongly_summable

variables [_root_.uniform_space α] [_root_.uniform_add_group α] 

lemma has_prod_of_one_add (hf : strongly_summable f) :
  has_prod (λ i, 1 + f i) hf.to_strongly_multipliable.prod := 
begin
  classical,
  haveI := uniform_add_group σ α,
  intros V hV,
  simp only [filter.mem_map, filter.mem_at_top_sets, ge_iff_le, 
    finset.le_eq_subset, set.mem_preimage],
  let V₀ := (has_add.add (hf.to_strongly_multipliable.prod)) ⁻¹' V,
  have hV'₀ : V = (has_add.add (- hf.to_strongly_multipliable.prod)) ⁻¹' V₀,
  { simp only [V₀, ← set.preimage_comp, comp_add_left, add_right_neg], 
    ext x,
    rw [set.mem_preimage, zero_add], },
  have hV₀ : V₀ ∈ nhds(0 : mv_power_series σ α),
  { simp only [V₀], 
    apply continuous_at_def.mp (continuous.continuous_at ( continuous_add_left _)),
    rw add_zero, exact hV,
    { apply_instance }},
  simp only [nhds_pi, filter.mem_pi] at hV₀,
  obtain ⟨D, hD, t, ht, htV₀⟩ := hV₀,
  use hf.union_of_support_of_coeff_le (hD.to_finset.sup id),
  intros J hIJ,
  rw [hV'₀, set.mem_preimage],
  apply htV₀,
  simp only [set.mem_pi, pi.add_apply, pi.neg_apply],
  intros d hd,
  convert mem_of_mem_nhds (ht d),
  simp only [pi.zero_apply, neg_eq_zero, neg_add_eq_sub, sub_eq_zero],
  convert strongly_summable.finset.prod_of_one_add_eq hf d J _, 
  intros i hi,
  apply hIJ,
  revert hi,
  contrapose,
  simp only [strongly_summable.not_mem_union_of_support_of_coeff_le_iff],
  intros h e hed,
  exact h _ (le_trans hed (finset.le_sup ((set.finite.mem_to_finset hD).mpr hd))),
end

lemma multipliable_of_one_add {ι : Type*} (f : ι → mv_power_series σ α) (hf : strongly_summable f) :
  multipliable (λ i, (1 + f i)) := 
by classical; exact hf.has_prod_of_one_add.multipliable

variable [_root_.t2_space α]

lemma tprod_eq_of_one_add {ι : Type*} {f : ι → mv_power_series σ α} (hf : strongly_summable f) :
  tprod (λ i, (1 + f i)) = tsum (partial_product f)  := 
begin
  haveI : _root_.t2_space (mv_power_series σ α) := t2_space σ α,
  rw [hf.has_prod_of_one_add.tprod_eq, strongly_multipliable.prod_eq, sum_eq_tsum]
end

end strongly_summable

-- TODO : treat the case of arbitrary topologies on α 
/- 
  but the statement is incorrect because `tsum F` has already used
  the given topology of `α`. 
  Except for this problem, this runs roughly as follows:

  let h := @has_prod_of_one_add σ α _ (default) ι _ f hf,
  
  have := @has_prod.tprod_eq (mv_power_series σ α) ι _
    (@mv_power_series.topological_space σ α default)
    (@mv_power_series.t2_space σ α default (@discrete_topology.to_t2_space α default (discrete_topology_bot α))),

  exact this h,

-/

end strongly_multipliable

end mv_power_series