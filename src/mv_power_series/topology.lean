import ring_theory.power_series.basic
import mv_power_series.order
import topology.algebra.infinite_sum.basic
import topology.algebra.ring.basic
import topology.uniform_space.basic
import topology.uniform_space.pi
import topology.uniform_space.separation
import data.set.finite


section topology

open_locale pointwise

variables {α : Type*} {ι : Type*}

lemma finite_support_of_tendsto_zero [add_comm_monoid α] 
  [topological_space α] [discrete_topology α] 
  {f : ι → α}
  (hf : filter.tendsto f filter.cofinite (nhds 0)) : f.support.finite :=
begin
  classical,
  simp only [nhds_discrete, filter.tendsto_pure] at hf,
  obtain ⟨s, H, p⟩ := filter.eventually.exists_mem hf, 
  simp only [filter.mem_cofinite] at H,
  apply set.finite.subset H,
  intros x hx,
  simp only [set.mem_compl_iff],
  by_contradiction hxs, 
  exact hx (p x hxs),
end

lemma finite_support_of_summable [add_comm_group α] [topological_space α] [discrete_topology α] [topological_add_group α] (f : ι → α) 
  (hf : summable f) : f.support.finite :=
finite_support_of_tendsto_zero hf.tendsto_cofinite_zero

lemma tendsto_zero_of_summable [add_comm_group α] [topological_space α] [topological_add_group α] 
  (f : ι → α) (hf : summable f) :
  filter.tendsto f filter.cofinite (nhds 0) :=
begin
  classical,
  obtain ⟨a, ha⟩ := hf, 
  simp [_root_.has_sum] at ha,
  rw [tendsto_at_top_nhds] at ha,
  simp only [tendsto_nhds],
  intros U₀ hU₀ memU₀,
  suffices : ∃ (U₁ : set α), is_open U₁ ∧ (0 : α) ∈ U₁ ∧ U₁ - U₁ ≤ U₀, 
  obtain ⟨U₁, hU₁, memU₁, addU₁_subset⟩ := this,
  specialize ha ((λ x, x - a) ⁻¹' U₁) _ _ ,
  simp only [memU₁, set.mem_preimage, sub_self],
  exact is_open.preimage (continuous_sub_right a) hU₁,
  obtain ⟨S, hS⟩ := ha,
  simp only [filter.mem_cofinite],
  apply set.finite.subset S.finite_to_set,
  intros i hi,
  simp only [set.mem_compl_iff, set.mem_preimage] at hi,
  by_contradiction his, apply hi,
  have hS' := hS (insert i S) (finset.subset_insert i S), 
  specialize hS S (le_rfl),
  apply addU₁_subset,
  use (insert i S).sum f - a, 
  use S.sum f - a, 
  split, simpa only [set.mem_preimage] using hS',
  split, simpa only [set.mem_preimage] using hS,
  simp only [finset.sum_insert his, sub_sub_sub_cancel_right, add_sub_cancel],

  suffices : is_open ((λ (xy : α × α), xy.fst - xy.snd) ⁻¹' U₀),
  rw is_open_prod_iff at this,
  specialize this 0 0 (by simp only [set.mem_preimage, sub_self, memU₀]), 
  obtain ⟨u, v, hu, hv, mem_u, mem_v, H⟩ := this,
  use (u ∩ v),
  split, exact is_open.inter hu hv,
  split, exact ⟨mem_u, mem_v⟩,
  rw ← set.image_subset_iff at H,
  apply subset_trans _ H,
  simp only [set.image_prod, set.image2_sub],
  rintros z ⟨x, y, hx, hy, rfl⟩,
  exact ⟨x, y, set.mem_of_mem_inter_left hx, set.mem_of_mem_inter_right hy, rfl⟩,

  exact is_open.preimage continuous_sub hU₀,
end

end topology


namespace mv_power_series

variables (σ : Type*)
variables (α : Type*) 


section topological

variable [topological_space α] 

/-- The pointwise topology on mv_power_series -/
instance : topological_space (mv_power_series σ α) := 
Pi.topological_space 

/-- Components are continuous -/
lemma continuous_component :
  ∀  (d : σ →₀ ℕ), continuous (λ a : mv_power_series σ α, a d) :=
continuous_pi_iff.mp continuous_id

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


/-- mv_power_series form a t2-space -/
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



section strongly_summable

variables {ι : Type*}
variables {σ α}

section semiring 

variable [semiring α]

def strongly_summable (f : ι → mv_power_series σ α) : Prop :=
  ∀ (d : σ →₀ ℕ), (λ i, coeff α d (f i)).support.finite 

namespace strongly_summable 

lemma support_add [decidable_eq ι] {f g : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (hg : strongly_summable g):
  ∀ (d : σ →₀ ℕ), (λ i, coeff α d ((f + g) i)).support ⊆ ((hf d).to_finset ∪ (hg d).to_finset : finset ι) := 
begin
  intros d i,
  simp only [pi.add_apply, map_add, function.mem_support, ne.def, finset.coe_union, set.finite.coe_to_finset, set.mem_union],
  intro h,
  by_cases h₁ : coeff α d (f i) = 0,
  right, simpa [h₁] using h,
  left, exact h₁,
end

lemma add {f g : ι → mv_power_series σ α} (hf : strongly_summable f) (hg : strongly_summable g):
  strongly_summable (f + g) :=
begin
  classical,
  intro d,
  apply set.finite.subset _ (support_add hf hg d),
  apply finset.finite_to_set,
end

lemma smul {f : ι → mv_power_series σ α} (a : ι → α) 
  (hf : strongly_summable f) : strongly_summable (a • f) := 
begin
  intro d,
  apply set.finite.subset (hf d),
  intro i, 
  simp only [pi.smul_apply', pi.smul_apply, function.mem_support, ne.def],
  intros h h', apply h, rw [coeff_smul, h', mul_zero],
end

lemma support_mul [decidable_eq ι] {f : ι → mv_power_series σ α} 
  {κ : Type*} [decidable_eq κ] {g : κ → mv_power_series σ α} 
  (hf : strongly_summable f) (hg : strongly_summable g) :
  ∀ (d : σ →₀ ℕ), (λ (i : ι × κ), coeff α d ((f i.fst) * (g i.snd))).support 
    ⊆ finset.product (finset.bUnion d.antidiagonal (λ b, (hf b.fst).to_finset))
      (finset.bUnion d.antidiagonal (λ b, (hg b.snd).to_finset)) := 
begin
  intro d, 
  dsimp only,
  rintro ⟨i, j⟩,
  intro h,
  simp only [function.mem_support, coeff_mul] at h,
  suffices : ∃ p ∈ d.antidiagonal,  
    (coeff α (p.fst : σ →₀ ℕ) (f i)) * ((coeff α p.snd) (g j)) ≠ 0,
  obtain ⟨⟨b,c⟩, hbc, h'⟩ := this,
  simp only [finsupp.mem_antidiagonal] at hbc,
  simp only [finset.coe_product, finset.coe_bUnion, finset.mem_coe, 
    finsupp.mem_antidiagonal, set.finite.coe_to_finset, set.prod_mk_mem_set_prod_eq, 
    set.mem_Union, function.mem_support, ne.def, exists_prop, prod.exists],
  split,
  use b, use c, apply and.intro hbc, intro h₁, apply h', rw h₁, rw zero_mul,
  use b, use c, apply and.intro hbc, intro h₂, apply h', rw h₂, rw mul_zero,
  
  by_contradiction h', push_neg at h',
  exact h (finset.sum_eq_zero h'),
end

lemma mul {f : ι → mv_power_series σ α} {κ : Type*} {g : κ → mv_power_series σ α}
  (hf : strongly_summable f) (hg : strongly_summable g) :
  strongly_summable (λ (i : ι × κ), (f i.fst) * (g i.snd)) := 
begin
  classical,
  intro d, 
  apply set.finite.subset _ (support_mul hf hg d),
  apply finset.finite_to_set,
end

noncomputable 
def sum {f : ι → mv_power_series σ α} (hf : strongly_summable f) : mv_power_series σ α :=
 λ d, (hf d).to_finset.sum (λ i, coeff α d (f i)) 

lemma coeff_sum.def {f : ι → mv_power_series σ α} {hf : strongly_summable f} (d : σ →₀ ℕ) : 
  coeff α d (hf.sum) = (hf d).to_finset.sum (λ i, coeff α d (f i)) :=  rfl

lemma coeff_sum {f : ι → mv_power_series σ α} {hf : strongly_summable f} (d : σ →₀ ℕ) 
  (s : finset ι) (hs : (λ i, coeff α d (f i)).support ⊆ s) : 
  coeff α d (hf.sum) = s.sum (λ i, coeff α d (f i)) := 
begin
  simp only [coeff_sum.def],
  rw finset.sum_subset (set.finite.to_finset_subset.mpr hs),
  { intros i hi hi', 
    simpa only [set.finite.mem_to_finset, function.mem_support, not_not] using hi', },
end

lemma sum_add {f g : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (hg : strongly_summable g) : 
  ∀ (hh : strongly_summable (f + g)),
  hh.sum = hf.sum + hg.sum :=
begin
  classical,
  intro hh,
  ext d, 
  simp only [coeff_sum, pi.add_apply, map_add],
  rw coeff_sum d _ (support_add hf hg d), 
  rw coeff_sum d, 
  rw coeff_sum d, 
  simp only [pi.add_apply, map_add, finset.union_assoc],
  rw finset.sum_add_distrib,
  all_goals { simp only [finset.coe_union, set.finite.coe_to_finset,
      set.subset_union_right, set.subset_union_left], },
end

lemma sum_mul {f : ι → mv_power_series σ α} 
  {κ : Type*} {g : κ → mv_power_series σ α}
  (hf : strongly_summable f) (hg : strongly_summable g) :
  ∀ (hh : strongly_summable (λ (i : ι × κ), (f i.fst) * (g i.snd))),
  hh.sum = hf.sum * hg.sum := 
begin
  classical,
  intro hh,
  ext d,
  rw coeff_sum d _ (support_mul hf hg d),
  simp_rw coeff_mul,
  rw finset.sum_comm,
  apply finset.sum_congr rfl,
  intros bc hbc,
  rw coeff_sum bc.fst, rw coeff_sum bc.snd, 
  rw finset.sum_mul_sum,
  all_goals { 
    simp only [finset.coe_bUnion, set.finite.coe_to_finset, finset.mem_coe],
    exact @set.subset_bUnion_of_mem _ _ _ _ bc hbc, },
end

lemma has_sum_coeff [topological_space α] {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (d : σ →₀ ℕ) : 
  _root_.has_sum (λ i, coeff α d (f i)) (coeff α d hf.sum) := 
begin
  apply has_sum_sum_of_ne_finset_zero, 
  intros b hb, 
  simp only [set.finite.mem_to_finset, function.mem_support, not_not] at hb,
  exact hb,
end

lemma summable_coeff [topological_space α] {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (d : σ →₀ ℕ) : summable (λ i, coeff α d (f i)) :=
⟨coeff α d hf.sum, hf.has_sum_coeff d⟩

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
  haveI := mv_power_series.t2_space σ α, 
  simp only [tsum, dif_pos hf.summable],
  exact has_sum.unique (hf.has_sum_coeff d) 
    (has_sum.map (classical.some_spec hf.summable) _ (continuous_component σ α d)),
end

end strongly_summable

end semiring

section ring 


namespace strongly_summable 


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
  (strongly_summable f) → (_root_.summable f) := strongly_summable.summable 

-- TODO (?): replace topological_ring instance by topological_add_group…
example [topological_space α] [_root_.topological_ring α] {f : ι → mv_power_series σ α} :
  (_root_.summable f) → filter.tendsto f filter.cofinite (nhds 0) := 
begin
  haveI := topological_ring σ α,
  exact tendsto_zero_of_summable f ,
end

lemma iff_summable [topological_space α] [discrete_topology α] 
  {f : ι → mv_power_series σ α} : (strongly_summable f) ↔ (_root_.summable f) :=
⟨summable, 
  λ hf d, finite_support_of_summable _ (hf.map _ (continuous_component σ α d))⟩

lemma iff_summable' [topological_space α] [discrete_topology α] 
  {f : ι → mv_power_series σ α} : (strongly_summable f) ↔ filter.tendsto f 
    filter.cofinite (nhds 0):=
begin
  haveI := topological_ring σ α,
  split,
  intro hf, exact hf.summable.tendsto_cofinite_zero, 

  simp only [strongly_summable, nhds_pi, filter.tendsto_pi],
  apply forall_imp,
  intro d,
  exact finite_support_of_tendsto_zero, 
end

end strongly_summable

end ring

end strongly_summable

section summable

variables [semiring α] [topological_space α]

variables {σ α}

/-- A power series is the sum (in the sense of summable families) of its monomials -/
lemma has_sum_of_monomials_self (f : mv_power_series σ α): has_sum (λ (d : σ →₀ ℕ),
  monomial α d (coeff α d f)) f := 
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

/- /-- If the coefficient space is T2, then a power series is the unique sum of its monomials -/
lemma has_unique_sum [t2_space α] (f g : mv_power_series σ α) : 
  has_sum (λ (d : σ →₀ ℕ), monomial α d (coeff α d f)) g 
  ↔ f = g := 
begin
  haveI : t2_space (mv_power_series σ α) := t2_space σ α,
  split,
  { intro h,
    exact has_sum.unique (has_sum f) h, },
  intro h, rw ← h, exact has_sum f, 
end -/

/-- If the coefficient space is T2, then the power series is `tsum` of its monomials -/
lemma as_tsum [_root_.t2_space α] (f : mv_power_series σ α) :
  f = tsum (λ (d : σ →₀ ℕ), monomial α d (coeff α d f)) := 
begin
  classical,
  haveI := mv_power_series.t2_space σ α, 
  simp only [tsum, dif_pos f.has_sum_of_monomials_self.summable],
  exact has_sum.unique f.has_sum_of_monomials_self (classical.some_spec _),
end

example {ι : Type*} (f : ι → mv_power_series σ α) :
  summable f ↔ ∀ d, summable (λ i, f i d) := pi.summable

example {ι : Type*} (f : ι → mv_power_series σ α) (a : mv_power_series σ α) (ha : ∀ (d : σ →₀ ℕ), has_sum (λ (i : ι), f i d) (a d)) : has_sum (λ (i : ι), f i) a := pi.has_sum.mpr ha


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

section strongly_summable


variables [semiring α]

variables {σ α}

lemma homogeneous_components_self_strongly_summable (w : σ → ℕ) (f : mv_power_series σ α) :
  strongly_summable (λ p, homogeneous_component w p f) := 
begin
  intro d,
  apply set.finite.subset (finset.finite_to_set {weight w d}),
  intro p,
  simp only [function.mem_support, ne.def, finset.mem_coe, coeff_homogeneous_component],
  rw finset.mem_singleton,
  simp only [ite_eq_right_iff, not_forall, exists_prop, and_imp],
  intros h h', exact h.symm,
end

lemma as_sum_of_homogeneous_components (w : σ → ℕ) (f : mv_power_series σ α) :
  ∀ (hf : strongly_summable (λ p, homogeneous_component w p f)), f = hf.sum := 
begin
  intro hf,
  ext d,
  simp only [strongly_summable.sum],
  simp only [coeff_apply, coeff_homogeneous_component],
  rw finset.sum_eq_single (weight w d),
  simp only [eq_self_iff_true, if_true],
  { intros b h h', rw if_neg (ne.symm h'), },
  { simp only [set.finite.mem_to_finset, function.mem_support, not_not, imp_self], }
end

end strongly_summable

section summable

variables [semiring α] 

variables {σ α}

-- Bourbaki, *Algèbre*, chap. 4, §4, page IV.25, exemple c)
/-- A family of power series is strongly summable if their weighted orders tend to infinity. -/
lemma strongly_summable_of_order_tendsto_at_top {ι : Type*} 
  (w : σ → ℕ) (f : ι → mv_power_series σ α) 
  (hf : filter.tendsto (λ i, weighted_order w (f i)) filter.cofinite filter.at_top) :
  strongly_summable f := 
begin
  intro d,
  rw ← compl_compl (function.support _),
  rw ← filter.mem_cofinite,
  rw filter.tendsto_def at hf, 
  specialize hf (set.Ici (weight w d).succ) (filter.Ici_mem_at_top _),
  apply filter.mem_of_superset hf, 
  intro i,
  simp only [set.mem_preimage, set.mem_Ici, set.mem_compl_iff, function.mem_support, not_not],
  intro h,
  apply coeff_of_lt_weighted_order w,
  apply lt_of_lt_of_le _ h,
  rw part_enat.coe_lt_coe,
  exact lt_add_one ((weight w) d),
end


variable  [topological_space α]

/-- A family of power series is summable if their weighted orders tend to infinity. -/
lemma summable_of_order_tendsto_at_top {ι : Type*} 
  (w : σ → ℕ) (f : ι → mv_power_series σ α) 
  (hf : filter.tendsto (λ i, weighted_order w (f i)) filter.cofinite filter.at_top) :
  summable f := (strongly_summable_of_order_tendsto_at_top w f hf).summable 

end summable

end mv_power_series