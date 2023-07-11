import ring_theory.power_series.basic
import mv_power_series.topology

-- import mv_power_series.order
-- -- import topology.algebra.infinite_sum.basic
-- import ..infinite_sum.basic
-- import topology.algebra.ring.basic
-- import topology.uniform_space.basic
-- import topology.uniform_space.pi
-- import topology.uniform_space.separation
-- import topology.order.basic
-- import data.set.finite

-- import ..antidiagonal

namespace function

open_locale pointwise

variables {α : Type*} {ι : Type*}

/-- If a function `f` to an additive commutative monoid with the discrete topology tends to zero
along the cofinite filter, then `f` has finite support. -/
lemma finite_support_of_tendsto_zero [add_comm_monoid α] [topological_space α] [discrete_topology α] 
  {f : ι → α} (hf : filter.tendsto f filter.cofinite (nhds 0)) : f.support.finite :=
begin
  simp only [nhds_discrete, filter.tendsto_pure] at hf,
  obtain ⟨s, H, p⟩ := filter.eventually.exists_mem hf, 
  simp only [filter.mem_cofinite] at H,
  apply set.finite.subset H,
  intros x hx,
  rw [set.mem_compl_iff],
  by_contradiction hxs, 
  exact hx (p x hxs),
end

/-- If a function `f` to a discrete topological commutative additive group is summable, then it has
finite support. -/
lemma finite_support_of_summable [add_comm_group α] [topological_space α] [discrete_topology α] 
  [topological_add_group α] {f : ι → α} (hf : summable f) : f.support.finite :=
finite_support_of_tendsto_zero hf.tendsto_cofinite_zero

/-- If a function `f` to a topological commutative additive group is summable, then it tends to zero
along the cofinite filter. -/
lemma tendsto_zero_of_summable [add_comm_group α] [topological_space α] [topological_add_group α] 
  {f : ι → α} (hf : summable f) : filter.tendsto f filter.cofinite (nhds 0) :=
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

end function


namespace mv_power_series

open function

variables (σ : Type*) (α : Type*) 

section strongly_summable

variables {ι : Type*}
variables {σ α}

section semiring 

variable [semiring α]

def strongly_summable (f : ι → mv_power_series σ α) : Prop :=
  ∀ (d : σ →₀ ℕ), (λ i, coeff α d (f i)).support.finite 

namespace strongly_summable 

lemma congr {f g: ι → mv_power_series σ α} (h : f = g) :
  strongly_summable f ↔ strongly_summable g := by rw [h]

section order

instance enat.topology := preorder.topology ℕ∞

-- Bourbaki, *Algèbre*, chap. 4, §4, page IV.25, exemple c)
/-- A family of power series is strongly summable if their weighted orders tend to infinity. -/
lemma of_weighted_order_tendsto_top (w : σ → ℕ) (f : ι → mv_power_series σ α) 
  (hf : filter.tendsto (λ i, weighted_order w (f i)) filter.cofinite (nhds ⊤)) :
  strongly_summable f := 
begin
  intro d,
  rw filter.has_basis.tendsto_right_iff nhds_top_basis at hf,
  specialize hf ((weight w d) : ℕ∞) (with_top.coe_lt_top _),
  dsimp at hf,
  refine set.finite.subset hf _,
  intro i,
  simp only [mem_support, ne.def, set.mem_set_of_eq],
  intros h' h, apply h',
  apply coeff_of_lt_weighted_order w,  exact h,
  exact ⟨rfl⟩,
  apply_instance,
end

lemma of_order_tendsto_top (f : ι → mv_power_series σ α) 
  (hf : filter.tendsto (λ i, order (f i)) filter.cofinite (nhds ⊤)) :
  strongly_summable f := of_weighted_order_tendsto_top _ f hf

-- Réciproques quand σ est fini !
/-- When σ is finite, a family of power series is strongly summable 
iff their weighted orders tend to infinity. -/
lemma weighted_order_tendsto_top_iff [hσ: finite σ] {ι : Type*} 
  (w : σ → ℕ) (hw : ∀ x, w x ≠ 0) (f : ι → mv_power_series σ α) :
  strongly_summable f ↔ 
  filter.tendsto (λ i, weighted_order w (f i)) filter.cofinite (nhds ⊤) :=
begin
  classical,
  split,
  { intro hf,
    rw filter.has_basis.tendsto_right_iff nhds_top_basis,
    intros n hn,
    induction n,
    exfalso, exact lt_irrefl ⊤ hn,
    simp only [set.mem_Ioi, filter.eventually_cofinite, not_lt],
    let s := { d : σ →₀ ℕ | ↑(weight w d) ≤ n},
    
    suffices : { i | (f i).weighted_order w ≤ some n} ⊆ ⋃ (d : σ →₀ ℕ) (H : d ∈ s), { i | coeff α d (f i) ≠ 0},
    refine set.finite.subset _ this,
    refine set.finite.bUnion (finite_of_weight_le w hw n) _,

    intros d hd, exact hf d,

    intros i hi,
    simp only [set.mem_set_of_eq] at hi,
    simp only [set.mem_set_of_eq, nat.cast_id, ne.def, set.mem_Union, exists_prop],
    obtain ⟨d, hd⟩ := exists_coeff_ne_zero_of_weighted_order w (f i) _, 
    use d,
    apply and.intro _ hd.2,
    simpa [← hd.1, with_top.some_eq_coe, nat.cast_le ] using hi,

    simp only [enat.coe_to_nat_eq_self], 
    intro hi', rw [hi', top_le_iff] at hi,
    exact with_top.coe_ne_top hi,

    exact ⟨rfl⟩,
    apply_instance, },
  exact of_weighted_order_tendsto_top w f,
end

/-- When σ is finite, a family of power series is strongly summable 
iff their orders tend to infinity. -/
lemma order_tendsto_top_iff [hσ: finite σ] 
  (f : ι → mv_power_series σ α) :
  strongly_summable f ↔ 
  filter.tendsto (λ i, order (f i)) filter.cofinite (nhds ⊤) :=
weighted_order_tendsto_top_iff _ (by simp) f

end order 

noncomputable def union_of_support_of_coeff_le [decidable_eq ι] 
  {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (d : σ →₀ ℕ) : finset ι :=
  finset.bUnion (finset.Iic d) (λ e, (hf e).to_finset) 

lemma not_mem_union_of_support_of_coeff_le_iff [decidable_eq ι] 
  {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (d : σ →₀ ℕ) (i : ι) : 
  i ∉ hf.union_of_support_of_coeff_le d ↔ 
  ∀ e (he : e ≤ d), coeff α e (f i) = 0 := 
by simp only [union_of_support_of_coeff_le, finset.mem_bUnion, finset.mem_Iic, 
  set.finite.mem_to_finset, mem_support, not_exists, not_not]

-- TODO : now that the proof is two lines long, is the statement necessary?
lemma union_of_coeff_support_finite {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (d : σ →₀ ℕ) : 
  (⋃ e (H : e ≤ d), (λ i, coeff α e (f i)).support).finite := 
begin
  refine set.finite.bUnion _ (λ d H, hf d),
  convert (set.Iic d).to_finite,
end

lemma of_subset_union_of_coeff_support_finite [decidable_eq ι] 
  {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (d : σ →₀ ℕ) : 
  { I : finset ι | I ⊆ hf.union_of_support_of_coeff_le d }.finite := 
begin
  suffices : {I : finset ι | I ⊆ hf.union_of_support_of_coeff_le d}
    = (hf.union_of_support_of_coeff_le d).powerset, 
  rw this,
  apply finset.finite_to_set,
  ext I,
  simp only [set.mem_set_of_eq, finset.coe_powerset, set.mem_preimage, 
    set.mem_powerset_iff, finset.coe_subset],
end

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

lemma sum_congr {f g : ι → mv_power_series σ α} {hf : strongly_summable f}
  {hg : strongly_summable g} (h : f = g) : hf.sum = hg.sum :=
begin
  ext d,
  simp only [coeff_sum.def],  
  apply finset.sum_congr,
  ext i, simp only [set.finite.mem_to_finset, mem_support, ne.def, h], 
  intros i hi, rw h,
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

lemma of_indicator {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (s : set ι) :
  strongly_summable (λ i, s.indicator f i) := 
begin
  intro d,
  apply set.finite.subset (hf d),
  intro i,
  simp only [mem_support, ne.def, not_imp_not],
  intro hi,
  cases s.indicator_eq_zero_or_self f i; simp only [h, hi, map_zero],
end

lemma add_compl {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (s : set ι) :
  hf.sum = (hf.of_indicator s).sum + (hf.of_indicator sᶜ).sum := 
begin
  have hf' : strongly_summable (s.indicator f + sᶜ.indicator f),
  { rw  s.indicator_self_add_compl f, exact hf, },
  rw ← sum_add (hf.of_indicator s) (hf.of_indicator sᶜ) hf', 
  exact sum_congr (s.indicator_self_add_compl f).symm,
end

lemma on_subtype {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (s : set ι) :
  strongly_summable (f ∘ coe : ↥s → mv_power_series σ α) := 
begin
  intro d,
  apply set.finite.of_finite_image _ (set.inj_on_of_injective subtype.coe_injective _),
  apply set.finite.subset (hf d),
  intro i,
  rintro ⟨j, hj, rfl⟩,
  simp only [comp_app, mem_support, ne.def] at hj,
  simp only [mem_support, ne.def],
  exact hj,
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
  exact tendsto_zero_of_summable,
end

lemma iff_summable [topological_space α] [discrete_topology α] 
  {f : ι → mv_power_series σ α} : (strongly_summable f) ↔ (_root_.summable f) :=
⟨summable, 
  λ hf d, finite_support_of_summable (hf.map _ (continuous_component σ α d))⟩

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

instance enat.topology := preorder.topology ℕ∞

variable  [topological_space α]

/-- A family of power series is summable if their weighted orders tend to infinity. -/
lemma summable_of_weighted_order_tendsto_top {ι : Type*} 
  (w : σ → ℕ) (f : ι → mv_power_series σ α) 
  (hf : filter.tendsto (λ i, weighted_order w (f i)) filter.cofinite (nhds ⊤)) :
  summable f := (strongly_summable.of_weighted_order_tendsto_top w f hf).summable 

lemma summable_of_order_tendsto_top {ι : Type*} 
  (f : ι → mv_power_series σ α) 
  (hf : filter.tendsto (λ i, order (f i)) filter.cofinite (nhds ⊤)) :
  summable f :=
(strongly_summable.of_order_tendsto_top f hf).summable

end summable

section strongly_multipliable

variables {ι : Type*} 

variable (f : ι → mv_power_series σ α)

variables [comm_ring α] 

variables {σ α}

noncomputable def partial_product : 
  finset ι → mv_power_series σ α := λ I, I.prod (λ i, f i)

/-- The family f is strongly multipliable if the family F on { I : set ι | I.finite} defined by… is strongly_summable -/
def strongly_multipliable : Prop := strongly_summable (partial_product f)

variable {f}
/-- The product of the family of (1 + f ι), when it is strongly_multipliable  -/
noncomputable def strongly_multipliable.prod (hf : strongly_multipliable f) : mv_power_series σ α := hf.sum 

lemma strongly_multipliable.prod_eq (hf : strongly_multipliable f) : 
  hf.prod = hf.sum := rfl
-- variable [decidable_eq σ]

lemma strongly_summable.support_partial_product_le [decidable_eq ι] (hf : strongly_summable f) 
  (d : σ →₀ ℕ) : support (λ I, coeff α d (partial_product f I))
  ⊆ (hf.union_of_support_of_coeff_le d).powerset := 
begin
  intro I,
  simp only [mem_support, ne.def, finset.coe_powerset, set.mem_preimage, set.mem_powerset_iff, finset.coe_subset, not_imp_comm],
  rw finset.not_subset,
  rintro ⟨i, hi, h⟩,
  rw strongly_summable.not_mem_union_of_support_of_coeff_le_iff at h,
  simp only [partial_product, finset.prod_eq_mul_prod_diff_singleton hi, coeff_mul],
  apply finset.sum_eq_zero,
  rintros ⟨x, y⟩,
  rw finsupp.mem_antidiagonal, 
  dsimp,
  intro hxy,
  rw [h x _, zero_mul],
  simp only [←hxy, finsupp.le_def, finsupp.coe_add, pi.add_apply, le_self_add],
end

lemma strongly_summable.to_strongly_multipliable [decidable_eq ι] (hf : strongly_summable f) :
  strongly_multipliable f :=
begin
  intro d,
  refine set.finite.subset _ (hf.support_partial_product_le d),
  apply finset.finite_to_set,
end

lemma strongly_multipliable.finset_prod_eq [decidable_eq ι] 
  (s : finset ι) (hf : strongly_multipliable f) : 
  s.prod (λ i, 1 + f i) = (hf.of_indicator {I : finset ι | I ⊆ s}).sum :=
begin
  rw finset.prod_one_add,
  ext d,
  rw map_sum,
  rw strongly_summable.coeff_sum d s.powerset,
  apply finset.sum_congr rfl,
  intros t ht,
  apply congr_arg,
  simp only [set.indicator],
  rw if_pos, refl,
  dsimp, simpa only [finset.mem_powerset] using ht,
  intro t,
  simp only [mem_support, ne.def, finset.mem_coe, finset.mem_powerset],
  rw not_imp_comm,
  intro ht', 
  rw [set.indicator, if_neg, map_zero], 
  exact ht',
end

lemma strongly_multipliable.prod_eq_sum_add_sum [decidable_eq ι] (hf : strongly_multipliable f)
  (s : set ι) : 
  hf.prod = (hf.of_indicator {I : finset ι | ↑I ⊆ s}).sum + (hf.of_indicator {I : finset ι | (↑I ⊆ s)}ᶜ).sum := by rw [hf.prod_eq, ← hf.add_compl]

lemma strongly_multipliable.prod_eq_finset_prod_add [decidable_eq ι] 
  (hf : strongly_multipliable f) (s : finset ι) : 
  hf.prod = s.prod (λ i, 1 + f i) + (hf.of_indicator {I : finset ι | (I ⊆ s)}ᶜ).sum := 
begin
  rw [hf.prod_eq_sum_add_sum s, hf.finset_prod_eq s],
  refl,
end


/- example [decidable_eq ι] (s : finset ι) (I : finset ι): decidable (I ⊆ s) := 
begin
exact finset.decidable_dforall_finset,
end

noncomputable lemma _root_.set.finite.decidable_mem [decidable_eq ι] (a : ι) (s : set ι) (hs : s.finite) :
  decidable (a ∈ s) := 
begin
  suffices : a ∈ hs.to_finset ↔ a ∈ s,
  apply decidable_of_iff _ this,
  simp only [set.finite.mem_to_finset],
end

noncomputable lemma _root_.set.decidable_dforall_finite
  [decidable_eq ι] {s : set ι} (hs : s.finite) 
  {I : set ι} (hI : I.finite): 
  decidable (I ⊆ s) := 
begin
  suffices : hI.to_finset ⊆ hs.to_finset ↔ I ⊆ s,
  apply decidable_of_iff _ this,
  simp only [set.finite.subset_to_finset, set.finite.coe_to_finset], 
end
  -/


lemma strongly_summable.finset.prod_of_one_add_eq [decidable_eq ι] (hf : strongly_summable f) (d : σ →₀ ℕ) (J : finset ι) (hJ : hf.union_of_support_of_coeff_le d ⊆ J) : (coeff α d) (J.prod (λi, 1 + f i)) = (coeff α d) hf.to_strongly_multipliable.prod :=
begin
--  suffices : ∃ I : finset ι, ∀ i, i ∉ I → ∀ e ≤ d, coeff α e (f i) = 0,
--  obtain ⟨I, hI⟩ := this,
--  use I,
--  intros J hIJ,

  rw hf.to_strongly_multipliable.prod_eq_finset_prod_add J,
  simp only [map_add, self_eq_add_right],
  rw strongly_summable.coeff_sum.def,
  apply finset.sum_eq_zero,
  intros t ht,
  simp only [set.indicator],
  split_ifs,
  simp only [set.mem_compl_iff, set.mem_set_of_eq, finset.not_subset] at h,
  obtain ⟨i, hit, hiJ⟩ := h,
  simp only [partial_product, finset.prod_eq_mul_prod_diff_singleton hit, coeff_mul],
  apply finset.sum_eq_zero,
  rintros ⟨x, y⟩,
  rw finsupp.mem_antidiagonal, 
  dsimp,
  intro hxy,
  rw (hf.not_mem_union_of_support_of_coeff_le_iff d i).mp 
    -- i ∉ hf.union_of_support_of_coeff_le d
    (show i ∉ _, by exact λ hi, hiJ (hJ hi)) 
    x _,
  rw zero_mul,
  simp only [← hxy, finsupp.le_def, finsupp.coe_add, pi.add_apply, le_self_add],
  rw map_zero,
end


section 

variables [_root_.uniform_space α] [_root_.uniform_add_group α] 
[_root_.t2_space α]

lemma strongly_summable.has_prod_of_one_add [decidable_eq ι] (hf : strongly_summable f) :
  has_prod (λ i, 1 + f i) hf.to_strongly_multipliable.prod := 
begin
  haveI := uniform_add_group σ α,
  -- obtain ⟨a, ha⟩ := (of_strongly_summable f hf).summable,
  intros V hV,
  simp only [filter.mem_map, filter.mem_at_top_sets, ge_iff_le, 
    finset.le_eq_subset, set.mem_preimage],
  let V₀ := (has_add.add (hf.to_strongly_multipliable.prod)) ⁻¹' V,
  have hV'₀ : V = (has_add.add (- hf.to_strongly_multipliable.prod)) ⁻¹' V₀,
  { simp only [V₀, ← set.preimage_comp, comp_add_left, add_right_neg], 
    convert set.preimage_id,
    ext x, rw zero_add, },
  have hV₀ : V₀ ∈ nhds(0 : mv_power_series σ α),
  { simp only [V₀], 
    apply continuous_at_def.mp, 
    apply continuous.continuous_at,
    apply continuous_add_left _,
    apply_instance,
    rw add_zero,  exact hV, },
  simp only [nhds_pi, filter.mem_pi] at hV₀,
  obtain ⟨D, hD, t, ht, htV₀⟩ := hV₀,

  use hf.union_of_support_of_coeff_le (hD.to_finset.sup id),
  
  intros J hIJ,
  simp only [hV'₀], -- set.mem_preimage],
  rw set.mem_preimage,
  apply htV₀,
  simp only [set.mem_pi, pi.add_apply, pi.neg_apply],
  intros d hd,

  convert mem_of_mem_nhds (ht d),
  simp only [pi.zero_apply, neg_eq_zero],
  rw [neg_add_eq_sub, sub_eq_zero],

  convert strongly_summable.finset.prod_of_one_add_eq hf d J _, 

  intros i hi,
  apply hIJ,
  revert hi,
  contrapose,
  simp only [strongly_summable.not_mem_union_of_support_of_coeff_le_iff],
  intros h e hed,
  apply h,
  apply le_trans hed, 
  convert finset.le_sup _, 
  exact (id.def d).symm,
  simp only [set.finite.mem_to_finset], 
  exact hd,
end

lemma multipliable_of_one_add {ι : Type*} [decidable_eq ι] (f : ι → mv_power_series σ α) (hf : strongly_summable f) : 
  multipliable (λ i, (1 + f i))  := 
hf.has_prod_of_one_add.multipliable

lemma tprod_eq_of_one_add [_root_.t2_space α] {ι : Type*} [decidable_eq ι] (f : ι → mv_power_series σ α) (hf : strongly_summable f) : 
  tprod (λ i, (1 + f i)) = tsum (partial_product f)  := 
begin
  haveI : _root_.t2_space (mv_power_series σ α) := t2_space σ α,
  rw hf.has_prod_of_one_add.tprod_eq,
  rw strongly_multipliable.prod_eq, 
  rw mv_power_series.strongly_summable.sum_eq_tsum,
end

end 

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