import ring_theory.power_series.basic
import mv_power_series.order 
import infinite_sum.basic
import topology.order.basic

open finset filter set

instance enat.topology := preorder.topology ℕ∞

instance : order_topology ℕ∞ := ⟨rfl⟩

namespace function

open_locale pointwise

variables {α : Type*} {ι : Type*}

/-- If a function `f` to an additive commutative monoid with the discrete topology tends to zero
along the cofinite filter, then `f` has finite support. -/
lemma finite_support_of_tendsto_zero [add_comm_monoid α] [topological_space α]
  [discrete_topology α] {f : ι → α} (hf : tendsto f cofinite (nhds 0)) :
  f.support.finite :=
begin
  rw [nhds_discrete, tendsto_pure] at hf,
  obtain ⟨s, H, p⟩ := eventually.exists_mem hf, 
  apply finite.subset H,
  intros x hx,
  rw [mem_compl_iff],
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
  {f : ι → α} (hf : summable f) : tendsto f cofinite (nhds 0) :=
begin
  classical,
  obtain ⟨a, ha⟩ := hf, 
  rw [has_sum, tendsto_at_top_nhds] at ha,
  rw [tendsto_nhds],
  intros U₀ hU₀ memU₀,
  suffices hU₁ : ∃ (U₁ : set α), is_open U₁ ∧ (0 : α) ∈ U₁ ∧ U₁ - U₁ ≤ U₀, 
  { obtain ⟨U₁, hU₁, memU₁, addU₁_subset⟩ := hU₁,
    obtain ⟨S, hS⟩ := ha ((λ x, x - a) ⁻¹' U₁) (by simp only [memU₁, set.mem_preimage, sub_self])
      (is_open.preimage (continuous_sub_right a) hU₁),
    apply (S.finite_to_set).subset,
    intros i hi,
    by_contradiction his,
    apply hi,
    apply addU₁_subset,
    use [(insert i S).sum f - a, S.sum f - a, hS (insert i S) (subset_insert i S), hS S (le_rfl)],
    rw [sum_insert his, sub_sub_sub_cancel_right, add_sub_cancel] },
  { suffices h_open : is_open ((λ (xy : α × α), xy.fst - xy.snd) ⁻¹' U₀),
    { rw is_open_prod_iff at h_open,
      obtain ⟨u, v, hu, hv, mem_u, mem_v, H⟩ :=
      h_open 0 0 (by simp only [set.mem_preimage, sub_self, memU₀]),
      use [u ∩ v, is_open.inter hu hv, ⟨mem_u, mem_v⟩],
      apply subset_trans _ (set.image_subset_iff.mpr H),
      rw [image_prod, image2_sub],
      rintros z ⟨x, y, hx, hy, rfl⟩,
      exact ⟨x, y, mem_of_mem_inter_left hx, mem_of_mem_inter_right hy, rfl⟩ },
    { exact is_open.preimage continuous_sub hU₀ }}
end

end function

namespace mv_power_series

open function

variables {σ α : Type*} 

section strongly_summable

variables {ι : Type*}

section semiring 

variable [semiring α]

/-- A family of power series is `strongly summable` if for every finitely supported function
`(d : σ →₀ ℕ)`, the function `λ i, coeff α d (f i)` is finitely supported. -/
def strongly_summable (f : ι → mv_power_series σ α) : Prop :=
  ∀ (d : σ →₀ ℕ), (λ i, coeff α d (f i)).support.finite 

namespace strongly_summable 

lemma congr {f g: ι → mv_power_series σ α} (h : f = g) :
  strongly_summable f ↔ strongly_summable g := by rw [h]

section order

-- Bourbaki, *Algèbre*, chap. 4, §4, page IV.25, exemple c)
/-- A family of power series is strongly summable if their weighted orders tend to infinity. -/
lemma of_weighted_order_tendsto_top (w : σ → ℕ) (f : ι → mv_power_series σ α) 
  (hf : tendsto (λ i, weighted_order w (f i)) cofinite (nhds ⊤)) :
  strongly_summable f := 
begin
  intro d,
  rw has_basis.tendsto_right_iff nhds_top_basis at hf,
  specialize hf ((weight w d) : ℕ∞) (with_top.coe_lt_top _),
  refine hf.subset _,
  intro i,
  simp only [mem_support, ne.def, mem_set_of_eq],
  intros h' h,
  apply h',
  exact coeff_of_lt_weighted_order w _ h,
  { apply_instance },
  { apply_instance },
end

lemma of_order_tendsto_top (f : ι → mv_power_series σ α) 
  (hf : tendsto (λ i, order (f i)) cofinite (nhds ⊤)) : strongly_summable f :=
of_weighted_order_tendsto_top _ f hf

-- Réciproques quand σ est fini !
/-- When σ is finite, a family of power series is strongly summable 
iff their weighted orders tend to infinity. -/
lemma weighted_order_tendsto_top_iff [finite σ] {ι : Type*} {w : σ → ℕ} (hw : ∀ x, w x ≠ 0) 
  (f : ι → mv_power_series σ α) : 
  strongly_summable f ↔ tendsto (λ i, weighted_order w (f i)) cofinite (nhds ⊤) :=
begin
  refine ⟨λ hf, _, of_weighted_order_tendsto_top w f⟩,
  { rw has_basis.tendsto_right_iff nhds_top_basis,
    intros n hn,
    induction n,
    { exfalso, exact lt_irrefl ⊤ hn },
    { simp only [set.mem_Ioi, eventually_cofinite, not_lt],
      let s := {d : σ →₀ ℕ | ↑(weight w d) ≤ n},
      suffices h_ss: { i | (f i).weighted_order w ≤ some n} ⊆ 
        ⋃ (d : σ →₀ ℕ) (H : d ∈ s), { i | coeff α d (f i) ≠ 0},
      { exact ((finite_of_weight_le w hw n).bUnion (λd hd, hf d)).subset h_ss },
      { intros i hi,
        simp only [mem_set_of_eq, nat.cast_id, ne.def, mem_Union, exists_prop],
        obtain ⟨d, hd⟩ := exists_coeff_ne_zero_of_weighted_order w (f i) _,
        refine ⟨d, _, hd.2⟩,
        simpa [← hd.1, with_top.some_eq_coe, nat.cast_le ] using hi,
        rw [enat.coe_to_nat_eq_self], 
        { intro hi',
          rw [mem_set_of_eq, hi', top_le_iff] at hi,
          exact with_top.coe_ne_top hi }}},
    { apply_instance },
    { apply_instance }}
end

/-- When σ is finite, a family of power series is strongly summable 
iff their orders tend to infinity. -/
lemma order_tendsto_top_iff [finite σ] (f : ι → mv_power_series σ α) :
  strongly_summable f ↔ tendsto (λ i, order (f i)) cofinite (nhds ⊤) :=
weighted_order_tendsto_top_iff (by simp) f

end order 

/-- The union of the supports of the functions `λ i, coeff α e (f i)`, where `e` runs over
the coefficients bounded by `d`. -/
noncomputable def union_of_support_of_coeff_le [decidable_eq ι] {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (d : σ →₀ ℕ) : finset ι :=
finset.bUnion (Iic d) (λ e, (hf e).to_finset) 

lemma not_mem_union_of_support_of_coeff_le_iff [decidable_eq ι] {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (d : σ →₀ ℕ) (i : ι) : 
  i ∉ hf.union_of_support_of_coeff_le d ↔ ∀ e (he : e ≤ d), coeff α e (f i) = 0 := 
by simp only [union_of_support_of_coeff_le, finset.mem_bUnion, finset.mem_Iic, 
  finite.mem_to_finset, mem_support, not_exists, not_not]

/- lemma union_of_coeff_support_finite {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (d : σ →₀ ℕ) : 
  (⋃ e (H : e ≤ d), (λ i, coeff α e (f i)).support).finite := 
(set.Iic d).to_finite.bUnion (λ d H, hf d) -/

lemma of_subset_union_of_coeff_support_finite [decidable_eq ι] {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (d : σ →₀ ℕ) : 
  {I : finset ι | I ⊆ hf.union_of_support_of_coeff_le d}.finite := 
begin
  suffices : {I : finset ι | I ⊆ hf.union_of_support_of_coeff_le d}
    = (hf.union_of_support_of_coeff_le d).powerset, 
  { rw this, apply finite_to_set },
  ext I,
  simp only [mem_set_of_eq, coe_powerset, set.mem_preimage, mem_powerset_iff, coe_subset],
end

lemma support_add [decidable_eq ι] {f g : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (hg : strongly_summable g) :
  ∀ (d : σ →₀ ℕ), (λ i, coeff α d ((f + g) i)).support ⊆
  ((hf d).to_finset ∪ (hg d).to_finset : finset ι) := 
begin
  intros d i,
  simp only [pi.add_apply, map_add, function.mem_support, ne.def, coe_union, 
    finite.coe_to_finset, set.mem_union],
  intro h,
  by_cases h₁ : coeff α d (f i) = 0,
  { right, simpa [h₁] using h },
  { left, exact h₁ },
end

lemma add {f g : ι → mv_power_series σ α} (hf : strongly_summable f) (hg : strongly_summable g):
  strongly_summable (f + g) :=
by classical; exact λ d, finite.subset (finite_to_set _) (support_add hf hg d)

lemma smul {f : ι → mv_power_series σ α} (a : ι → α) (hf : strongly_summable f) :
  strongly_summable (a • f) := 
begin
  intro d,
  apply finite.subset (hf d),
  intro i, 
  simp only [pi.smul_apply', pi.smul_apply, function.mem_support, ne.def],
  intros h h',
  apply h,
  rw [coeff_smul, h', mul_zero],
end

lemma support_mul [decidable_eq ι] {f : ι → mv_power_series σ α} {κ : Type*} [decidable_eq κ]
  {g : κ → mv_power_series σ α} (hf : strongly_summable f) (hg : strongly_summable g) :
  ∀ (d : σ →₀ ℕ), (λ (i : ι × κ), coeff α d ((f i.fst) * (g i.snd))).support ⊆
    (d.antidiagonal.bUnion (λ b, (hf b.fst).to_finset)).product 
      (d.antidiagonal.bUnion (λ b, (hg b.snd).to_finset)) := 
begin
  rintro d ⟨i, j⟩ h,
  dsimp only [function.mem_support, coeff_mul] at h,
  suffices : ∃ p ∈ d.antidiagonal,  
    (coeff α (p.fst : σ →₀ ℕ) (f i)) * ((coeff α p.snd) (g j)) ≠ 0,
  { obtain ⟨⟨b,c⟩, hbc, h'⟩ := this,
    rw [finsupp.mem_antidiagonal] at hbc,
    simp only [coe_product, coe_bUnion, mem_coe, 
      finsupp.mem_antidiagonal, finite.coe_to_finset, prod_mk_mem_set_prod_eq, 
      mem_Union, function.mem_support, ne.def, exists_prop, prod.exists],
    split,
    use b, use c, apply and.intro hbc, intro h₁, apply h', rw h₁, rw zero_mul,
    use b, use c, apply and.intro hbc, intro h₂, apply h', rw h₂, rw mul_zero },
  { by_contra' h',
    exact h (sum_eq_zero h') },
end

lemma mul {f : ι → mv_power_series σ α} {κ : Type*} {g : κ → mv_power_series σ α}
  (hf : strongly_summable f) (hg : strongly_summable g) :
  strongly_summable (λ (i : ι × κ), (f i.fst) * (g i.snd)) := 
by classical; exact λ d, finite.subset (finite_to_set _) (support_mul hf hg d)

/-- The sum of a strongly summable family of power series. -/
noncomputable def sum {f : ι → mv_power_series σ α} (hf : strongly_summable f) : 
  mv_power_series σ α :=
λ d, (hf d).to_finset.sum (λ i, coeff α d (f i)) 

lemma coeff_sum.def {f : ι → mv_power_series σ α} {hf : strongly_summable f} (d : σ →₀ ℕ) : 
  coeff α d (hf.sum) = (hf d).to_finset.sum (λ i, coeff α d (f i)) := rfl

lemma coeff_sum {f : ι → mv_power_series σ α} {hf : strongly_summable f} (d : σ →₀ ℕ) 
  (s : finset ι) (hs : (λ i, coeff α d (f i)).support ⊆ s) : 
  coeff α d (hf.sum) = s.sum (λ i, coeff α d (f i)) := 
begin
  rw [coeff_sum.def, sum_subset (finite.to_finset_subset.mpr hs)],
  intros i hi hi', 
  simpa only [finite.mem_to_finset, function.mem_support, not_not] using hi',
end

lemma sum_congr {f g : ι → mv_power_series σ α} {hf : strongly_summable f}
  {hg : strongly_summable g} (h : f = g) : hf.sum = hg.sum :=
begin
  ext d,
  rw [coeff_sum.def],  
  refine sum_congr _ (λ i hi, by rw h),
  ext i,
  simp only [finite.mem_to_finset, mem_support, ne.def, h], 
end

lemma sum_add {f g : ι → mv_power_series σ α} (hf : strongly_summable f)
  (hg : strongly_summable g) (hh : strongly_summable (f + g)) :
  hh.sum = hf.sum + hg.sum :=
begin
  classical,
  ext d, 
  simp only [coeff_sum, pi.add_apply, map_add],
  rw [coeff_sum d _ (support_add hf hg d), coeff_sum d, coeff_sum d], 
  simp only [pi.add_apply, map_add, finset.union_assoc],
  rw sum_add_distrib,
  all_goals { simp only [coe_union, finite.coe_to_finset, set.subset_union_right, 
    set.subset_union_left], },
end

lemma sum_mul {f : ι → mv_power_series σ α} {κ : Type*} {g : κ → mv_power_series σ α}
  (hf : strongly_summable f) (hg : strongly_summable g)
  (hh : strongly_summable (λ (i : ι × κ), (f i.fst) * (g i.snd))) :
  hh.sum = hf.sum * hg.sum := 
begin
  classical,
  ext d,
  simp_rw [coeff_sum d _ (support_mul hf hg d), coeff_mul],
  rw sum_comm,
  apply finset.sum_congr rfl,
  intros bc hbc,
  rw [coeff_sum bc.fst, coeff_sum bc.snd, sum_mul_sum],
  all_goals { simp only [coe_bUnion, finite.coe_to_finset, mem_coe],
    exact @set.subset_bUnion_of_mem _ _ _ _ bc hbc },
end

lemma of_indicator {f : ι → mv_power_series σ α} (hf : strongly_summable f) (s : set ι) :
  strongly_summable (λ i, s.indicator f i) := 
begin
  intro d,
  apply (hf d).subset,
  intro i,
  simp only [mem_support, ne.def, not_imp_not],
  intro hi,
  cases s.indicator_eq_zero_or_self f i;
  simp only [h, hi, map_zero],
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

lemma on_subtype {f : ι → mv_power_series σ α} (hf : strongly_summable f) (s : set ι) :
  strongly_summable (f ∘ coe : ↥s → mv_power_series σ α) := 
begin
  intro d,
  apply finite.of_finite_image _ (inj_on_of_injective subtype.coe_injective _),
  apply (hf d).subset,
  rintro i ⟨j, hj, rfl⟩,
  simp only [comp_app, mem_support, ne.def] at hj ⊢,
  exact hj,
end

lemma has_sum_coeff [topological_space α] {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (d : σ →₀ ℕ) : 
  _root_.has_sum (λ i, coeff α d (f i)) (coeff α d hf.sum) := 
begin
  apply has_sum_sum_of_ne_finset_zero, 
  intros b hb, 
  rw [finite.mem_to_finset, function.mem_support, not_not] at hb,
  exact hb,
end

lemma summable_coeff [topological_space α] {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (d : σ →₀ ℕ) : summable (λ i, coeff α d (f i)) :=
⟨coeff α d hf.sum, hf.has_sum_coeff d⟩

end strongly_summable

lemma homogeneous_components_self_strongly_summable (w : σ → ℕ) (f : mv_power_series σ α) :
  strongly_summable (λ p, homogeneous_component w p f) := 
begin
  intro d,
  apply (finite_to_set {weight w d}).subset,
  intro p,
  rw [function.mem_support, ne.def, mem_coe, coeff_homogeneous_component, finset.mem_singleton,
    ite_eq_right_iff, not_forall, exists_prop, and_imp],
  intros h h',
  exact h.symm,
end

lemma as_sum_of_homogeneous_components (w : σ → ℕ) (f : mv_power_series σ α) :
  ∀ (hf : strongly_summable (λ p, homogeneous_component w p f)), f = hf.sum := 
begin
  intro hf,
  ext d,
  simp only [strongly_summable.sum, coeff_apply, coeff_homogeneous_component],
  rw sum_eq_single (weight w d),
  { simp only [eq_self_iff_true, if_true] },
  { intros b h h', rw if_neg (ne.symm h') },
  { simp only [finite.mem_to_finset, function.mem_support, not_not, imp_self] }
end

end semiring

end strongly_summable


section strongly_multipliable

variables [comm_ring α] {ι : Type*} (f : ι → mv_power_series σ α) 

/-- The map sending `(I : finset ι)` to the finite product `I.prod (λ i, f i)`. -/
noncomputable def partial_product : finset ι → mv_power_series σ α := λ I, I.prod (λ i, f i)

/- TODO : give a more general (and easier) definition 
 A family `f` is strongly multipliable if for each `d`,
 the coefficients `coeff α d (s.prod f)` of the finite products are eventually constant 
 and rewrite the case of sums in the same spirit
 But beware of subfamilies when `∃ i, f i = 0` -/

/-- The family f is strongly multipliable if the family F on { I : set ι | I.finite} 
  defined by… is strongly_summable -/
def strongly_multipliable : Prop := strongly_summable (partial_product f)

variable {f}

/-- The product of the family of (1 + f ι), when it is strongly_multipliable  -/
noncomputable def strongly_multipliable.prod (hf : strongly_multipliable f) :
  mv_power_series σ α := hf.sum 

lemma strongly_multipliable.prod_eq (hf : strongly_multipliable f) : hf.prod = hf.sum := rfl

lemma strongly_summable.support_partial_product_le [decidable_eq ι] (hf : strongly_summable f) 
  (d : σ →₀ ℕ) : 
  support (λ I, coeff α d (partial_product f I)) ⊆ (hf.union_of_support_of_coeff_le d).powerset := 
begin
  intro I,
  simp only [mem_support, ne.def, coe_powerset, set.mem_preimage, set.mem_powerset_iff, 
    coe_subset, not_imp_comm, finset.not_subset],
  rintro ⟨i, hi, h⟩,
  rw strongly_summable.not_mem_union_of_support_of_coeff_le_iff at h,
  simp only [partial_product, prod_eq_mul_prod_diff_singleton hi, coeff_mul],
  apply sum_eq_zero,
  rintros ⟨x, y⟩,
  rw finsupp.mem_antidiagonal, 
  intro hxy,
  rw [h x _, zero_mul],
  simp only [←hxy, finsupp.le_def, finsupp.coe_add, pi.add_apply, le_self_add],
end

lemma strongly_summable.to_strongly_multipliable (hf : strongly_summable f) :
  strongly_multipliable f :=
by classical; exact λ d, finite.subset (finite_to_set _) (hf.support_partial_product_le d)

--TODO: move
lemma finset.prod_one_add' {ι α: Type*} [comm_ring α] {f : ι → α} (s : finset ι) :
  s.prod (λ i, 1 + f i) = s.powerset.sum (λ t, t.prod f) := 
begin
  simp_rw [add_comm, prod_add],
  apply congr_arg,
  ext t,
  convert mul_one _,
  exact prod_eq_one (λi hi, rfl),
end

lemma strongly_multipliable.finset_prod_eq (s : finset ι) (hf : strongly_multipliable f) : 
  s.prod (λ i, 1 + f i) = (hf.of_indicator {I : finset ι | I ⊆ s}).sum :=
begin
  rw finset.prod_one_add',
  ext d,
  rw [map_sum, strongly_summable.coeff_sum d s.powerset],
  { apply sum_congr rfl,
    intros t ht,
    apply congr_arg,
    rw [indicator, if_pos], refl,
    { exact finset.mem_powerset.mp ht }},
  { intro t,
    rw [mem_support, ne.def, mem_coe, finset.mem_powerset, not_imp_comm],
    intro ht', 
    rw [indicator, if_neg, map_zero], 
    exact ht' },
end

lemma strongly_multipliable.prod_eq_sum_add_sum (hf : strongly_multipliable f) (s : set ι) : 
  hf.prod = (hf.of_indicator {I : finset ι | ↑I ⊆ s}).sum + 
    (hf.of_indicator {I : finset ι | (↑I ⊆ s)}ᶜ).sum :=
by rw [hf.prod_eq, ← hf.add_compl]

lemma strongly_multipliable.prod_eq_finset_prod_add (hf : strongly_multipliable f) (s : finset ι) : 
  hf.prod = s.prod (λ i, 1 + f i) + (hf.of_indicator {I : finset ι | (I ⊆ s)}ᶜ).sum := 
by rw [hf.prod_eq_sum_add_sum s, hf.finset_prod_eq s]; refl

lemma strongly_summable.finset.prod_of_one_add_eq [decidable_eq ι] (hf : strongly_summable f)
  (d : σ →₀ ℕ) (J : finset ι) (hJ : hf.union_of_support_of_coeff_le d ⊆ J) :
  (coeff α d) (J.prod (λi, 1 + f i)) = (coeff α d) hf.to_strongly_multipliable.prod :=
begin
  rw [hf.to_strongly_multipliable.prod_eq_finset_prod_add J, map_add, self_eq_add_right, 
    strongly_summable.coeff_sum.def],
  apply sum_eq_zero,
  intros t ht,
  rw indicator,
  split_ifs with h,
  { rw [mem_compl_iff, mem_set_of_eq, finset.not_subset] at h,
    obtain ⟨i, hit, hiJ⟩ := h,
    simp only [partial_product, prod_eq_mul_prod_diff_singleton hit, coeff_mul],
    apply sum_eq_zero,
    rintros ⟨x, y⟩,
    rw finsupp.mem_antidiagonal, 
    intro hxy,
    rw [(hf.not_mem_union_of_support_of_coeff_le_iff d i).mp  (λ hi, hiJ (hJ hi)) x _, zero_mul],
    simp only [← hxy, finsupp.le_def, finsupp.coe_add, pi.add_apply, le_self_add] },
  { rw map_zero },
end

end strongly_multipliable

end mv_power_series