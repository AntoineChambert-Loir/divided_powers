/- ACL and MIdFF, Lean 2022 meeting at Icerm -/
import divided_powers.basic
import basic_lemmas

namespace divided_powers

/-- The structure of a sub-pd-ideal of a pd-ideal -/
structure is_sub_pd_ideal {A : Type*} [comm_ring A] {I : ideal A} (hI : divided_powers I)
  (J : ideal A) : Prop :=
(is_sub_ideal : J ≤ I)
(dpow_mem_ideal : ∀ (n : ℕ) (hn : n ≠ 0) (j ∈ J), hI.dpow n j ∈ J )

section is_sub_pd_ideal

variables {A : Type*} [comm_ring A] {I : ideal A} (hI : divided_powers I)

/-- The ideal J ⊓ I is a sub-pd-ideal of I, 
    if and only if (on I) the divided powers have some compatiblity mod J 
    (The necessity was proved as a sanity check.) -/
lemma is_sub_pd_ideal_inf_iff (J : ideal A) :
  (is_sub_pd_ideal hI (J ⊓ I)) ↔ (∀ (n : ℕ) (a b : A) (ha : a ∈ I) (hb : b ∈ I) (hab : (a - b) ∈ J),
    hI.dpow n a - hI.dpow n b ∈ J) := 
begin
  refine ⟨λ hIJ n a b ha hb hab, _, λ hIJ, _⟩,
  { have hab' : a - b ∈ I := I.sub_mem ha hb,  
    rw [← add_sub_cancel'_right b a, hI.dpow_add n hb hab', finset.range_succ, 
      finset.sum_insert (finset.not_mem_range_self), tsub_self, hI.dpow_zero hab', mul_one,
      add_sub_cancel'], 
    apply ideal.sum_mem,
    intros i hi, 
    apply semilattice_inf.inf_le_left J I,
    exact (J ⊓ I).smul_mem _ (hIJ.dpow_mem_ideal (n - i) 
      (ne_of_gt (nat.sub_pos_of_lt (finset.mem_range.mp hi))) _ ⟨hab, hab'⟩) },
  { refine ⟨semilattice_inf.inf_le_right J I, λ n hn a ha,  ⟨_, hI.dpow_mem hn ha.right⟩⟩,
    rw [← sub_zero (hI.dpow n a), ← hI.dpow_eval_zero hn], 
    exact hIJ n a 0 ha.right (I.zero_mem) (J.sub_mem ha.left J.zero_mem) },
end

/-- Lemma 3.6 of [BO] (Antoine) -/
lemma span_is_sub_pd_ideal_iff (S : set A) (hS : S ⊆ I) :
  is_sub_pd_ideal hI (ideal.span S) ↔ 
  ∀ (n : ℕ) (hn : n ≠ 0) (s ∈ S), hI.dpow n s ∈ ideal.span S := 
begin 
  split,
  { -- trivial direction
    intros hhI h hn s hs, 
    apply hhI.dpow_mem_ideal h hn s (ideal.subset_span hs), },
  { -- interesting direction,
    intro hhI,
    have hSI := ideal.span_le.mpr hS,
    apply is_sub_pd_ideal.mk (hSI),
    intros n hn z hz, revert n,
    refine submodule.span_induction' _ _ _ _ hz, 
    { -- case of elements of S 
      intros s hs n hn, exact hhI n hn s hs, },
    { -- case of 0 
      intros n hn, rw hI.dpow_eval_zero hn, apply ideal.zero_mem _, },
    { -- case of sum
      rintros x hxI y hyI hx hy n hn,
      rw hI.dpow_add n (hSI hxI) (hSI hyI),
      apply submodule.sum_mem (ideal.span S),
      intros m hm,
      by_cases hm0 : m = 0,
      { rw hm0,
        refine ideal.mul_mem_left (ideal.span S) _ (hy n hn), },
      { refine ideal.mul_mem_right _ (ideal.span S) (hx m hm0), } },
    { -- case : product,
      intros a x hxI hx n hn,
      simp only [algebra.id.smul_eq_mul],
      rw hI.dpow_smul n (hSI hxI),
      exact ideal.mul_mem_left (ideal.span S) (a ^ n) (hx n hn), }, },
end

lemma generated_dpow_is_sub_ideal {S : set A} (hS : S ⊆ I) :
  ideal.span { y : A | ∃ (n : ℕ) (hn : n ≠ 0) (x : A) (hx : x ∈ S), y = hI.dpow n x } ≤ I :=
begin
  rw ideal.span_le,
  rintros y ⟨n, hn, x, hx, hxy⟩,
  rw hxy,
  exact hI.dpow_mem hn (hS hx)
end

end is_sub_pd_ideal

/-- A `sub-pd-ideal` of `I` is a sub-ideal `J` of `I` such that for all `n ∈ ℕ ≥ 0` and all
  `j ∈ J`, `hI.dpow n j ∈ J`. -/
@[ext] structure sub_pd_ideal {A : Type*} [comm_ring A] {I : ideal A} (hI : divided_powers I) :=
(carrier : ideal A)
(is_sub_ideal : carrier ≤ I)
(dpow_mem_ideal : ∀ (n : ℕ) (hn : n ≠ 0) (j ∈ carrier), hI.dpow n j ∈ carrier)

namespace sub_pd_ideal

variables {A : Type*} [comm_ring A] {I : ideal A} (hI : divided_powers I)

def mk' (J : ideal A) (hJ : is_sub_pd_ideal hI J) : sub_pd_ideal hI :=
{ carrier := J,
  is_sub_ideal := hJ.1,
  dpow_mem_ideal := hJ.2 }

instance : set_like (sub_pd_ideal hI) A :=
{ coe := λ s, s.carrier,
  coe_injective' := λ p q h, by rw [set_like.coe_set_eq] at h; cases p; cases q; congr'  }

@[simp]
lemma mem_carrier {s : sub_pd_ideal hI} {x : A} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

/-- I is a sub-pd-ideal ot itself. -/
instance : has_top (sub_pd_ideal hI) :=
⟨{ carrier       := I,
  is_sub_ideal   := le_refl _,
  dpow_mem_ideal := λ n hn x hx, hI.dpow_mem hn hx }⟩

lemma top_carrier_def : (⊤ : hI.sub_pd_ideal).carrier = I := rfl 

instance : inhabited hI.sub_pd_ideal := ⟨⊤⟩

/-- (0) is a sub-pd-ideal ot the pd-ideal I. -/
instance : has_bot (sub_pd_ideal hI) :=
⟨{ carrier       := ⊥,
  is_sub_ideal   := bot_le,
  dpow_mem_ideal := λ n hn x hx, 
  by rw [ideal.mem_bot.mp hx, hI.dpow_eval_zero hn, ideal.mem_bot]}⟩

/-- If there is a pd-structure on I(A/J) such that the quotient map is 
   a pd-morphism, then J ⊓ I is a sub-pd-ideal of I -/
def inter_quot (J : ideal A) (hJ : divided_powers (I.map (ideal.quotient.mk J)))
  (φ : pd_morphism hI hJ) (hφ:  φ.to_ring_hom = ideal.quotient.mk J) : 
  sub_pd_ideal hI := 
{ carrier        := J ⊓ I,
  is_sub_ideal   := set.inter_subset_right J I, 
  dpow_mem_ideal := λ n hn a ⟨haJ, haI⟩,
  begin
    refine ⟨_, hI.dpow_mem hn haI⟩,
    rw [set_like.mem_coe,← ideal.quotient.eq_zero_iff_mem, ← hφ, ← φ.dpow_comp n a haI], 
    suffices ha0 : (φ.to_ring_hom) a = 0,
    { rw ha0,
      exact hJ.dpow_eval_zero hn },
    rw [hφ, ideal.quotient.eq_zero_iff_mem], 
    exact haJ, 
  end }

/-- If J is an ideal of A, then J ⬝ I is a sub-pd-ideal of I. (Berthelot, 1.6.1 (i)) -/
def prod (J : ideal A) : sub_pd_ideal hI  :=
{ carrier        := I • J,
  is_sub_ideal   := ideal.mul_le_right,
  dpow_mem_ideal := λ n hn x hx,
  begin
    revert n,
    apply submodule.smul_induction_on' hx,
    { -- mul 
      intros a ha b hb n hn,
      rw [algebra.id.smul_eq_mul, mul_comm a b, hI.dpow_smul n ha, mul_comm], 
      exact submodule.mul_mem_mul (hI.dpow_mem hn ha)
        (J.pow_mem_of_mem hb n (zero_lt_iff.mpr hn)) },
    { -- add 
      intros x hx y hy hx' hy' n hn, 
      rw hI.dpow_add n (ideal.mul_le_right hx) (ideal.mul_le_right hy),
      apply submodule.sum_mem (I • J),
      intros k hk,
      by_cases hk0 : k = 0,
      { rw hk0, apply ideal.mul_mem_left (I • J), exact hy' _ hn, },
      { apply ideal.mul_mem_right _ (I • J), exact hx' k hk0, }, }
  end }

/- TODO : 
* prove uniqueness
* add rfl lemma that gives analogue of dpow_quot_eq for the divided_powers 
that was just defined 
* maybe other… 
-/

--Section 1.8 of [B]
/- The intersection of two sub-PD ideals is a sub-PD ideal. -/
instance : has_inf (sub_pd_ideal hI) := ⟨λ J J',
{ carrier := J.carrier ⊓ J'.carrier,
  is_sub_ideal := λ x hx, J.is_sub_ideal hx.1,
  dpow_mem_ideal :=  λ n hn x hx, ⟨J.dpow_mem_ideal n hn x hx.1, J'.dpow_mem_ideal n hn x hx.2⟩ }⟩

lemma inf_carrier_def (J J' : sub_pd_ideal hI) :
  (J ⊓ J').carrier = J.carrier ⊓ J'.carrier := rfl

instance : has_Inf (sub_pd_ideal hI) := ⟨λ S,
{ carrier := ⨅ s ∈ (has_insert.insert ⊤ S), (s : hI.sub_pd_ideal).carrier, 
  is_sub_ideal := λ x hx,
  begin
    simp only [ideal.mem_infi] at hx,
    exact hx ⊤ (set.mem_insert ⊤ S),
  end,
  dpow_mem_ideal := λ n hn x hx,
  begin
    simp only [ideal.mem_infi] at hx ⊢,
    intros s hs,
    refine (s : hI.sub_pd_ideal).dpow_mem_ideal n hn x (hx s hs),
  end }⟩

lemma Inf_carrier_def (S : set (sub_pd_ideal hI)) :
  (Inf S).carrier = ⨅ s ∈ (has_insert.insert ⊤ S), (s : hI.sub_pd_ideal).carrier := rfl

/-- The sub-pd-ideal of I generated by a family of elements of A. -/
def generated (S : set A) : sub_pd_ideal hI := 
Inf { J : sub_pd_ideal hI | S ⊆ J.carrier }

/-- The sub-pd-ideal of I generated by the family `hI.dpow n x`, where `n ∈ ℕ ≥ 0` and `x ∈ S`. -/
def generated_dpow {S : set A} (hS : S ⊆ I) :
  sub_pd_ideal hI := 
{ carrier := ideal.span { y : A | ∃ (n : ℕ) (hn : n ≠ 0) (x : A) (hx : x ∈ S), y = hI.dpow n x },
  is_sub_ideal := generated_dpow_is_sub_ideal hI hS,
  dpow_mem_ideal := λ n hn z hz, 
  begin
    have hSI := generated_dpow_is_sub_ideal hI hS,
    revert n,
    refine submodule.span_induction' _ _ _ _ hz,
    { -- Elements of S
      rintros y ⟨m, hm, x, hxS, hxy⟩ n hn,
      rw [hxy, hI.dpow_comp n hm (hS hxS)],
      exact ideal.mul_mem_left _ _ (ideal.subset_span ⟨n*m, mul_ne_zero hn hm, x, hxS, rfl⟩) },
    { -- Zero
      intros n hn,
      rw hI.dpow_eval_zero hn, exact ideal.zero_mem _ },
    { intros x hx y hy hx_pow hy_pow n hn,
      rw hI.dpow_add n (hSI hx) (hSI hy),
      apply submodule.sum_mem (ideal.span _),
      intros m hm,
      by_cases hm0 : m = 0,
      { rw hm0, exact ideal.mul_mem_left (ideal.span _) _ (hy_pow n hn), },
      { exact ideal.mul_mem_right _ (ideal.span _) (hx_pow m hm0), }, },
    { intros a x hx hx_pow n hn,
      rw [smul_eq_mul, hI.dpow_smul n (hSI hx)],
      exact ideal.mul_mem_left (ideal.span _) (a ^ n) (hx_pow n hn) }
  end }

lemma generated_dpow_carrier {S : set A} (hS : S ⊆ I) :
  (generated_dpow hI hS).carrier = 
  ideal.span { y : A | ∃ (n : ℕ) (hn : n ≠ 0) (x : A) (hx : x ∈ S), y = hI.dpow n x } := rfl

lemma le_generated_dpow {S : set A} (hS : S ⊆ I) :
  S ⊆ (generated_dpow hI hS).carrier :=
λ x hx, ideal.subset_span ⟨1, one_ne_zero, x, hx, by rw hI.dpow_one (hS hx)⟩

lemma generated_dpow_le (S : set A) (J : sub_pd_ideal hI) 
  (hSJ : S ⊆ J.carrier) :
  ideal.span { y : A | ∃ (n : ℕ) (hn : n ≠ 0) (x : A) (hx : x ∈ S), y = hI.dpow n x } ≤ J.carrier :=
begin
  rw ideal.span_le,
  rintros y ⟨n, hn, x, hx, hxy⟩,
  rw hxy,
  exact J.dpow_mem_ideal n hn x (hSJ hx),
end

lemma generated_carrier_eq {S : set A} (hS : S ⊆ I) :
  (generated hI S).carrier =
    ideal.span { y : A | ∃ (n : ℕ) (hn : n ≠ 0) (x : A) (hx : x ∈ S), y = hI.dpow n x } := 
begin
  simp only [generated, Inf_carrier_def],
  apply le_antisymm,
  { have h : generated_dpow hI hS ∈ insert ⊤ {J : hI.sub_pd_ideal | S ⊆ ↑(J.carrier)},
  { apply set.mem_insert_of_mem,
    simp only [set.mem_set_of_eq, generated_dpow_carrier],
    exact le_generated_dpow hI hS },
    refine Inf_le_of_le ⟨generated_dpow hI hS, _⟩ (le_refl _),
    simp only [h, cinfi_pos],
    refl },
  { rw le_infi₂_iff,
    rintros J hJ,
    refine generated_dpow_le hI S J _,
    cases set.mem_insert_iff.mp hJ with hJI hJS,
    { rw hJI, exact hS },
    { exact hJS }}
end

section complete_lattice

instance : has_coe (sub_pd_ideal hI) (ideal A) := ⟨λ J, J.carrier⟩

instance : has_le (sub_pd_ideal hI) := ⟨λ J J', J.carrier ≤ J'.carrier⟩

lemma le_iff {J J' : sub_pd_ideal hI} : J ≤ J' ↔ J.carrier ≤ J'.carrier := iff.rfl

instance : has_lt (sub_pd_ideal hI) := ⟨λ J J', J.carrier < J'.carrier⟩

lemma lt_iff {J J' : sub_pd_ideal hI} : J < J' ↔ J.carrier < J'.carrier := iff.rfl

instance : has_sup (sub_pd_ideal hI) := 
⟨λ J J', sub_pd_ideal.mk' hI ((J : ideal A) ⊔ J')  $ begin
  have hJJ' : (J : ideal A) ⊔ (J' : ideal A) = ideal.span(J ∪ J'),
  { simp only [ideal.span_union, coe_coe, ideal.span_eq] },
  rw [hJJ', span_is_sub_pd_ideal_iff hI (J ∪ J') (set.union_subset J.is_sub_ideal J'.is_sub_ideal)],
  rintros n hn x (hx | hx),
  { exact ideal.subset_span (set.mem_union_left _ (J.dpow_mem_ideal n hn x hx)) },
  { exact ideal.subset_span (set.mem_union_right _ (J'.dpow_mem_ideal n hn x hx)) }
end⟩

lemma coe_def (J : sub_pd_ideal hI) : (J : ideal A) = J.carrier := rfl

lemma sup_carrier_def (J J' : sub_pd_ideal hI) : (J ⊔ J').carrier = J ⊔ J' := rfl

lemma submodule.supr_eq_span' {R M : Type*} [semiring R] [add_comm_monoid M] [module R M] {ι : Sort*} 
(p : ι → submodule R M) (h : ι → Prop) : 
  (⨆ (i : ι) (hi : h i), p i) = submodule.span R (⋃ (i : ι) (hi : h i), ↑(p i)) :=
by simp_rw [← submodule.supr_span, submodule.span_eq]

instance : has_Sup (sub_pd_ideal hI) := 
⟨λ S, sub_pd_ideal.mk' hI (Sup ((coe : sub_pd_ideal hI → ideal A) '' S)) $ begin
   have h : (⋃ (i : ideal A) (hi : i ∈ coe '' S), ↑i) ⊆ (I : set A),
  { rintros a ⟨-, ⟨J, rfl⟩, haJ⟩,
    rw [set.mem_Union, set_like.mem_coe, exists_prop] at haJ,
    obtain ⟨J', hJ'⟩ := (set.mem_image _ _ _).mp haJ.1,
    rw [← hJ'.2, coe_def] at haJ,
    exact J'.is_sub_ideal haJ.2, },
  rw [Sup_eq_supr, submodule.supr_eq_span', ideal.submodule_span_eq, 
    span_is_sub_pd_ideal_iff hI _ h],
  { rintros n hn x ⟨T, hT, hTx⟩,
    obtain ⟨J, hJ⟩ := hT,
    rw ← hJ at hTx,
    obtain ⟨J', ⟨⟨hJ', rfl⟩, h'⟩⟩ := hTx,
    apply ideal.subset_span,
    apply set.mem_bUnion hJ',
    obtain ⟨K, hKS, rfl⟩ := hJ',
    exact K.dpow_mem_ideal n hn x h', },
end⟩

lemma Sup_carrier_def (S : set (sub_pd_ideal hI)) :
  (Sup S).carrier = Sup ((coe : sub_pd_ideal hI → ideal A) '' S) := rfl

def subtype.galois_coinsertion : galois_coinsertion (λ J : {J : ideal A // J ≤ I}, (J : ideal A))
  (λ J : ideal A, ⟨J ⊓ I, by exact inf_le_right⟩) :=
galois_coinsertion.monotone_intro (λ J J' h, subtype.mk_le_mk.mpr (inf_le_inf_right I h))
  (λ J J' h, h) (λ J, inf_le_left)
  (λ ⟨J, hJ⟩, by simp only [subtype.coe_mk]; exact inf_eq_left.mpr hJ) 

instance : has_coe (sub_pd_ideal hI) {J : ideal A // J ≤ I} :=  ⟨λ J, ⟨J.carrier, J.is_sub_ideal⟩⟩

instance : complete_lattice {J : ideal A // J ≤ I} := 
galois_coinsertion.lift_complete_lattice (subtype.galois_coinsertion)

lemma subtype.top_def : (⟨I, le_refl I⟩ : {J : ideal A // J ≤ I}) = ⊤ := 
eq_top_iff.mpr (⊤ : {J : ideal A // J ≤ I}).property

lemma subtype.bot_def : (⟨⊥, bot_le⟩ : {J : ideal A // J ≤ I}) = ⊥ := 
by rw [subtype.mk_bot]

lemma subtype.inf_def (J J' : {J : ideal A // J ≤ I}) : 
  (J ⊓ J' : {J : ideal A // J ≤ I} ) = ⟨(J : ideal A) ⊓ (J' : ideal A), inf_le_of_left_le J.2⟩ :=
by { ext x, exact ⟨λ ⟨h, h'⟩, h, λ h, ⟨h, J.property h.left⟩⟩ }

lemma subtype.Inf_def (S : set {J : ideal A // J ≤ I}) : 
  (Inf S : {J : ideal A // J ≤ I} ) = ⟨(Inf ((coe : _ → ideal A) '' S)) ⊓ I, inf_le_right⟩ :=
by { ext x, refl }

lemma subtype.sup_def (J J' : {J : ideal A // J ≤ I}) : 
  (J ⊔ J' : {J : ideal A // J ≤ I} ) = 
    ⟨Inf {B | (J : ideal A) ≤ B ∧ (J' : ideal A) ≤ B}, Inf_le_of_le ⟨J.2, J'.2⟩ (le_refl I)⟩ :=
begin
  ext x,
  refine ⟨λ ⟨h, h'⟩, h, λ h, ⟨h, _⟩⟩,
  rw [subtype.coe_mk, submodule.mem_Inf] at h,
  exact h I ⟨J.2, J'.2⟩
end

lemma subtype.Sup_def (S : set {J : ideal A // J ≤ I}) : 
  (Sup S : {J : ideal A // J ≤ I} ) = ⟨(Sup ((coe : _ → ideal A) '' S)) ⊓ I, inf_le_right⟩ :=
by { ext x, refl }

lemma coe_coe (J : sub_pd_ideal hI) : ((J : {J : ideal A // J ≤ I}) : ideal A) = (J : ideal A) := 
rfl

instance : complete_lattice (sub_pd_ideal hI) :=
begin
  refine function.injective.complete_lattice (λ J : sub_pd_ideal hI, (J : {J : ideal A // J ≤ I}))
    (λ J J' h, (ext_iff _ _).mpr (subtype.ext_iff.mp h)) (λ J J', by rw subtype.sup_def; refl)
    (λ J J', by rw subtype.inf_def; refl) _ _ (by rw ← subtype.top_def; refl) 
    (by rw ← subtype.bot_def; refl),
  { intro S,
    conv_rhs { rw supr },
    rw [subtype.Sup_def, subtype.ext_iff, coe_coe, coe_def, Sup_carrier_def, subtype.coe_mk, 
      Sup_image, Sup_image, supr_range], 
    have : ∀ (J : hI.sub_pd_ideal),
      ((⨆ (H : J ∈ S), (J : {B : ideal A // B ≤ I}) : {B : ideal A // B ≤ I} ) : ideal A) =
      (⨆ (H : J ∈ S), (J : ideal A)),
    { intro J,
      by_cases hJ : J ∈ S,
      { rw [csupr_pos hJ, csupr_pos hJ], refl },
      { simp only [hJ, supr_false, subtype.coe_eq_bot_iff, bot_le] }},
    simp_rw this,
    ext a,
    refine ⟨λ ha, ⟨ha, _⟩, λ ha, ha.1⟩,
    apply (submodule.mem_supr _).mp ha I,
    intro J,
    by_cases hJ : J ∈ S,
    { rw csupr_pos hJ, exact J.is_sub_ideal, },
    { simp only [hJ, supr_false, bot_le] }},
  { intro S,
    conv_rhs { rw infi },
    rw [subtype.Inf_def, subtype.ext_iff, coe_coe, coe_def, Inf_carrier_def, subtype.coe_mk,
      Inf_image, infi_range, infi_inf, infi_insert, inf_infi],
    apply infi_congr,
    intro J,
    by_cases hJ : J ∈ S,
    { rw [cinfi_pos hJ, cinfi_pos hJ, inf_comm], refl, },
    { simp only [hJ, infi_false, inf_top_eq, ← subtype.top_def, subtype.coe_mk, inf_idem], refl }}
end

end complete_lattice 

end sub_pd_ideal

namespace quot

variables {A : Type*} [comm_ring A] {I : ideal A} (hI : divided_powers I)

/- Tagged as noncomputable because it makes use of function.extend, 
but under is_sub_pd_ideal hI (J ⊓ I), dpow_quot_eq proves that no choices are involved -/
/-- The definition of divided powers on A ⧸ J -/
noncomputable def dpow (J : ideal A) : ℕ → (A ⧸ J) → (A ⧸ J) := 
λ n, function.extend (λ a, ideal.quotient.mk J ↑a : I → A ⧸ J) 
  (λ a, (ideal.quotient.mk J) (hI.dpow n a) : I → A ⧸ J) 0

variables {J : ideal A} (hIJ : is_sub_pd_ideal hI (J ⊓ I))

include hIJ

open_locale classical

/-- Divided powers on the quotient are compatible with quotient map -/
lemma dpow_eq {n : ℕ} {a : A} (ha : a ∈ I) :
  dpow hI J n (ideal.quotient.mk J a) = (ideal.quotient.mk J) (hI.dpow n a) :=
begin
  have ha' : ∃ (a' : ↥I), (ideal.quotient.mk J) ↑a' = (ideal.quotient.mk J) a := ⟨⟨a, ha⟩, rfl⟩,
  simp only [dpow],
  rw [ function.extend_def, dif_pos ha', ideal.quotient.eq], 
  apply (is_sub_pd_ideal_inf_iff hI J).mp hIJ n _ _ (set_like.coe_mem _) ha,
  rw [← ideal.quotient.eq, classical.some_spec ha'], 
end

-- We wish for a better API to denote I.map (ideal.quotient.mk J) as I ⧸ J 
/-- When `I ⊓ J` is a `sub_pd_ideal` of `I`, the dpow map for the ideal `I(A⧸J)` of the quotient -/
noncomputable def divided_powers : divided_powers (I.map (ideal.quotient.mk J)) :=
{ dpow := dpow hI J, 
  dpow_null := λ n x hx, 
  begin
    simp only [dpow, function.extend_def], 
    have ha' : ¬ ∃ (a' : ↥I), (ideal.quotient.mk J) ↑a' = x,
    { rintro ⟨a, rfl⟩, 
      exact hx (ideal.apply_coe_mem_map (ideal.quotient.mk J) I a), },
    rw [dif_neg ha', pi.zero_apply],
  end,
  dpow_zero := λ x hx, 
  begin
    obtain ⟨a, ha, hax⟩ := 
    (ideal.mem_map_iff_of_surjective _ (ideal.quotient.mk J).is_surjective).mp hx,
    rw [← hax, dpow_eq hI hIJ ha, hI.dpow_zero ha, map_one],
  end,
  dpow_one := λ x hx, 
  begin
    obtain ⟨a, ha, hax⟩ := 
    (ideal.mem_map_iff_of_surjective _ (ideal.quotient.mk J).is_surjective).mp hx,
    rw [← hax, dpow_eq hI hIJ ha, hI.dpow_one ha],
  end,
  dpow_mem := λ n hn x hx, 
  begin 
    simp only [dpow], rw function.extend_def,
    split_ifs with ha,
    { rw [ideal.mem_quotient_iff_mem_sup],
      exact ideal.mem_sup_left (hI.dpow_mem hn (set_like.coe_mem _)) },
    { exact ideal.zero_mem _ }
  end, 
  dpow_add := λ n x y hx hy, 
  begin
    obtain ⟨a, ha, hax⟩ := 
    (ideal.mem_map_iff_of_surjective _ (ideal.quotient.mk J).is_surjective).mp hx,
    obtain ⟨b, hb, hby⟩ := 
    (ideal.mem_map_iff_of_surjective _ (ideal.quotient.mk J).is_surjective).mp hy,
    rw [← hax, ← hby, ← map_add, dpow_eq hI hIJ (I.add_mem ha hb), hI.dpow_add n ha hb, 
      map_sum, 
 finset.sum_congr rfl],
    { intros k hk, 
      rw [dpow_eq hI hIJ ha, dpow_eq hI hIJ hb, ← map_mul] },
  end,
  dpow_smul := λ n x y hy, 
  begin
    obtain ⟨a, rfl⟩ := ideal.quotient.mk_surjective x, 
    obtain ⟨b, hb, hby⟩ := 
    (ideal.mem_map_iff_of_surjective _ (ideal.quotient.mk J).is_surjective).mp hy,
    rw [← hby, dpow_eq hI hIJ hb, ← map_mul, ← map_pow, dpow_eq hI hIJ (ideal.mul_mem_left I a hb),
      hI.dpow_smul n hb, map_mul],
    end,
  dpow_mul := λ m n x hx, 
  begin
    obtain ⟨a, ha, hax⟩ := 
    (ideal.mem_map_iff_of_surjective _ (ideal.quotient.mk J).is_surjective).mp hx,
    simp only [← hax, dpow_eq hI hIJ ha], 
    rw [← map_mul, hI.dpow_mul m n ha, map_mul, map_nat_cast],
  end,
  dpow_comp := λ m n hn x hx,
  begin 
    obtain ⟨a, ha, hax⟩ := 
    (ideal.mem_map_iff_of_surjective _ (ideal.quotient.mk J).is_surjective).mp hx,
    simp only [← hax, dpow_eq hI hIJ, ha, hI.dpow_mem hn ha],
    rw [hI.dpow_comp m hn ha, map_mul, map_nat_cast],
  end }

lemma divided_powers_dpow_quot_apply {n : ℕ} {x : A ⧸ J} :
  (divided_powers hI hIJ).dpow n x = dpow hI J n x :=
rfl

lemma divided_powers_quot_unique (hquot : _root_.divided_powers (I.map (ideal.quotient.mk J)))
  (hm : is_pd_morphism hI hquot (ideal.quotient.mk J)) :
  hquot = divided_powers hI hIJ := eq_of_eq_on_ideal _ _ $ λ n x hx,
begin
  obtain ⟨a, ha, hax⟩ := 
  (ideal.mem_map_iff_of_surjective _ (ideal.quotient.mk J).is_surjective).mp hx,
  rw [← hax, hm.dpow_comp n a ha, divided_powers_dpow_quot_apply, dpow_eq hI hIJ ha],
end

end quot

end divided_powers