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
      cases not_eq_or_aux hn hm with hm hm,
      { refine ideal.mul_mem_right _ (ideal.span S) (hx m hm), },
      { refine ideal.mul_mem_left (ideal.span S) _ (hy (n - m) hm), } },
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
include hI

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
      cases not_eq_or_aux hn hk with hk' hk',
      { apply ideal.mul_mem_right _ (I • J), exact hx' k hk', },
      { apply ideal.mul_mem_left (I • J), exact hy' _ hk', } }
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
      cases not_eq_or_aux hn hm with hm hm,
      { exact ideal.mul_mem_right _ (ideal.span _) (hx_pow m hm) },
      { exact ideal.mul_mem_left (ideal.span _) _ (hy_pow (n - m) hm) }},
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

instance : has_le (sub_pd_ideal hI) := ⟨λ J J', J.carrier ≤ J'.carrier⟩

lemma le_iff {J J' : sub_pd_ideal hI} : J ≤ J' ↔ J.carrier ≤ J'.carrier := iff.rfl

instance : has_lt (sub_pd_ideal hI) := ⟨λ J J', J.carrier < J'.carrier⟩

lemma lt_iff {J J' : sub_pd_ideal hI} : J < J' ↔ J.carrier < J'.carrier := iff.rfl

instance : complete_lattice (sub_pd_ideal hI) :=
{ sup := sorry,
  le  := has_le.le,
  lt  := has_lt.lt,
  le_refl := le_refl,
  le_trans := λ J K L, le_trans,
  lt_iff_le_not_le := λ J J', lt_iff_le_not_le,
  le_antisymm := λ J J', le_antisymm,
  le_sup_left := sorry,
  le_sup_right := sorry,
  sup_le := sorry,
  inf := has_inf.inf,
  inf_le_left := λ J J' x hx, hx.left,
  inf_le_right := λ J J' x hx, hx.right,
  le_inf := λ J K L hJK hJL, by { rw le_iff at hJK hJL ⊢, exact le_inf hJK hJL }, 
  Sup := sorry,
  le_Sup := sorry,
  Sup_le := sorry,
  Inf := has_Inf.Inf,
  Inf_le := λ S J hJS, sorry,
  le_Inf := sorry,
  top := has_top.top,
  bot := has_bot.bot,
  le_top := λ J, J.is_sub_ideal,
  bot_le := λ J, bot_le }
end complete_lattice

end sub_pd_ideal

section quot

variables {A : Type*} [comm_ring A] {I : ideal A} (hI : divided_powers I)

/- Tagged as noncomputable because it makes use of function.extend, 
but under is_sub_pd_ideal hI (J ⊓ I), dpow_quot_eq proves that no choices are involved -/
/-- The definition of divided powers on A ⧸ J -/
noncomputable
def dpow_quot (J : ideal A) : -- (hIJ : is_sub_pd_ideal hI (J ⊓ I)) :
  ℕ → (A ⧸ J) → (A ⧸ J) := λ n, 
  function.extend 
    (λ a, ideal.quotient.mk J ↑a : I → A ⧸ J) 
    (λ a, (ideal.quotient.mk J) (hI.dpow n a) : I → A ⧸ J) 
    (0)

variables (J : ideal A) (hIJ : is_sub_pd_ideal hI (J ⊓ I))
include hIJ

open_locale classical

/-- Divided powers on the quotient are compatible with quotient map -/
lemma dpow_quot_eq (n : ℕ) {a : A} (ha : a ∈ I) :
  dpow_quot hI J n (ideal.quotient.mk J a) = (ideal.quotient.mk J) (hI.dpow n a) :=
begin
  rw dpow_quot, simp only, rw function.extend_def, 
  have ha' : ∃ (a' : ↥I), (ideal.quotient.mk J) ↑a' = (ideal.quotient.mk J) a,
  { use ⟨a, ha⟩, simp only [submodule.coe_mk], },
  simp only [ha', dif_pos], 
  rw ideal.quotient.eq, 
  apply (is_sub_pd_ideal_inf_iff hI J).mp hIJ, 
  apply set_like.coe_mem,
  exact ha,
  rw ← ideal.quotient.eq, 
  rw classical.some_spec ha', 
end

-- We wish for a better API to denote I.map (ideal.quotient.mk J) as I ⧸ J 
/-- When `I ⊓ J` is a `sub_pd_ideal` of `I`, the dpow map for the ideal `I(A⧸J)` of the quotient -/
noncomputable def divided_powers_quot : divided_powers (I.map (ideal.quotient.mk J)) :=
{ dpow := dpow_quot hI J, 
  dpow_null := λ n x hx, 
  begin
    rw dpow_quot, simp only, rw function.extend_def, 
    have ha' : ¬ ∃ (a' : ↥I), (ideal.quotient.mk J) ↑a' = x,
    { intro ha, obtain ⟨a, rfl⟩ := ha, 
      apply hx, 
      exact ideal.apply_coe_mem_map (ideal.quotient.mk J) I a, },
    simp only [ha', not_false_iff, pi.zero_apply, dif_neg],
  end,
  dpow_zero := λ x hx, 
  begin
    rw ideal.mem_map_iff_of_surjective at hx, 
    swap, exact ideal.quotient.mk_surjective,
    obtain ⟨a, ha, rfl⟩ := hx, 
    rw dpow_quot_eq hI J hIJ 0 ha,
    rw hI.dpow_zero ha, 
    exact map_one (ideal.quotient.mk J),
  end,
  dpow_one := λ x hx, 
  begin
    rw ideal.mem_map_iff_of_surjective at hx, 
    swap, exact ideal.quotient.mk_surjective,
    obtain ⟨a, ha, rfl⟩ := hx, 
    rw dpow_quot_eq hI J hIJ 1 ha,
    rw hI.dpow_one ha, 
  end,
  dpow_mem := λ n hn x hx, 
  begin 
    rw dpow_quot, simp only, rw function.extend_def,
    cases em (∃ (a : I), ideal.quotient.mk J ↑a = x) with ha ha,
    simp only [ha, dif_pos, ideal.mem_quotient_iff_mem_sup],
    apply ideal.mem_sup_left,
    apply hI.dpow_mem hn,
    apply set_like.coe_mem, 
    simp only [ha, not_false_iff, pi.zero_apply, dif_neg, submodule.zero_mem],
  end, 
  dpow_add := λ n x y hx hy, 
  begin
    rw ideal.mem_map_iff_of_surjective at hx, 
    swap, exact ideal.quotient.mk_surjective,
    obtain ⟨a, ha, rfl⟩ := hx, 
    rw ideal.mem_map_iff_of_surjective at hy, 
    swap, exact ideal.quotient.mk_surjective,
    obtain ⟨b, hb, rfl⟩ := hy, 
    rw ← map_add, 
    rw dpow_quot_eq hI J hIJ n (I.add_mem ha hb),
    rw hI.dpow_add n ha hb, rw ring_hom.map_sum, 
    rw finset.sum_congr rfl, 
    { intros k hk, 
      rw dpow_quot_eq hI J hIJ _ ha, 
      rw dpow_quot_eq hI J hIJ _ hb, 
      rw ← map_mul },
  end,
  dpow_smul := λ n x y hy, 
  begin
    obtain ⟨a, rfl⟩ := ideal.quotient.mk_surjective x, 
    rw ideal.mem_map_iff_of_surjective at hy, 
    swap, exact ideal.quotient.mk_surjective,
    obtain ⟨b, hb, rfl⟩ := hy, 
    rw hI.dpow_quot_eq J hIJ n hb, 
    simp only [← map_mul, ← map_pow],
    rw hI.dpow_quot_eq J hIJ n, 
    apply congr_arg,
    rw hI.dpow_smul n hb,
    exact ideal.mul_mem_left I a hb,
  end,
  dpow_mul := λ m n x hx, 
  begin
    rw ideal.mem_map_iff_of_surjective at hx, 
    swap, exact ideal.quotient.mk_surjective,
    obtain ⟨a, ha, rfl⟩ := hx, 
    simp only [hI.dpow_quot_eq J hIJ _ ha], rw ← map_mul,
    rw hI.dpow_mul m n ha,
    simp only [map_mul, map_nat_cast],
  end,
  dpow_comp := λ m n hn x hx,
  begin 
    rw ideal.mem_map_iff_of_surjective at hx, 
    swap, exact ideal.quotient.mk_surjective,
    obtain ⟨a, ha, rfl⟩ := hx, 
    simp only [hI.dpow_quot_eq J hIJ _, ha, hI.dpow_mem hn ha],
    rw hI.dpow_comp m hn ha, 
    simp only [map_mul, map_nat_cast],
  end }

lemma divided_powers_dpow_quot_apply (n : ℕ) (x : A ⧸ J) :
  (divided_powers_quot hI J hIJ).dpow n x = dpow_quot hI J n x :=
rfl

lemma divided_powers_quot_unique (hquot : divided_powers (I.map (ideal.quotient.mk J)))
  (hm : is_pd_morphism hI hquot (ideal.quotient.mk J)) :
  hquot = divided_powers_quot hI J hIJ := 
begin
  apply eq_of_eq_on_ideal, 
  intros n x hx,
  obtain ⟨a, ha, hax⟩ := 
  (ideal.mem_map_iff_of_surjective _ (ideal.quotient.mk J).is_surjective).mp hx,
  rw [← hax, hm.dpow_comp n a ha, divided_powers_dpow_quot_apply, dpow_quot_eq hI J hIJ n ha], 
end

end quot

end divided_powers