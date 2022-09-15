/- ACL and MIdFF, Lean 2022 meeting at Icerm -/

import tactic
import ring_theory.ideal.operations
import ring_theory.ideal.quotient
import linear_algebra.quotient
import ring_theory.tensor_product

/-! # Divided powers 

Let `A` be a commutative ring and `I` be an ideal of `A`. 
A *divided power* structure on `I` is the datum of operations `div_pow : ℕ → I → A` 
satisfying relations that model the 
intuitive formula `div_pow n a = a ^ n / n.factorial` and collected by the structure `divided_powers`.
To avoid coercions, we rather consider `div_pow : ℕ → A → A`, extended by 0.

## References 

* P. Berthelot (1974), *Cohomologie cristalline des schémas de caractéristique $p$ > 0*, 
Lectures notes in mathematics 407, Springer-Verlag.

* P. Berthelot and A. Ogus (1978), *Notes on crystalline cohomology*, 
Princeton University Press.

-/

open_locale classical

section combinatorics

/-- Number of possibilities of choosing m groups of n-element subsets out of mn elements -/
def mchoose (m n : ℕ) : ℕ := 
finset.prod (finset.range m) (λ p, nat.choose (p * n + n - 1) (n - 1))

lemma mchoose_zero (n : ℕ) : mchoose 0 n = 1 := 
by rw [mchoose, finset.range_zero, finset.prod_empty]

lemma mchoose_succ (m n : ℕ) : 
  mchoose (m + 1) n = (nat.choose (m * n + n - 1) (n - 1)) * (mchoose m n) := 
by simp only [mchoose, finset.prod_range_succ, mul_comm]

lemma mchoose_lemma (m : ℕ) {n : ℕ} (hn : 0 < n) :
  (m.factorial) * (n.factorial)^m * (mchoose m n) = (m * n).factorial :=
begin
  induction m with m ih,
  { rw [mchoose_zero, mul_one, zero_mul, nat.factorial_zero, pow_zero, mul_one] }, 
  { have hmn : (m + 1) * (m * n + n - 1).choose (n - 1) = (m * n + n).choose n,
    { rw [← nat.mul_left_inj (nat.mul_pos (nat.factorial_pos (m * n)) (nat.factorial_pos n)), 
        ← mul_assoc, ← mul_assoc, nat.add_choose_mul_factorial_mul_factorial,
        ← nat.mul_factorial_pred hn, mul_comm n _, ← mul_assoc, nat.add_sub_assoc hn (m * n),
        mul_comm,mul_assoc ((m + 1) * (m * n + (n - 1)).choose (n - 1)), mul_assoc (m + 1),
        ← mul_assoc ((m * n + (n - 1)).choose (n - 1)), nat.add_choose_mul_factorial_mul_factorial,
        ← nat.mul_factorial_pred  (nat.add_pos_right _ hn), ← nat.add_sub_assoc hn (m * n)], 
      ring, },
    rw [mchoose_succ, nat.factorial_succ, pow_succ, ← mul_assoc],
    conv_rhs { rw nat.succ_mul},
    rw [← nat.add_choose_mul_factorial_mul_factorial, ← ih, ← hmn],
    ring_nf, }
end

end combinatorics

section divided_powers_definition

/- No need for this, Mario says…

structure is_divided_powers {A : Type*} [comm_ring A] (I : ideal A) (dpow : ℕ → A → A) : Prop :=
(dpow_null : ∀ {n x} (hx : x ∉ I), dpow n x = 0)
(dpow_zero : ∀ {x} (hx : x ∈ I), dpow 0 x = 1)
(dpow_one : ∀ {x} (hx : x ∈ I), dpow 1 x = x)
(dpow_mem : ∀ {n} (hn : n ≠ 0) {x} (hx : x ∈ I), dpow n x ∈ I)
(dpow_sum : ∀ n {x y} (hx : x ∈ I) (hy : y ∈ I) , dpow n (x + y)
  = finset.sum (finset.range (n + 1)) (λ k, (dpow k x) * (dpow (n - k) y)))
(dpow_smul : ∀ n {a} {x} (hx : x ∈ I), dpow n (a * x) = (a ^ n) * (dpow n x))
(dpow_mul : ∀ m n {x} (hx : x ∈ I), (dpow m x) * (dpow n x) = (nat.choose (n+m) m) * dpow (n + m) x)
(dpow_comp : ∀ m {n} (hn : n ≠ 0) {x} (hx : x ∈ I),
  dpow m (dpow n x) = (mchoose m n) * dpow (m * n) x)
 -/

/-- The divided power structure on an ideal I of a commutative ring A -/
structure divided_powers {A : Type*} [comm_ring A] (I : ideal A) := 
(dpow : ℕ → A → A)
(dpow_null : ∀ {n x} (hx : x ∉ I), dpow n x = 0)
(dpow_zero : ∀ {x} (hx : x ∈ I), dpow 0 x = 1)
(dpow_one : ∀ {x} (hx : x ∈ I), dpow 1 x = x)
(dpow_mem : ∀ {n} (hn : n ≠ 0) {x} (hx : x ∈ I), dpow n x ∈ I)
(dpow_sum : ∀ n {x y} (hx : x ∈ I) (hy : y ∈ I) , dpow n (x + y)
  = finset.sum (finset.range (n + 1)) (λ k, (dpow k x) * (dpow (n - k) y)))
(dpow_smul : ∀ n {a} {x} (hx : x ∈ I), dpow n (a * x) = (a ^ n) * (dpow n x))
(dpow_mul : ∀ m n {x} (hx : x ∈ I), (dpow m x) * (dpow n x) = (nat.choose (n+m) m) * dpow (n + m) x)
(dpow_comp : ∀ m {n} (hn : n ≠ 0) {x} (hx : x ∈ I),
  dpow m (dpow n x) = (mchoose m n) * dpow (m * n) x)

instance {A : Type*} [comm_ring A] (I : ideal A) : has_coe_to_fun (divided_powers I) (λ _, ℕ → A → A) := ⟨λ hI, hI.dpow⟩

structure pd_ring {A : Type*} extends comm_ring A := 
(pd_ideal : ideal A)
(divided_powers : divided_powers pd_ideal)

/-  Does not work
def pd_ring.mk (A : Type*) [comm_ring A] (I : ideal A) (hI : divided_powers I):
  pd_ring := {
    pd_ideal := I,
    divided_powers := hI, 
    .. ‹ comm_ring A › }
 -/

end divided_powers_definition

namespace divided_powers

section divided_powers_examples

variables {A : Type*} [comm_ring A] {I : ideal A} (hI : divided_powers I)
include hI

lemma factorial_mul_dpow_eq_pow (n : ℕ) (x : A) (hx : x ∈ I) : (n.factorial : A) * (hI.dpow n x) = x^n :=
begin
  induction n with n ih,
  { rw [nat.nat_zero_eq_zero, nat.factorial_zero, nat.cast_one, one_mul, pow_zero, hI.dpow_zero hx], },
  { rw [nat.factorial_succ, mul_comm (n + 1), nat.cast_mul, mul_assoc, pow_succ', ← ih, mul_assoc,
      ← (n + 1).choose_one_right, nat.succ_eq_add_one, ← hI.dpow_mul _ _ hx, hI.dpow_one hx,
      mul_comm (x : A)], }
end

example (n : ℕ) (hn : n ≠ 0) : 0 ^ n = 0 :=
begin
exact zero_pow' n hn,
end

lemma dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : hI.dpow n 0 = 0 := 
begin
  rw [← mul_zero (0 : A), hI.dpow_smul, zero_pow' n hn, zero_mul, zero_mul],
  exact ideal.zero_mem I,
end

end divided_powers_examples

section divided_powers_morphisms

-- Remove the explicit I and J… 
/-- Compatibility of a ring morphism with pd-structures -/
structure is_pd_morphism {A B : Type*} [comm_ring A] [comm_ring B] (I : ideal A) (J : ideal B )
  (hI : divided_powers I) (hJ : divided_powers J) (f : A →+* B) :=
(ideal_comp : I.map f ≤ J)
(dpow_comp : ∀ (n : ℕ) (a ∈ I), hJ.dpow n (f a) = f (hI.dpow n a))

/-- The structure of a pd_morphism between rings endowed with pd-rings -/
structure pd_morphism {A B : Type*} [comm_ring A] [comm_ring B] {I : ideal A} {J : ideal B }
  (hI : divided_powers I) (hJ : divided_powers J) :=
(to_ring_hom : A →+* B)
(ideal_comp : I.map to_ring_hom ≤ J)
(dpow_comp : ∀ (n : ℕ) (a ∈ I), 
  hJ.dpow n (to_ring_hom a) = to_ring_hom (hI.dpow n a))

-- For the moment, the notation does not work
-- notation `p(` A `,` I, `,` hI `)` →ₚ  `(` B `,` J, `,` hJ `)` := pd_morphism hI hJ
-- Also, we expect a `pd` subscript

/- TODO : identity, composition… -/

end divided_powers_morphisms

section sub_pd_ideals

variables {A : Type*} [comm_ring A] {I : ideal A} (hI : divided_powers I)
include hI

/-- The structure of a sub-pd-ideal of a pd-ideal -/
structure is_sub_pd_ideal (J : ideal A) : Prop :=
(is_sub_ideal : J ≤ I)
(dpow_mem_ideal : ∀ (n : ℕ) (hn : n ≠ 0) (j ∈ J), hI.dpow n j ∈ J )

/- If there is a pd-structure on I(A/J) such that the quotient map is 
   a pd-morphism, then J ⊓ I is a sub-pd-ideal of I -/
lemma is_sub_pd_ideal_of (J : ideal A) (hJ : divided_powers (I.map (ideal.quotient.mk J)))
  (φ : pd_morphism hI hJ) (hφ:  φ.to_ring_hom = ideal.quotient.mk J) : 
  hI.is_sub_pd_ideal (J ⊓ I) := 
begin
  split,
  exact semilattice_inf.inf_le_right J I, 
  intros n hn a, 
  simp only [ideal.mem_inf], 
  rintros ⟨haJ, haI⟩,
  split,
  { rw [← ideal.quotient.eq_zero_iff_mem, ← hφ],
    rw ← φ.dpow_comp n a,  
    suffices : (φ.to_ring_hom) a = 0, rw this,
    exact hJ.dpow_eval_zero hn,
    rw [hφ, ideal.quotient.eq_zero_iff_mem], 
    exact haJ, exact haI, }, 
  exact hI.dpow_mem hn haI,
end

/-- The ideal J ⊓ I is a sub-pd-ideal of I, 
    if and only if (on I) the divided powers have some compatiblity mod J 
    (The necessity was proved as a sanity check.) -/
lemma is_sub_pd_ideal_inf_iff (J : ideal A) :
  (is_sub_pd_ideal hI (J ⊓ I)) ↔
  (∀ (n : ℕ) (a b : A) (ha : a ∈ I) (hb : b ∈ I) 
    (hab : (a - b) ∈ J), hI.dpow n a - hI.dpow n b ∈ J) := 
begin
  split,
  { intro hIJ,
    intros n a b ha hb hab,
    have hb' : a = b + (a - b), by rw [add_comm, sub_add_cancel],
    have hab' : a - b ∈ I := ideal.sub_mem I ha hb,  
    rw hb',
    rw hI.dpow_sum n hb hab', 
    rw finset.range_succ, 
    rw finset.sum_insert (finset.not_mem_range_self),
    simp only [tsub_self, hI.dpow_zero hab', mul_one, add_sub_cancel'], 
    apply ideal.sum_mem ,
    intros i hi, 
    simp only [finset.mem_range] at hi,
    apply J.smul_mem,
    apply semilattice_inf.inf_le_left J I,
    let hzz := hIJ.dpow_mem_ideal (n - i),
    apply hIJ.dpow_mem_ideal (n - i) _ _ _, 
    { apply ne_of_gt, exact (nat.sub_pos_of_lt hi), }, 
    rw ideal.mem_inf, exact ⟨hab, hab'⟩ },
  { intro hIJ, 
    split,
    apply semilattice_inf.inf_le_right J I,
    intros n hn a ha, 
    rw ideal.mem_inf at ha, 
    simp only [ideal.mem_inf], 
    split,
    { rw [← sub_zero (hI.dpow n a), ← hI.dpow_eval_zero hn], 
      apply hIJ n a 0 ha.2 (I.zero_mem), 
      rw sub_zero, exact ha.1, },
    { exact hI.dpow_mem hn ha.2, } },
end


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

/-- Divided powers on the quotient are compatible with quotient map -/
lemma dpow_quot_eq (J : ideal A) (hIJ : is_sub_pd_ideal hI (J ⊓ I))
  (n : ℕ) {a : A} (ha : a ∈ I) :
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
noncomputable
def divided_powers_quot (J  : ideal A) (hIJ : is_sub_pd_ideal hI (J ⊓ I)) : divided_powers (I.map (ideal.quotient.mk J)) := {
dpow := dpow_quot hI J, 
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
dpow_sum := λ n x y hx hy, 
begin
  rw ideal.mem_map_iff_of_surjective at hx, 
  swap, exact ideal.quotient.mk_surjective,
  obtain ⟨a, ha, rfl⟩ := hx, 
  rw ideal.mem_map_iff_of_surjective at hy, 
  swap, exact ideal.quotient.mk_surjective,
  obtain ⟨b, hb, rfl⟩ := hy, 
  rw ← map_add, 
  rw dpow_quot_eq hI J hIJ n (I.add_mem ha hb),
  rw hI.dpow_sum n ha hb, rw ring_hom.map_sum, 
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

/- TODO : 
* add rfl lemma that gives analogue of dpow_quot_eq for the divided_powers 
that was just defined 
* maybe other… 
-/

/-- Lemma 3.6 of [BO] -/
lemma span_is_sub_pd_ideal_iff (S : set A) (hS : S ⊆ I) :
  is_sub_pd_ideal hI (ideal.span S) ↔ 
  ∀ (n : ℕ) (hn : 0 < n) (s : S), hI.dpow n s ∈ ideal.span S := sorry


/- 3.7 Lemma. Suppose R is a ring, В and С are R-algebras, and
I ⊆ В and J ⊆ С are augmentation ideals (i.e. there is a section of В → B/I, etc.) 
with P.D. structures γ and δ, respectively. 
Then the ideal К = Ker (В ⊗ С → B/I ⊗ C/J) has a unique P.D. structure ε 
such that (B,I,γ) → (В ⊗ С,К,ε) and
(C,J,δ) → (B ⊗ C,K,ε) are P.D. morphisms. -/

open algebra
open_locale tensor_product

/- Lemma 3.7 of [BO] -/
def foo (R B C : Type*) [comm_ring R] [comm_ring B] [comm_ring C] [algebra R B]
  [algebra R C] {I : ideal B} {J : ideal C} (hI : divided_powers I) (hJ : divided_powers J)
  (hIs : function.has_right_inverse (ideal.quotient.mk I))
  (hJs : function.has_right_inverse (ideal.quotient.mk J)) :
  divided_powers (algebra.tensor_product.map (ideal.quotient.mkₐ R I) 
    (ideal.quotient.mkₐ R J)).to_ring_hom.ker  :=
begin
  let K := (algebra.tensor_product.map (ideal.quotient.mkₐ R I)
    (ideal.quotient.mkₐ R J)).to_ring_hom.ker,
sorry
end

end sub_pd_ideals

end divided_powers