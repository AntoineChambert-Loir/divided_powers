/- ACL and MIdFF, Lean 2022 meeting at Icerm -/

import tactic
import ring_theory.ideal.operations
import ring_theory.ideal.quotient
import linear_algebra.quotient
import ring_theory.tensor_product
import ring_theory.ideal.operations

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

* N. Roby (1968), *Construction de certaines algèbres à puissances divisées*, 
Bulletin de la Société Mathématique de France, Tome 96, p. 97-113. 
doi: https://doi.org/10.24033/bsmf.1661

* N. Roby (1966), *Sur l'algèbre des puissances divisées d'un module et le module de ses différentielles*,
Annales scientifiques de l'École Normale Supérieure, Série 3, Tome 83,no. 2, p. 75-89. 
doi: https://doi.org/10.24033/asens.1148

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
@[ext] structure divided_powers {A : Type*} [comm_ring A] (I : ideal A) := 
(dpow : ℕ → A → A)
(dpow_null : ∀ {n x} (hx : x ∉ I), dpow n x = 0)
(dpow_zero : ∀ {x} (hx : x ∈ I), dpow 0 x = 1)
(dpow_one : ∀ {x} (hx : x ∈ I), dpow 1 x = x)
(dpow_mem : ∀ {n} (hn : n ≠ 0) {x} (hx : x ∈ I), dpow n x ∈ I)
(dpow_sum : ∀ n {x y} (hx : x ∈ I) (hy : y ∈ I) , dpow n (x + y)
  = finset.sum (finset.range (n + 1)) (λ k, (dpow k x) * (dpow (n - k) y)))
(dpow_smul : ∀ n {a : A} {x} (hx : x ∈ I), dpow n (a * x) = (a ^ n) * (dpow n x))
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

/- To help distinguish the extreme cases in a finset.range(n+1).sum -/
lemma not_eq_or_aux {n m : ℕ} (hn : n ≠ 0) (hm : m ∈ finset.range(n + 1)) : m ≠ 0 ∨ n - m ≠ 0 :=
begin
  simp only [finset.mem_range, nat.lt_succ_iff] at hm,
  by_contradiction h,
  simp only [not_or_distrib, ne.def, not_not, tsub_eq_zero_iff_le, not_le, not_lt] at h,
  apply hn, rw ← le_zero_iff, rw ← h.1, exact h.2, 
end

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

end divided_powers


section factorial_inverse
variables {A : Type*} [comm_ring A] {I : ideal A}

lemma factorial_is_unit {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A))
  {m : ℕ} (hmn : m < n) : is_unit (m.factorial : A) :=
begin
  apply is_unit_of_dvd_unit _ hn_fac,
  obtain ⟨c, hc⟩ := nat.factorial_dvd_factorial (nat.le_pred_of_lt hmn),
  use (c : A),
  rw [← nat.cast_mul, hc],
end

noncomputable def factorial_unit {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A))
  {m : ℕ} (hmn : m < n) : Aˣ :=
(factorial_is_unit hn_fac hmn).unit

lemma factorial_unit_coe {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ} (hmn : m < n) :
  (factorial_unit hn_fac hmn : A) = (m.factorial : A) :=
rfl

lemma factorial_inverse_mul {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ} (hmn : m < n) :
  ((factorial_unit hn_fac hmn).inv : A) * (m.factorial : A) = 1 :=
by simp only [units.inv_eq_coe_inv, units.inv_mul_eq_one, factorial_unit, is_unit.unit_spec]

lemma factorial_inverse_one {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) (hn1 : 1 < n) :
  (factorial_unit hn_fac hn1).inv = 1 :=
begin
  rw [← mul_one (factorial_unit hn_fac hn1).inv],
  convert factorial_inverse_mul hn_fac hn1,
  rw [nat.factorial_one, nat.cast_one]
end

end factorial_inverse

namespace divided_powers

section factorial

variables {A : Type*} [comm_ring A] {I : ideal A}
/-- Proposition 1.2.7 of [B74], part (i). -/
lemma nilpotent_of_pd_ideal_mem (hI : divided_powers I) {n : ℕ} (hn : n ≠ 0)
  (hnI : ∀ {y : A}(hy : y ∈ I), n • y = 0) {x : A} (hx : x ∈ I) : x^n = 0 := 
begin
  have h_fac: (n.factorial : A) * hI.dpow n x = n • ((n-1).factorial : A) * hI.dpow n x,
  { rw [nsmul_eq_mul, ← nat.cast_mul, nat.mul_factorial_pred (nat.pos_of_ne_zero hn)] },
  rw [← factorial_mul_dpow_eq_pow hI _ _ hx, h_fac, smul_mul_assoc],
  exact hnI (I.mul_mem_left ((n - 1).factorial : A) (hI.dpow_mem hn hx))
end

namespace of_invertible_factorial

noncomputable def dpow (I : ideal A) {n : ℕ} (hn0 : n ≠ 0)
  (hn_fac : is_unit ((n-1).factorial : A)) : ℕ → A → A :=
λ m x, if h : m < n ∧ x ∈ I then (factorial_unit hn_fac h.1).inv * x^m else 0

lemma dpow_if_pos (I : ideal A) {n : ℕ} (hn0 : n ≠ 0)
  (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ} (hm : m < n) {x : A} (hx : x ∈ I) :
  dpow I hn0 hn_fac m x = (factorial_unit hn_fac hm).inv * x^m :=
by simp only [dpow]; rw dif_pos (and.intro hm hx)

lemma dpow_of_nmem (I : ideal A) {n : ℕ} (hn0 : n ≠ 0)
  (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ} {x : A} (hx : x ∉ I) :
  dpow I hn0 hn_fac m x = 0 :=
by simp only [dpow]; rw dif_neg (not_and_of_not_right _ hx)

lemma dpow_of_ge (I : ideal A) {n : ℕ} (hn0 : n ≠ 0)
  (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ} (hm : ¬ m < n) {x : A} :
  dpow I hn0 hn_fac m x = 0 :=
by simp only [dpow]; rw dif_neg (not_and_of_not_left _ hm)

lemma dpow_null {n : ℕ} (hn0 : n ≠ 0)
  (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ} {x : A} (hx : x ∉ I) :
  dpow I hn0 hn_fac m x = 0 := 
by simp only [dpow]; rw [dif_neg (not_and_of_not_right _ hx)]

lemma dpow_mem {n : ℕ} (hn0 : n ≠ 0)
  (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ} (hn : m ≠ 0)
  {x : A} (hx : x ∈ I) : dpow I hn0 hn_fac m x ∈ I := 
begin
  simp only [dpow],
  split_ifs with h,
  { exact ideal.mul_mem_left I _ (ideal.pow_mem_of_mem I hx _ (nat.pos_of_ne_zero hn)) },
  { exact ideal.zero_mem I },
end

lemma dpow_sum {n : ℕ} (hn0 : n ≠ 0)(hn_fac : is_unit ((n-1).factorial : A)) (hnI : I^n = 0)
  (m : ℕ) {x : A} (hx : x ∈ I) {y : A} (hy : y ∈ I) :
  dpow I hn0 hn_fac m (x + y) = (finset.range (m + 1)).sum (λ (k : ℕ), dpow I hn0 hn_fac k x * 
    dpow I hn0 hn_fac (m - k) y) := 
begin
  by_cases hmn : m < n,
  { rw dpow_if_pos I hn0 hn_fac hmn (ideal.add_mem I hx hy),
    simp only [dpow],
    sorry, },
  { sorry }
end

lemma ideal.mem_pow_eq_zero (n m : ℕ) (hnI : I^n = 0) (hmn : n ≤ m) {x : A} (hx : x ∈ I) :
  x ^ m = 0 :=
begin
  have hxn : x^n = 0,
  { rw [ideal.zero_eq_bot] at hnI,
    rw [← ideal.mem_bot, ← hnI],
    exact ideal.pow_mem_pow hx n },
  obtain ⟨c, hc⟩ := nat.exists_eq_add_of_le hmn,
  rw [hc, pow_add, hxn, zero_mul]
end

lemma dpow_mul {n : ℕ} (hn0 : n ≠ 0) (hn_fac : is_unit ((n-1).factorial : A)) (hnI : I^n = 0)
  (m k : ℕ) {x : A} (hx : x ∈ I) :
  dpow I hn0 hn_fac m x * dpow I hn0 hn_fac k x = 
    ↑((k + m).choose m) * dpow I hn0 hn_fac (k + m) x := 
begin
    simp only [dpow],
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8,
    { have h_fac : (factorial_unit hn_fac h1.1).inv * (factorial_unit hn_fac h2.1).inv =
        ↑((k + m).choose m) * (factorial_unit hn_fac h3.1).inv,
        { simp only [units.inv_eq_coe_inv],
          rw [← units.coe_mul, units.eq_mul_inv_iff_mul_eq, ← mul_inv_rev,
            units.inv_mul_eq_iff_eq_mul, factorial_unit_coe, units.coe_mul, factorial_unit_coe,
            factorial_unit_coe],
          norm_cast,
          rw [← nat.add_choose_mul_factorial_mul_factorial, mul_assoc, mul_comm] },
      rw [mul_assoc, ← mul_assoc (x^m), mul_comm (x^m), mul_assoc _ (x^m), ← pow_add,
        ← mul_assoc, ← mul_assoc, add_comm, h_fac], },
    { have hxmk : x ^ (k + m) = 0,
      { simp only [hx, and_true, not_lt] at h3,
        exact ideal.mem_pow_eq_zero n (k + m) hnI h3 hx, },
      rw [mul_assoc, ← mul_assoc (x^m), mul_comm (x^m), mul_assoc _ (x^m), ← pow_add, add_comm, hxmk,
        mul_zero, mul_zero, mul_zero] },
    { exfalso,
      simp only [hx, and_true, not_lt] at h2,
      linarith [h2, h4.1], },
    { rw [mul_zero, mul_zero] },
    { exfalso,
      simp only [hx, and_true, not_lt] at h1,
      linarith [h1, h6.1], },
    { rw [zero_mul, mul_zero] },
    { exfalso,
      simp only [hx, and_true, not_lt] at h1,
      linarith [h1, h7.1], },
    { rw [mul_zero, mul_zero] },
  end

lemma dpow_comp {n : ℕ} (hn0 : n ≠ 0) (hn_fac : is_unit ((n-1).factorial : A)) (hnI : I^n = 0)
  (m : ℕ) {k : ℕ} (hk : k ≠ 0) {x : A} (hx : x ∈ I) :
  dpow I hn0 hn_fac m (dpow I hn0 hn_fac k x) = ↑(mchoose m k) * dpow I hn0 hn_fac (m * k) x :=
begin
    simp only [dpow],
    split_ifs,
    { by_cases hmn : m < n,
      { rw dif_pos,
        { by_cases hmk : m * k < n,
          { have h_fac : (factorial_unit hn_fac hmn).inv * ((factorial_unit hn_fac h.1).inv) ^ m =
              ↑(mchoose m k) * (factorial_unit hn_fac hmk).inv,
            { simp only [units.inv_eq_coe_inv],
          rw [← units.coe_pow, ← units.coe_mul, inv_pow,
            units.eq_mul_inv_iff_mul_eq, ← mul_inv_rev, units.inv_mul_eq_iff_eq_mul, units.coe_mul,
            units.coe_pow, factorial_unit_coe, factorial_unit_coe, factorial_unit_coe,
            ← mchoose_lemma _ (nat.pos_of_ne_zero hk), nat.cast_mul, nat.cast_mul, nat.cast_pow,
            mul_comm ↑m.factorial], },
            rw [dif_pos (and.intro hmk hx), mul_pow, ← pow_mul, mul_comm k, ← mul_assoc,
              ← mul_assoc, h_fac] },
          { rw [dif_neg (not_and_of_not_left _ hmk), mul_pow, ← pow_mul],
            rw [mul_comm, not_lt] at hmk,
            rw [ideal.mem_pow_eq_zero n (k * m) hnI hmk hx, mul_zero, mul_zero, mul_zero] }},
        { refine ⟨hmn, _⟩,
          rw dif_pos h,
          exact ideal.mul_mem_left I _ (ideal.pow_mem_of_mem I hx _ (nat.pos_of_ne_zero hk)) }},      
      { rw dif_neg (not_and_of_not_left _ hmn),
        { rw [dif_neg, mul_zero],
          simp only [hx, and_true, not_lt],
          exact le_trans (not_lt.mp hmn) (nat.le_mul_of_pos_right (nat.pos_of_ne_zero hk)) }}},
    { by_cases hmn : m < n,
      { by_cases hm0 : m = 0,
        { have hmkn : m * k < n,
          { rw [hm0, zero_mul],
            exact nat.pos_of_ne_zero hn0 },
          erw dif_pos (and.intro hmn (dpow_mem hn0 hn_fac hk hx)),
          rw dif_pos (and.intro hmkn hx),
          simp only [hm0, zero_mul, pow_zero, mul_one, mchoose_zero, nat.cast_one, one_mul] },
        { have hmkn : ¬ m * k < n,
          { simp only [hx, and_true, not_lt] at h,
            exact not_lt.mpr (le_trans h (nat.le_mul_of_pos_left (nat.pos_of_ne_zero hm0))) },
          erw dif_pos (and.intro hmn (dpow_mem hn0 hn_fac hk hx)),
          rw [dif_neg (not_and_of_not_left _ hmkn), zero_pow' _ hm0, mul_zero, mul_zero], }},
      { have hmkn : ¬ m * k < n,
        { exact not_lt.mpr (le_trans (not_lt.mp hmn)
            (nat.le_mul_of_pos_right (nat.pos_of_ne_zero hk))) },
        rw [dif_neg (not_and_of_not_left _ hmn), dif_neg (not_and_of_not_left _ hmkn), mul_zero] }}
  end

/-- Proposition 1.2.7 of [B74], part (ii). -/
noncomputable def divided_powers {n : ℕ} (hn0 : n ≠ 0)
  (hn_fac : is_unit ((n-1).factorial : A))
  (hnI : I^n = 0) : divided_powers I := 
{ dpow := dpow I hn0 hn_fac,
  dpow_null := λ n x hx,
  by simp only [dpow]; rw dif_neg (not_and_of_not_right _ hx),
  dpow_zero := λ x hx,
  begin
    simp only [dpow],
    rw [dif_pos (and.intro (nat.pos_of_ne_zero hn0) hx), pow_zero, mul_one, units.inv_eq_coe_inv,
      units.coe_eq_one, inv_eq_one],
    ext,
    rw [factorial_unit_coe, nat.factorial_zero, nat.cast_one, units.coe_one],
  end,
  dpow_one  := λ x hx,
  begin
    simp only [dpow],
    split_ifs with h,
    { rw [pow_one, factorial_inverse_one, one_mul] },
    { simp only [hx, and_true, not_lt] at h,
      have hn1 : n = 1 := le_antisymm h (nat.succ_le_of_lt (nat.pos_of_ne_zero hn0)),
      rw [hn1, pow_one] at hnI,
      rw [hnI, ideal.zero_eq_bot, ideal.mem_bot] at hx,
      exact hx.symm,  },
  end,
  dpow_mem  := λ n hn x hx, dpow_mem hn0 hn_fac hn hx,
  dpow_sum  := λ m x y hx hy, dpow_sum hn0 hn_fac hnI m hx hy,
  dpow_smul := λ m a x hx,
  begin
    simp only [dpow],
    split_ifs with hmax hmx hmx hmax,
    { rw [mul_pow, ← mul_assoc, mul_comm _ (a^m), mul_assoc], },
    { exfalso,
      rw not_and at hmx,
      exact hmx (hmax.1) hx, },
    { exfalso,
      rw [not_and] at hmax,
      exact hmax (hmx.1) (ideal.mul_mem_left I _ hmx.2), },
    { rw mul_zero, }
  end,
  dpow_mul  := λ m k x hx, dpow_mul hn0 hn_fac hnI m k hx,
  dpow_comp := λ m k hk x hx, dpow_comp hn0 hn_fac hnI m hk hx, }

end of_invertible_factorial
#exit
end factorial

--#lint
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
* prove uniqueness
* add rfl lemma that gives analogue of dpow_quot_eq for the divided_powers 
that was just defined 
* maybe other… 
-/

/-- Lemma 3.6 of [BO] (Antoine) -/
lemma span_is_sub_pd_ideal_iff (S : set A) (hS : S ⊆ I) :
  is_sub_pd_ideal hI (ideal.span S) ↔ 
  ∀ (n : ℕ) (hn : 0 < n) (s ∈ S), hI.dpow n s ∈ ideal.span S := 
begin 
  split,
  { -- trivial direction
    intros hhI h hn s hs, 
    apply hhI.dpow_mem_ideal h (ne_of_gt hn) s (ideal.subset_span hs), },
  { -- interesting direction,
    intro hhI,
    have hSI := ideal.span_le.mpr hS,
    apply is_sub_pd_ideal.mk (hSI),
    suffices : ∀ (z : A) (hz : z ∈ ideal.span S),
      z ∈ I ∧ ∀ (n : ℕ), n ≠ 0 → hI.dpow n z ∈ ideal.span S, 
    { intros n hn z hz, 
      exact (this z hz).2 n hn, },
    intros z hz, 
    apply submodule.span_induction hz, 
    { -- case of elements of S 
      intros s hs,
      apply and.intro (hS hs), 
      intros n hn,
      exact hhI n (zero_lt_iff.mpr hn) s hs, },
    { -- case of 0 
      apply and.intro (ideal.zero_mem _),
      intros n hn, rw hI.dpow_eval_zero hn, apply ideal.zero_mem _, },
    { -- case of sum
      rintros x y ⟨hxI, hx⟩ ⟨hyI, hy⟩,
      apply and.intro (ideal.add_mem I hxI hyI),
      intros n hn,
      rw ideal.mem_span, intros J hSJ,
      rw hI.dpow_sum n hxI hyI,
      apply submodule.sum_mem,
      intros m hm,
      cases not_eq_or_aux hn hm with hm hm,
      { apply ideal.mul_mem_right, 
        apply ideal.span_le.mpr hSJ, 
        exact hx m hm,  },
      { apply ideal.mul_mem_left,
        apply ideal.span_le.mpr hSJ,
        exact hy (n - m) hm, }, },
    { -- case : product,
      rintros a x ⟨hxI, hx⟩,
      apply and.intro (submodule.smul_mem I a hxI),
      intros n hn,
      simp only [algebra.id.smul_eq_mul],
      rw hI.dpow_smul n hxI,
      exact ideal.mul_mem_left (ideal.span S) (a ^ n) (hx n hn), }, },
end

/- Questions 

* decide if the hypothesis for (n : ℕ) in dp-lemmas should be `n ≠ 0` or `0 < n`
* should we use • instead of * in `dpow_smul` ?
-/

/- 3.7 Lemma. Suppose R is a ring, В and С are R-algebras, and
I ⊆ В and J ⊆ С are augmentation ideals (i.e. there is a section of В → B/I, etc.) 
with P.D. structures γ and δ, respectively. 
Then the ideal К = Ker (В ⊗ С → B/I ⊗ C/J) has a unique P.D. structure ε 
such that (B,I,γ) → (В ⊗ С,К,ε) and
(C,J,δ) → (B ⊗ C,K,ε) are P.D. morphisms. -/

open_locale tensor_product

/- Lemma 3.7 of [BO] -> Change to 1.7.1 -/
/- TODO:
  * 1.2.7 (María Inés)
  * Given hI, hJ compatible, get divided powers on I + J (1.6.4) 
  * Do 1.6.5
  * Formalize 1.4 (d.p. algebra) -/

def dpow_tensor_product (R B C : Type*) [comm_ring R] [comm_ring B] [comm_ring C]
  [algebra R B] [algebra R C] {I : ideal B} {J : ideal C} (hI : divided_powers I)
  (hJ : divided_powers J) (hIs : function.has_right_inverse (ideal.quotient.mk I))
  (hJs : function.has_right_inverse (ideal.quotient.mk J)) :
  ℕ → (B ⊗[R] C) → (B ⊗[R] C) := sorry

def divided_powers_tensor_product (R B C : Type*) [comm_ring R] [comm_ring B] [comm_ring C]
  [algebra R B] [algebra R C] {I : ideal B} {J : ideal C} (hI : divided_powers I)
  (hJ : divided_powers J) (hIs : function.has_right_inverse (ideal.quotient.mk I))
  (hJs : function.has_right_inverse (ideal.quotient.mk J)) :
  divided_powers (algebra.tensor_product.map (ideal.quotient.mkₐ R I) 
    (ideal.quotient.mkₐ R J)).to_ring_hom.ker  :=
{ dpow := dpow_tensor_product R B C hI hJ hIs hJs,
  dpow_null := sorry,
  dpow_zero := sorry,
  dpow_one  := sorry,
  dpow_mem  := sorry,
  dpow_sum  := sorry,
  dpow_smul := sorry,
  dpow_mul  := sorry,
  dpow_comp := sorry }

lemma divided_powers_tensor_product_unique (R B C : Type*) [comm_ring R] [comm_ring B] [comm_ring C]
  [algebra R B] [algebra R C] {I : ideal B} {J : ideal C} (hI : divided_powers I)
  (hJ : divided_powers J) (hIs : function.has_right_inverse (ideal.quotient.mk I))
  (hJs : function.has_right_inverse (ideal.quotient.mk J)) 
  (hK : divided_powers (algebra.tensor_product.map (ideal.quotient.mkₐ R I) 
  (ideal.quotient.mkₐ R J)).to_ring_hom.ker) :
  hK = (divided_powers_tensor_product R B C hI hJ hIs hJs) :=
begin
  ext n x,
  sorry
end

end sub_pd_ideals



end divided_powers