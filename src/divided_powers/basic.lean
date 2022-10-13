/- ACL and MIdFF, Lean 2022 meeting at Icerm -/
import ring_theory.power_series.basic
import algebra_lemmas
import combinatorics_lemmas

/-! # Divided powers 

Let `A` be a commutative ring and `I` be an ideal of `A`. 
A *divided power* structure on `I` is the datum of operations `div_pow : ℕ → I → A` 
satisfying relations that model the intuitive formula `div_pow n a = a ^ n / n.factorial` and
collected by the structure `divided_powers`.
To avoid coercions, we rather consider `div_pow : ℕ → A → A`, extended by 0.

## References 

* P. Berthelot (1974), *Cohomologie cristalline des schémas de caractéristique $p$ > 0*, 
Lectures notes in mathematics 407, Springer-Verlag.

* P. Berthelot and A. Ogus (1978), *Notes on crystalline cohomology*, 
Princeton University Press.

* N. Roby (1968), *Construction de certaines algèbres à puissances divisées*, 
Bulletin de la Société Mathématique de France, Tome 96, p. 97-113. 
doi: https://doi.org/10.24033/bsmf.1661

* N. Roby (1966), *Sur l'algèbre des puissances divisées d'un module et le module de ses 
différentielles*, Annales scientifiques de l'École Normale Supérieure, Série 3, Tome 83,no. 2, 
p. 75-89. 
doi: https://doi.org/10.24033/asens.1148

-/

section divided_powers_definition

/-- The divided power structure on an ideal I of a commutative ring A -/
@[ext] structure divided_powers {A : Type*} [comm_ring A] (I : ideal A) := 
(dpow : ℕ → A → A)
(dpow_null : ∀ {n x} (hx : x ∉ I), dpow n x = 0)
(dpow_zero : ∀ {x} (hx : x ∈ I), dpow 0 x = 1)
(dpow_one : ∀ {x} (hx : x ∈ I), dpow 1 x = x)
(dpow_mem : ∀ {n} (hn : n ≠ 0) {x} (hx : x ∈ I), dpow n x ∈ I)
(dpow_add : ∀ n {x y} (hx : x ∈ I) (hy : y ∈ I) , dpow n (x + y)
  = finset.sum (finset.range (n + 1)) (λ k, (dpow k x) * (dpow (n - k) y)))
(dpow_smul : ∀ n {a : A} {x} (hx : x ∈ I), dpow n (a * x) = (a ^ n) * (dpow n x))
(dpow_mul : ∀ m n {x} (hx : x ∈ I), (dpow m x) * (dpow n x) = (nat.choose (m+n) m) * dpow (m + n) x)
(dpow_comp : ∀ m {n} (hn : n ≠ 0) {x} (hx : x ∈ I),
  dpow m (dpow n x) = (mchoose m n) * dpow (m * n) x)

instance {A : Type*} [comm_ring A] (I : ideal A) :
  has_coe_to_fun (divided_powers I) (λ _, ℕ → A → A) :=
⟨λ hI, hI.dpow⟩

structure pd_ring (A : Type*) extends comm_ring A := 
(pd_ideal : ideal A)
(divided_powers : divided_powers pd_ideal)

end divided_powers_definition

open_locale classical

namespace divided_powers

section divided_powers_examples

variables {A : Type*} [comm_ring A] {I : ideal A}

def dpow_exp (hI : divided_powers I) (a : A) := power_series.mk (λ n, hI.dpow n a)

lemma add_dpow_exp (hI : divided_powers I) {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
  hI.dpow_exp (a + b) = hI.dpow_exp (a) * hI.dpow_exp (b) :=
begin   
  simp only [dpow_exp],
  ext,
  simp only [power_series.coeff_mk, power_series.coeff_mul],
  rw hI.dpow_add n ha hb,
  rw finset.nat.sum_antidiagonal_eq_sum_range_succ_mk, 
end

lemma eq_of_eq_on_ideal (hI : divided_powers I) (hI' : divided_powers I) 
  (h_eq : ∀ (n : ℕ) {x : A} (hx : x ∈ I), hI.dpow n x = hI'.dpow n x ) :
  hI = hI' :=
begin
  ext n x,
  by_cases hx : x ∈ I,
  { exact h_eq n hx },
  { rw [hI.dpow_null hx, hI'.dpow_null hx] }
end

/- noncomputable
def dpow_of_dpow_exp (I : ideal A) (ε : I → power_series A) : 
  ℕ → A → A := λ n,
  function.extend 
    (λ (a : I), a.val) 
    (λ a, power_series.coeff A n (ε a))
    (λ (a :A) , (0 : A))

def divided_powers_of_dpow_exp (I : ideal A) (ε : I → power_series A)
  (hε_add : ∀ (a b : I), ε(a + b) = ε(a) * ε(b))
  (hε_zero : ε(0) = 1) -/


open_locale big_operators

open finset

variable (hI : divided_powers I)
include hI

/- Rewriting lemmas -/
lemma dpow_smul' (n : ℕ) {a : A} {x : A} (hx : x ∈ I) :
  hI.dpow n (a • x) = (a ^ n) • (hI.dpow n x) :=
by simp only [smul_eq_mul, hI.dpow_smul, hx]

lemma factorial_mul_dpow_eq_pow (n : ℕ) (x : A) (hx : x ∈ I) :
  (n.factorial : A) * (hI.dpow n x) = x^n :=
begin
  induction n with n ih,
  { rw [nat.nat_zero_eq_zero, nat.factorial_zero, nat.cast_one, one_mul, pow_zero,
      hI.dpow_zero hx], },
  { rw [nat.factorial_succ, mul_comm (n + 1), ← (n + 1).choose_one_right,
  ← nat.choose_symm_add, nat.cast_mul, nat.succ_eq_add_one, mul_assoc, 
  ← hI.dpow_mul n 1 hx, ← mul_assoc, ih, hI.dpow_one hx, pow_succ'], }
end

lemma dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : hI.dpow n 0 = 0 := 
begin
  rw [← mul_zero (0 : A), hI.dpow_smul, zero_pow' n hn, zero_mul, zero_mul],
  exact ideal.zero_mem I,
end

end divided_powers_examples

section divided_powers_morphisms

/-- Compatibility of a ring morphism with pd-structures -/
structure is_pd_morphism {A B : Type*} [comm_ring A] [comm_ring B] {I : ideal A} {J : ideal B}
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

open_locale classical

noncomputable def dpow (I : ideal A) :
  ℕ → A → A :=
λ m x, if h : x ∈ I then ring.inverse (m.factorial : A) * x^m else 0

lemma dpow_dif_pos {I : ideal A} (m : ℕ) {x : A} (hx : x ∈ I) :
  dpow I m x = ring.inverse (m.factorial : A) * x^m :=
by simp only [dpow]; rw dif_pos hx

lemma dpow_dif_neg {I : ideal A} {m : ℕ} {x : A} (hx : x ∉ I) : dpow I m x = 0 :=
by simp only [dpow]; rw dif_neg hx

lemma dpow_null {m : ℕ} {x : A} (hx : x ∉ I) : dpow I m x = 0 := 
by simp only [dpow]; rw dif_neg hx

lemma dpow_zero {x : A} (hx : x ∈ I) : dpow I 0 x = 1 :=
begin
  simp only [dpow],
  rw [dif_pos hx, pow_zero, mul_one, nat.factorial_zero, nat.cast_one, ring.inverse_one],
end

lemma dpow_one {x : A} (hx : x ∈ I) :
  dpow I 1 x = x := 
by rw [dpow_dif_pos 1 hx, pow_one, nat.factorial_one, nat.cast_one, ring.inverse_one, one_mul] 


lemma dpow_mem {m : ℕ} (hm : m ≠ 0) {x : A} (hx : x ∈ I) : dpow I m x ∈ I := 
begin
  rw dpow_dif_pos m hx,
  exact ideal.mul_mem_left I _ (ideal.pow_mem_of_mem I hx _ (nat.pos_of_ne_zero hm)) 
end

lemma dpow_add_dif_pos {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ} (hmn : m < n)
  {x y : A} (hx : x ∈ I) (hy : y ∈ I) : dpow I m (x + y) =
  (finset.range (m + 1)).sum (λ (k : ℕ), dpow I k x * dpow I (m - k) y) :=
begin
  rw dpow_dif_pos m (ideal.add_mem I hx hy),
  simp only [dpow],
  rw [ring.inverse_mul_eq_iff_eq_mul _ _ (factorial_is_unit hn_fac hmn), finset.mul_sum, add_pow],
  apply finset.sum_congr rfl,
  intros k hk,
  rw [finset.mem_range, nat.lt_succ_iff] at hk,
  have h_ch : (m.choose k : A) =
    (m.factorial : A) * (ring.inverse (k.factorial)) * (ring.inverse ((m - k).factorial)),
  { have hadd : m = (m - k) + k := (tsub_add_cancel_iff_le.mpr hk).symm,
    rw [ring.eq_mul_inverse_iff_mul_eq  _ _
      (factorial_is_unit hn_fac (lt_of_le_of_lt (nat.sub_le m k) hmn)),
      ring.eq_mul_inverse_iff_mul_eq  _ _ (factorial_is_unit hn_fac  (lt_of_le_of_lt hk hmn))],
    nth_rewrite 0 hadd,
    nth_rewrite 2 hadd,
    rw [← nat.cast_mul, ← nat.cast_mul, nat.add_choose_mul_factorial_mul_factorial],},
    rw [dif_pos hx, dif_pos hy, h_ch, ← mul_assoc, ← mul_assoc, mul_comm
      (ring.inverse ↑((m - k).factorial))  (y ^ (m - k)), mul_assoc _ (x^k), ← mul_assoc (x^k),
      mul_comm (x ^ k * y ^ (m - k)) (ring.inverse ↑((m - k).factorial))],
    ring_nf,
end

lemma dpow_add {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) (hnI : I^n = 0) (m : ℕ) {x : A}
  (hx : x ∈ I) {y : A} (hy : y ∈ I) : dpow I m (x + y) =
    (finset.range (m + 1)).sum (λ (k : ℕ), dpow I k x * dpow I (m - k) y) := 
begin
  by_cases hmn : m < n,
  { exact dpow_add_dif_pos hn_fac hmn hx hy },
  { have h_sub : I^m ≤ I^n := ideal.pow_le_pow (not_lt.mp hmn),
    rw dpow_dif_pos m (ideal.add_mem I hx hy),
    simp only [dpow], 
    have hxy : (x + y) ^ m = 0,
    { rw [← ideal.mem_bot, ← ideal.zero_eq_bot, ← hnI],
      apply set.mem_of_subset_of_mem h_sub
        (ideal.pow_mem_pow (ideal.add_mem I hx hy) m) },
    rw [hxy, mul_zero, eq_comm],
    apply finset.sum_eq_zero,
    intros k hk,
    rw [dif_pos hx, dif_pos hy, mul_assoc, mul_comm (x^k), mul_assoc, ← mul_assoc],
    apply mul_eq_zero_of_right,
    rw [← ideal.mem_bot, ← ideal.zero_eq_bot, ← hnI],
    have hIm : y ^ (m - k) * x ^ k ∈ I ^ m,
    { have hadd : m = (m - k) + k,
      { rw [eq_comm, tsub_add_cancel_iff_le],
        exact nat.le_of_lt_succ (finset.mem_range.mp hk) },
      nth_rewrite 1 hadd,
      rw pow_add,
      exact ideal.mul_mem_mul (ideal.pow_mem_pow hy _) (ideal.pow_mem_pow hx _) },
    apply set.mem_of_subset_of_mem h_sub hIm }
end

lemma dpow_smul (m : ℕ) {a x : A} (hx : x ∈ I) :
  dpow I m (a * x) = a ^ m * dpow I m x :=
by rw [dpow_dif_pos m (ideal.mul_mem_left I _ hx), dpow_dif_pos m hx, mul_pow,
    ← mul_assoc, mul_comm _ (a^m), mul_assoc]


lemma dpow_mul_dif_pos {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m k : ℕ} (hkm : m + k < n) 
  {x : A} (hx : x ∈ I) :
  dpow I m x * dpow I k x = ↑((m + k).choose m) * dpow I (m + k) x := 
begin
  have hm : m < n := lt_of_le_of_lt le_self_add hkm,
  have hk : k < n := lt_of_le_of_lt le_add_self hkm,
  have h_fac : (ring.inverse (m.factorial : A)) * (ring.inverse k.factorial) =
    ↑((m + k).choose m) * (ring.inverse (m + k).factorial),
  { rw [ring.eq_mul_inverse_iff_mul_eq _ _ (factorial_is_unit hn_fac hkm), mul_assoc,
    ring.inverse_mul_eq_iff_eq_mul _ _ (factorial_is_unit hn_fac hm),
      ring.inverse_mul_eq_iff_eq_mul _ _ (factorial_is_unit hn_fac hk)],
    norm_cast, apply congr_arg,
    rw [← nat.add_choose_mul_factorial_mul_factorial, mul_comm, mul_comm _ m.factorial, 
      nat.choose_symm_add] },
    rw [dpow_dif_pos _ hx, dpow_dif_pos _ hx, dpow_dif_pos _ hx, mul_assoc,
       ← mul_assoc (x^m), mul_comm (x^m), mul_assoc _ (x^m), ← pow_add, ← mul_assoc, 
       ← mul_assoc, h_fac],
end

lemma dpow_mul {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) (hnI : I^n = 0) (m k : ℕ) {x : A}
  (hx : x ∈ I) :
  dpow I m x * dpow I k x = ↑((m + k).choose m) * dpow I (m + k) x := 
begin
  by_cases hkm : m + k < n,
  { exact dpow_mul_dif_pos hn_fac hkm hx, },
  { have hxmk : x ^ (m + k) = 0,
    { exact ideal.mem_pow_eq_zero n (m + k) hnI (not_lt.mp hkm) hx },
    rw [dpow_dif_pos m hx, dpow_dif_pos k hx, dpow_dif_pos (m + k) hx, mul_assoc, ← mul_assoc (x^m),
      mul_comm (x^m), mul_assoc _ (x^m), ← pow_add, hxmk, mul_zero, mul_zero, mul_zero, mul_zero] }
end

lemma dpow_comp_dif_pos {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) 
  {m k : ℕ} (hk : k ≠ 0) (hkm : m * k < n) {x : A} (hx : x ∈ I) :
  dpow I m (dpow I k x) = ↑(mchoose m k) * dpow I (m * k) x := 
begin
  have hmn : m < n,
  { exact lt_of_le_of_lt (nat.le_mul_of_pos_right (nat.pos_of_ne_zero hk)) hkm },
  rw [dpow_dif_pos  (m *k) hx, dpow_dif_pos _ (dpow_mem hk hx)],
  by_cases hm0 : m = 0,
  { simp only [hm0, zero_mul, pow_zero, mul_one, mchoose_zero, nat.cast_one, one_mul] },
  { have hkn : k < n,
    { exact lt_of_le_of_lt (nat.le_mul_of_pos_left (nat.pos_of_ne_zero hm0)) hkm },
    rw dpow_dif_pos _ hx,
    have h_fac : (ring.inverse (m.factorial : A)) * (ring.inverse k.factorial) ^ m =
      ↑(mchoose m k) * (ring.inverse (m*k).factorial),
    { rw [ring.eq_mul_inverse_iff_mul_eq _ _ (factorial_is_unit hn_fac hkm), mul_assoc,
        ring.inverse_mul_eq_iff_eq_mul  _ _ (factorial_is_unit hn_fac hmn)],
      rw ring.inverse_pow_mul_eq_iff_eq_mul _ _ (factorial_is_unit hn_fac hkn),
      rw [← mchoose_lemma _ hk,
        nat.cast_mul, nat.cast_mul, nat.cast_pow, mul_comm ↑m.factorial, mul_assoc] },
    rw [ mul_pow, ← pow_mul, mul_comm k, ← mul_assoc, ← mul_assoc, h_fac] },
end

lemma dpow_comp {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) (hnI : I^n = 0)
  (m : ℕ) {k : ℕ} (hk : k ≠ 0) {x : A} (hx : x ∈ I) :
  dpow I m (dpow I k x) = ↑(mchoose m k) * dpow I (m * k) x :=
begin
  by_cases hmk : m * k < n,
  { exact dpow_comp_dif_pos hn_fac hk hmk hx },
  { have hxmk : x ^ (m * k) = 0,
    { exact ideal.mem_pow_eq_zero n (m * k) hnI (not_lt.mp hmk) hx },
    rw [dpow_dif_pos _ (dpow_mem hk hx), dpow_dif_pos _ hx, dpow_dif_pos _ hx, mul_pow, ← pow_mul,
      ← mul_assoc, mul_comm k, hxmk, mul_zero, mul_zero, mul_zero] }
end

/-- Proposition 1.2.7 of [B74], part (ii). -/
noncomputable def divided_powers {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) (hnI : I^n = 0) :
  divided_powers I := 
{ dpow      := dpow I,
  dpow_null := λ n x hx, dpow_null hx,
  dpow_zero := λ x hx, dpow_zero hx,
  dpow_one  := λ x hx, dpow_one hx,
  dpow_mem  := λ n hn x hx, dpow_mem hn hx,
  dpow_add  := λ m x y hx hy, dpow_add hn_fac hnI m hx hy,
  dpow_smul := λ m a x hx, dpow_smul m hx,
  dpow_mul  := λ m k x hx, dpow_mul hn_fac hnI m k hx,
  dpow_comp := λ m k hk x hx, dpow_comp hn_fac hnI m hk hx }

end of_invertible_factorial

end factorial

-- Instead of 1.2.1, I formalize example 2 from [BO], Section 3.
namespace Q_algebra

variables {R : Type*} [comm_ring R] 

lemma factorial.is_unit [algebra ℚ R] (n : ℕ) : is_unit (n.factorial : R) :=
begin
  have hn : (n.factorial : R) = algebra_map ℚ R n.factorial,
  { rw [map_nat_cast] },
  rw hn,
  apply is_unit.map,
  exact is_unit_iff_ne_zero.mpr (nat.cast_ne_zero.mpr (nat.factorial_ne_zero n)),
end

variable (I : ideal R) 

noncomputable def dpow : ℕ → R → R :=
λ n, of_invertible_factorial.dpow I n

variable {I}
-- We may not need this, but I'll leave it here for now
lemma dpow_def (n : ℕ) {x : R} (hx : x ∈ I) : 
  dpow I n x = (ring.inverse n.factorial) * x^n :=
by simp only [dpow]; rw of_invertible_factorial.dpow_dif_pos _ hx

variable [algebra ℚ R]

variable (I)

noncomputable def rat_algebra_divided_powers : divided_powers I := 
{ dpow      := dpow I,
  dpow_null := λ n x hx, of_invertible_factorial.dpow_null hx,
  dpow_zero := λ x hx, of_invertible_factorial.dpow_zero hx,
  dpow_one  := λ x hx, of_invertible_factorial.dpow_one hx,
  dpow_mem  := λ n hn x hx, of_invertible_factorial.dpow_mem hn hx,
  dpow_add  := λ n x y hx hy, of_invertible_factorial.dpow_add_dif_pos
                 (factorial.is_unit (n + 1 - 1)) (n.lt_succ_self) hx hy,
  dpow_smul := λ n a x hx, of_invertible_factorial.dpow_smul n hx,
  dpow_mul  := λ m k x hx, of_invertible_factorial.dpow_mul_dif_pos
                 (factorial.is_unit (m + k + 1 - 1)) (m + k).lt_succ_self hx,
  dpow_comp := λ m k hk x hx, of_invertible_factorial.dpow_comp_dif_pos
                 (factorial.is_unit (m * k + 1 - 1)) hk (lt_add_one _) hx }

lemma rat_algebra_divided_powers_dpow_apply (n : ℕ) (x : R) : 
  (rat_algebra_divided_powers I).dpow n x = dpow I n x :=
rfl

variable {I}

-- There are no other divided power structures on a ℚ-algebra.
lemma divided_powers_Q_algebra_unique (hI : divided_powers I) :
  hI = (rat_algebra_divided_powers I) :=
begin
  apply eq_of_eq_on_ideal, 
  intros n x hx,
  have hn : is_unit (n.factorial : R) := factorial.is_unit n,
    rw [rat_algebra_divided_powers_dpow_apply, dpow_def n hx, eq_comm,
      ring.inverse_mul_eq_iff_eq_mul _ _ hn, factorial_mul_dpow_eq_pow _ _ _ hx]
end

end Q_algebra

/-- If J is another ideal of A with divided powers, 
then the divided powers of I and J coincide on I • J 
(Berthelot, 1.6.1 (ii))-/
lemma coincide_on_smul  {A : Type*} [comm_ring A] {I : ideal A} (hI : divided_powers I) 
  {J : ideal A} (hJ : divided_powers J) : 
∀ {n} (a ∈ I • J), hI.dpow n a = hJ.dpow n a :=
begin
  intros n a ha,
  revert  n,
  apply submodule.smul_induction_on' ha,
  { intros a ha b hb n, 
    simp only [algebra.id.smul_eq_mul], 
    rw hJ.dpow_smul n hb,
    rw mul_comm a b, rw hI.dpow_smul n ha, 
    rw ← hJ.factorial_mul_dpow_eq_pow n b hb,
    rw ← hI.factorial_mul_dpow_eq_pow n a ha,
    ring, },
  { intros x hx y hy hx' hy' n, 
    rw hI.dpow_add n (ideal.mul_le_right hx) (ideal.mul_le_right hy), 
    rw hJ.dpow_add n (ideal.mul_le_left hx) (ideal.mul_le_left hy), 
    apply finset.sum_congr rfl,
    intros k hk,
    rw hx', rw hy', },
end


end divided_powers

/- Comparison with Berthelot, Coho. cristalline

1.1 : done
1.2.1 : follows from 1.2.7 - done (for ℚ-algebras).
1.2.2 (*) : To be added
1.2.4 : To be added if Cohen/Witt vectors rings exist
1.2.7 (M) : done
1.3 (pd -morphism) : done
1.3.1 : To be added (needs limits of rings)

1.4 : To be added, but difficult
1.5.: depends on 1.4  

1.6 : sub-pd-ideal : done
1.6.1 Done !
1.6.2 : Done : dpow_quot]
1.6.4 (A) : to be added
(should we add the remark on page 33)
1.6.5 (A): to be added

1.7 : tensor product, see Roby

1.8 (M). Done! 


PRs : 
 (M) : ring_inverse, tsub_tsub - DONE
 (A) : submodule_induction, function.extend_apply_first - DONE

Delete obsolete versions
 (A) : rewrite_4_sums

(A) Simplify, remove not_eq_or_aux (see REMOVE or MOVE)
  Prove uniqueness of pd-structure when possible
    (ideal_add, dpow_quot)
(M) Complete the lattice structure

-/