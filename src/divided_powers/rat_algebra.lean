import algebra_lemmas
import divided_powers.basic

namespace divided_powers

namespace of_invertible_factorial

variables {A : Type*} [comm_ring A] {I : ideal A}

open_locale classical

noncomputable def dpow (I : ideal A) : ℕ → A → A :=
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
  rw [ring.inverse_mul_eq_iff_eq_mul _ _ _ (factorial_is_unit hn_fac hmn), finset.mul_sum, add_pow],
  apply finset.sum_congr rfl,
  intros k hk,
  rw [finset.mem_range, nat.lt_succ_iff] at hk,
  have h_ch : (m.choose k : A) =
    (m.factorial : A) * (ring.inverse (k.factorial)) * (ring.inverse ((m - k).factorial)),
  { have hadd : m = (m - k) + k := (tsub_add_cancel_iff_le.mpr hk).symm,
    rw [ring.eq_mul_inverse_iff_mul_eq _ _ _
      (factorial_is_unit hn_fac (lt_of_le_of_lt (nat.sub_le m k) hmn)),
      ring.eq_mul_inverse_iff_mul_eq  _ _ _ (factorial_is_unit hn_fac  (lt_of_le_of_lt hk hmn))],
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
  { rw [ring.eq_mul_inverse_iff_mul_eq _ _ _ (factorial_is_unit hn_fac hkm), mul_assoc,
    ring.inverse_mul_eq_iff_eq_mul _ _ _ (factorial_is_unit hn_fac hm),
      ring.inverse_mul_eq_iff_eq_mul _ _ _ (factorial_is_unit hn_fac hk)],
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
    { rw [ring.eq_mul_inverse_iff_mul_eq _ _ _ (factorial_is_unit hn_fac hkm), mul_assoc,
        ring.inverse_mul_eq_iff_eq_mul  _ _ _ (factorial_is_unit hn_fac hmn)],
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

namespace of_square_zero

variables {A : Type*} [comm_ring A] {I : ideal A} (hI2 : I^2 = 0)

noncomputable def divided_powers  :
  divided_powers I := of_invertible_factorial.divided_powers (by simp) hI2

-- TODO: generalize to I^p = 0 in a ring A with prime characteristic p

/- -- Keep ?
lemma dpow_one (a : A) [decidable (a ∈ I)]:
  (divided_powers hI2) 1 a = ite (a ∈ I) a 0 :=
begin
  split_ifs with ha,
  exact dpow_one _ ha,
  exact dpow_null _ ha, 
end -/

lemma dpow_of_two_le {n : ℕ} (hn : 2 ≤ n) (a : A) : 
  (divided_powers hI2) n a = 0 := 
begin
  dsimp [divided_powers, of_invertible_factorial.divided_powers, of_invertible_factorial.dpow], 
  rw coe_to_fun_apply,
  simp only,
  split_ifs with ha, convert mul_zero _,
  exact ideal.mem_pow_eq_zero 2 n hI2 hn ha,
  refl,
end

end of_square_zero

-- Instead of 1.2.1, I formalize example 2 from [BO], Section 3.
namespace rat_algebra

variables {R : Type*} [comm_ring R] (I : ideal R) 

noncomputable def dpow : ℕ → R → R :=
λ n, of_invertible_factorial.dpow I n

variable {I}
-- We may not need this, but I'll leave it here for now
lemma dpow_def (n : ℕ) {x : R} (hx : x ∈ I) : 
  dpow I n x = (ring.inverse n.factorial) * x^n :=
by simp only [dpow]; rw of_invertible_factorial.dpow_dif_pos _ hx

variable [algebra ℚ R]

variable (I)

noncomputable def divided_powers : divided_powers I := 
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

lemma divided_powers_dpow_apply (n : ℕ) (x : R) : 
  (divided_powers I).dpow n x = dpow I n x :=
rfl

variable {I}

-- There are no other divided power structures on a ℚ-algebra.
lemma divided_powers_unique (hI : _root_.divided_powers I) :
  hI = (divided_powers I) :=
begin
  apply eq_of_eq_on_ideal, 
  intros n x hx,
  have hn : is_unit (n.factorial : R) := factorial.is_unit n,
    rw [divided_powers_dpow_apply, dpow_def n hx, eq_comm,
      ring.inverse_mul_eq_iff_eq_mul _ _ _ hn, factorial_mul_dpow_eq_pow _ _ _ hx]
end

end rat_algebra

end divided_powers