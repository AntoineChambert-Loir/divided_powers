/- Copyright ACL and MIdFF -/

import ring_theory.ideal.operations
import ring_theory.ideal.quotient

/-! # Divided powers 


-/


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

/-- The divided power structure on an ideal I of a commutative ring A -/
structure divided_powers {A : Type*} [comm_ring A] {I : ideal A} (dpow : ℕ → I → A) : Prop := 
(dpow_zero : dpow 0 = 1)
(dpow_one : dpow 1 = coe)
(dpow_mem : ∀ (n : ℕ) (x : I), 1 ≤ n → dpow n x ∈ I)
(dpow_sum : ∀ (n : ℕ) (x y : I), dpow n (x + y)
  = finset.sum (finset.range (n + 1)) (λ k, (dpow k x) * (dpow (n - k) y)))
(dpow_smul : ∀ (n : ℕ) (a : A) (x : I), dpow n (a • x) = (a ^ n) * (dpow n x))
(dpow_mul : ∀ (m n : ℕ) (x : I), (dpow m x) * (dpow n x) = (nat.choose (n+m) m) * dpow (n + m) x)
(dpow_comp : ∀ (m n : ℕ) (hn : 1 ≤ n) (x : I),
  dpow m (⟨dpow n x, dpow_mem n x hn⟩) = (mchoose m n) * dpow (m * n) x)

namespace divided_powers
variables {A : Type*} [comm_ring A] {I : ideal A} (dpow : ℕ → I → A) (hI : divided_powers dpow)
include hI

lemma factorial_mul_dpow_eq_pow (n : ℕ) (x : I) : (n.factorial : A) * (dpow n x) = x^n :=
begin
  induction n with n ih,
  { rw [pow_zero, nat.factorial_zero, nat.cast_one, one_mul, hI.dpow_zero, pi.one_apply] },
  { rw [nat.factorial_succ, mul_comm (n + 1), nat.cast_mul, mul_assoc, pow_succ', ← ih, mul_assoc,
      ← (n + 1).choose_one_right, nat.succ_eq_add_one, ← hI.dpow_mul, hI.dpow_one,
      mul_comm (x : A)], }
end

lemma dpow_eval_zero {n : ℕ} (hn : 0 < n) : dpow n 0 = 0 := 
by rw [← smul_zero (0 : A), hI.dpow_smul, zero_pow hn, zero_mul]

structure is_pd_morphism {A B : Type*} [comm_ring A] [comm_ring B] (I : ideal A) (J : ideal B )
  (dpow_I : ℕ → I → A) (dpow_J : ℕ → J → B)
  (hI : divided_powers dpow_I) (hJ : divided_powers dpow_J) (f : A →+* B) :=
(ideal_comp : ∀ (a : I), f a ∈ J)
(dpow_comp : ∀ (n : ℕ) (a : I), dpow_J n (⟨f a, ideal_comp a⟩) = f (dpow_I n a))

structure pd_morphism {A B : Type*} [comm_ring A] [comm_ring B] {I : ideal A} {J : ideal B }
  (dpow_I : ℕ → I → A) (dpow_J : ℕ → J → B) (hI : divided_powers dpow_I)
  (hJ : divided_powers dpow_J) :=
(to_ring_hom : A →+* B)
(ideal_comp : ∀ (a : I), to_ring_hom a ∈ J)
(dpow_comp : ∀ (n : ℕ) (a : I), 
  dpow_J n (⟨to_ring_hom a, ideal_comp a⟩) = to_ring_hom (dpow_I n a))

--notation `(` A `,` I, `,` hI `)` →ₚ  `(` B `,` J, `,` hJ `)` := pd_morphism hI hJ

structure is_sub_pd_ideal (J : ideal A) : Prop :=
(is_sub_ideal : ∀ j : J, (j : A) ∈ I)
(dpow_mem_ideal : ∀ (n : ℕ) (hn : 0 < n) (j : J), dpow n ⟨j, is_sub_ideal j⟩ ∈ J )

def quot.has_divided_powers (J : ideal A) (hIJ : is_sub_pd_ideal dpow hI (I ⊓ J)) :
  ∃ (dpow_quot : ℕ → (I.map (ideal.quotient.mk J)) → (A ⧸ J)), divided_powers dpow_quot ↔
  false := sorry

lemma is_sub_pd_ideal_iff (S : set A) (hS : S ⊆ I) :
  is_sub_pd_ideal dpow hI (ideal.span S) ↔ 
  ∀ (n : ℕ) (hn : 0 < n) (s : S), dpow n ⟨s, hS s.property⟩ ∈ ideal.span S :=
sorry

end divided_powers