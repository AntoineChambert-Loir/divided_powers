/- Copyright ACL and MIdFF -/

-- import algebra.ring
import ring_theory.ideal.basic

/-! # Divided powers 


-/


/-- Number of possibilities of choosing m groups of n-element subsets out of mn elements -/
def mchoose (m n : ℕ) : ℕ := finset.prod (finset.range m) (λ p, nat.choose (p * n + n - 1) (n - 1))

lemma mchoose_zero (n : ℕ) : mchoose 0 n = 1 := 
begin
  rw mchoose, simp, 
end

lemma mchoose_succ (m n : ℕ) : mchoose (m + 1) n = (nat.choose (m * n + n - 1) (n - 1)) * (mchoose m n) := 
begin
  simp [mchoose],
  rw finset.prod_range_succ, 
  simp, 
  rw mul_comm, 
end

lemma mchoose_lemma (m n : ℕ) (hn : 1 ≤ n): (m.factorial) * (n.factorial) ^m * (mchoose m n) = (m * n).factorial :=
begin
  induction m with m ih, 
  simp only [nat.nat_zero_eq_zero, nat.factorial_zero, pow_zero, one_mul, zero_mul], apply mchoose_zero, 
  simp only [nat.factorial_succ], rw [mchoose_succ, pow_succ],
  simp only [←mul_assoc],
  conv_rhs { rw nat.succ_mul},
  rw ← nat.add_choose_mul_factorial_mul_factorial,
  rw ← ih,
  suffices : (m + 1) * (m * n + n - 1).choose (n - 1)
    = (m * n + n).choose n,
  rw ← this,
  ring_nf,

  suffices : 0 < (m * n).factorial * n.factorial,
  rw ← nat.mul_left_inj this, 
  simp only [←mul_assoc],
  rw nat.add_choose_mul_factorial_mul_factorial,
  rw ← nat.mul_factorial_pred hn,
  rw mul_comm n _, 
  rw ← mul_assoc,
  suffices this : m * n + n - 1 =  m * n + (n - 1),
  { rw this,
    simp only [mul_assoc], rw mul_comm, 
    simp  only [← mul_assoc],
    rw nat.add_choose_mul_factorial_mul_factorial,
    suffices also_this : 0 < m * n + n,
    { rw ← nat.mul_factorial_pred  also_this, 
      rw ← this, 
      ring },
    apply nat.add_pos_right _ hn, },
  exact nat.add_sub_assoc hn (m * n),

  apply nat.mul_pos;
  apply nat.factorial_pos
end

/-- The divided power structure on an ideal I of a commutative ring A -/
structure has_divided_powers (A : Type*) [comm_ring A] (I : ideal A) := 
(dpow : ℕ → I → A)
(dpow_zero : dpow 0 = 1)
(dpow_one : dpow 1 = coe)
(dpow_mem : ∀ (n : ℕ) (x : I), 1 ≤ n → dpow n x ∈ I)
(dpow_sum : ∀ (n : ℕ) (x y : I), dpow n (x + y)
  = finset.sum (finset.range (n + 1)) (λ k, (dpow k x) * (dpow (n - k) y)))
(dpow_smul : ∀ (n : ℕ) (a : A) (x : I), dpow n (a • x) = (a ^ n) * (dpow n x))
(dpow_mul : ∀ (m n : ℕ) (x : I), (dpow m x) * (dpow n x) = (nat.choose (n+m) m) * dpow (m + n) x)
(dpow_comp : ∀ (m n : ℕ) (hn : 1 ≤ n) (x : I),
  dpow m (⟨dpow n x, dpow_mem n x hn⟩) = (mchoose m n) * dpow (m * n) x)

class divided_power_ring (A : Type*) extends comm_ring A:= 
(pd_ideal : ideal A)
(dpow : ℕ → pd_ideal → A)
(dpow_zero : dpow 0 = 1)
(dpow_one : dpow 1 = coe)
(dpow_mem : ∀ (n : ℕ) (x : pd_ideal), 1 ≤ n → dpow n x ∈ pd_ideal)
(dpow_sum : ∀ (n : ℕ) (x y : pd_ideal), dpow n (x + y)
  = finset.sum (finset.range (n + 1)) (λ k, (dpow k x) * (dpow (n - k) y)))
(dpow_smul : ∀ (n : ℕ) (a : A) (x : pd_ideal), dpow n (a • x) = (a ^ n) * (dpow n x))
(dpow_mul : ∀ (m n : ℕ) (x : pd_ideal), (dpow m x) * (dpow n x) = (nat.choose (n+m) m) * dpow (m + n) x)
(dpow_comp : ∀ (m n : ℕ) (hn : 1 ≤ n) (x : pd_ideal),
  dpow m (⟨dpow n x, dpow_mem n x hn⟩) = (mchoose m n) * dpow (m * n) x)


structure is_pd_morphism {A B : Type*} [hA : divided_power_ring A] [hB : divided_power_ring B] (f : A →+* B) :=
(ideal_comp : ∀ (a : hA.pd_ideal), f a ∈ hB.pd_ideal)
(dpow_comp : ∀ (n : ℕ) (a : hA.pd_ideal), 
divided_power_ring.dpow n (⟨f a, ideal_comp a⟩) = f (divided_power_ring.dpow n a))


#print has_divided_powers

#lint