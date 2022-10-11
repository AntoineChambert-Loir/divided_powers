/- Copyright ACL and MIdFF -/

-- import algebra.ring
import divided_powers.basic

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


variables {A : Type*} [comm_ring A] [hA: divided_power_ring A] [hA': divided_power_ring A]

--notation `(` A `,` I, `,` hI `)` →ₚ  `(` B `,` J, `,` hJ `)` := pd_morphism hI hJ

structure is_pd_morphism' {A B : Type*} [hA : divided_power_ring A] [hB : divided_power_ring B]
  (f : A →+* B) :=
(ideal_comp : ∀ (a : hA.pd_ideal), f a ∈ hB.pd_ideal)
(dpow_comp : ∀ (n : ℕ) (a : hA.pd_ideal),
  divided_power_ring.dpow n (⟨f a, ideal_comp a⟩) = f (divided_power_ring.dpow n a))
