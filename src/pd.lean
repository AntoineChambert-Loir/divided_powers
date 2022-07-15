/- Copyright ACL and MIdFF -/

import ring_theory.ideal.operations
import ring_theory.ideal.quotient

/-! # Divided powers 

Let `A` be a commutative ring and `I` be an ideal of `A`. A *divided power* structure on `I`
is the datum of operations `div_pow : ℕ → I → A` satisfying relations that model the 
intuitive formula `div_pow n a = a ^ n / n.factorial` and collected by the structure `divided_powers`.





## References 

* P. Berthelot (1974), *Cohomologie cristalline des schémas de caractéristique $p$ > 0*, 
Lectures notes in mathematics 407, Springer-Verlag.

* P. Berthelot and A. Ogus (1978), *Notes on crystalline cohomology*, 
Princeton University Press.

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
(dpow_zero : ∀ (x : I), dpow 0 x = 1)
(dpow_one : ∀ (x : I), dpow 1 x = x)
(dpow_mem : ∀ (n : ℕ) (x : I), 1 ≤ n → dpow n x ∈ I)
(dpow_sum : ∀ (n : ℕ) (x y : I), dpow n (x + y)
  = finset.sum (finset.range (n + 1)) (λ k, (dpow k x) * (dpow (n - k) y)))
(dpow_smul : ∀ (n : ℕ) (a : A) (x : I), dpow n (a • x) = (a ^ n) * (dpow n x))
(dpow_mul : ∀ (m n : ℕ) (x : I), (dpow m x) * (dpow n x) = (nat.choose (n+m) m) * dpow (n + m) x)
(dpow_comp : ∀ (m n : ℕ) (hn : 1 ≤ n) (x : I),
  dpow m (⟨dpow n x, dpow_mem n x hn⟩) = (mchoose m n) * dpow (m * n) x)

namespace divided_powers
variables {A : Type*} [comm_ring A] {I : ideal A} {dpow : ℕ → I → A} (hI : divided_powers dpow)
include hI

lemma factorial_mul_dpow_eq_pow (n : ℕ) (x : I) : (n.factorial : A) * (dpow n x) = x^n :=
begin
  induction n with n ih,
  { rw [pow_zero, nat.factorial_zero, nat.cast_one, one_mul, hI.dpow_zero] },
  { rw [nat.factorial_succ, mul_comm (n + 1), nat.cast_mul, mul_assoc, pow_succ', ← ih, mul_assoc,
      ← (n + 1).choose_one_right, nat.succ_eq_add_one, ← hI.dpow_mul, hI.dpow_one,
      mul_comm (x : A)], }
end

lemma dpow_eval_zero {n : ℕ} (hn : 0 < n) : dpow n 0 = 0 := 
by rw [← smul_zero (0 : A), hI.dpow_smul, zero_pow hn, zero_mul]

/-- Compatibility of a ring morphism with pd-structures -/
structure is_pd_morphism {A B : Type*} [comm_ring A] [comm_ring B] (I : ideal A) (J : ideal B )
  (dpow_I : ℕ → I → A) (dpow_J : ℕ → J → B)
  (hI : divided_powers dpow_I) (hJ : divided_powers dpow_J) (f : A →+* B) :=
(ideal_comp : ∀ (a : I), f a ∈ J)
(dpow_comp : ∀ (n : ℕ) (a : I), dpow_J n (⟨f a, ideal_comp a⟩) = f (dpow_I n a))

/-- The structure of a pd_morphism between rings endowed with pd-rings -/
structure pd_morphism {A B : Type*} [comm_ring A] [comm_ring B] {I : ideal A} {J : ideal B }
  (dpow_I : ℕ → I → A) (dpow_J : ℕ → J → B) (hI : divided_powers dpow_I)
  (hJ : divided_powers dpow_J) :=
(to_ring_hom : A →+* B)
(ideal_comp : ∀ (a : I), to_ring_hom a ∈ J)
(dpow_comp : ∀ (n : ℕ) (a : I), 
  dpow_J n (⟨to_ring_hom a, ideal_comp a⟩) = to_ring_hom (dpow_I n a))

-- For the moment, the notation does not work
--notation `(` A `,` I, `,` hI `)` →ₚ  `(` B `,` J, `,` hJ `)` := pd_morphism hI hJ

/-- The structure of a sub-pd-ideal of a pd-ideal -/
structure is_sub_pd_ideal (J : ideal A) : Prop :=
(is_sub_ideal : ∀ j : J, (j : A) ∈ I)
(dpow_mem_ideal' : ∀ (n : ℕ) (hn : 1 ≤ n) (j : I) (hj : ↑j ∈ J), dpow n j ∈ J )

/- There are two possible ways of phrasing the compatibility condition, 
we had first used `dpow_mem_ideal`,  but it seems easier to use `dpow_mem_ideal'`.
The following lemma makes the translation.  -/
lemma is_sub_pd_ideal.dpow_mem_ideal (J : ideal A) (hIJ : is_sub_pd_ideal hI J) 
  (n : ℕ) (hn : 1 ≤ n) (j : J) : dpow n ⟨↑j, hIJ.is_sub_ideal j⟩ ∈ J := 
begin
  convert hIJ.dpow_mem_ideal' n hn _ _,
  simp only [submodule.coe_mk, submodule.coe_mem],
end

/- If we needed to go in the other direction, we would require this -/
example (J : ideal A) (hIJ : is_sub_pd_ideal hI J) 
  (n : ℕ) (hn : 1 ≤ n) (j : I) (hj : ↑j ∈ J) : dpow n j ∈ J :=
begin
  have : j = ⟨(⟨↑j, hj⟩ : J), hIJ.is_sub_ideal ⟨↑j, hj⟩⟩, 
  by simp only [submodule.coe_mk, set_like.eta],
  rw this,
  apply  is_sub_pd_ideal.dpow_mem_ideal hI J hIJ n hn,
end


lemma dpow_quot_aux (J : ideal A) (hIJ : is_sub_pd_ideal hI (J ⊓ I)) : 
  ∀ (n : ℕ) (a b : I) (hab : (b : A) - (a : A) ∈ J), dpow n b - dpow n a ∈ J := 
begin
  intros n a b hab,
  have hb : b = a + (b - a), by rw [add_comm, sub_add_cancel],
  rw hb,
  rw hI.dpow_sum, 
  rw finset.range_succ, 
  rw finset.sum_insert (finset.not_mem_range_self),
  simp only [tsub_self, hI.dpow_zero, mul_one, add_sub_cancel'], 
  apply ideal.sum_mem ,
  intros i hi, 
  simp only [finset.mem_range] at hi,
  apply J.smul_mem,
  apply semilattice_inf.inf_le_left J I,
  apply hIJ.dpow_mem_ideal' (n - i) (nat.sub_pos_of_lt hi), 
  split,
    simp only [add_subgroup_class.coe_sub], exact hab,
    exact (b - a).prop, 
end

-- We wish a better API to denote I.map (ideal.quotient.mk J) as I ⧸ J 
/-- When `I ⊓ J` is a `sub_pd_ideal` of `I`, the dpow map for the ideal `I(A⧸J)` of the quotient -/
def dpow_quot (J  : ideal A) (hIJ : is_sub_pd_ideal hI (I ⊓ J)) : ℕ → (I.map (ideal.quotient.mk J)) → (A ⧸ J) := sorry

lemma divided_powers_quot (J : ideal A) (hIJ : is_sub_pd_ideal hI (I ⊓ J)) :
  divided_powers (dpow_quot hI J hIJ) := sorry

lemma is_sub_pd_ideal_iff (S : set A) (hS : S ⊆ I) :
  is_sub_pd_ideal hI (ideal.span S) ↔ 
  ∀ (n : ℕ) (hn : 0 < n) (s : S), dpow n ⟨s, hS s.property⟩ ∈ ideal.span S :=
sorry

end divided_powers