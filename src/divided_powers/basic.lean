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

variables {A : Type*} [comm_ring A] {I : ideal A} (hI : divided_powers I)
/-- Proposition 1.2.7 of [B74], part (i). -/
lemma nilpotent_of_pd_ideal_mem (hI : divided_powers I) {n : ℕ} (hn : n ≠ 0)
  (hnI : ∀ {y : A}(hy : y ∈ I), n • y = 0) {x : A} (hx : x ∈ I) : x^n = 0 := 
begin
  have h_fac: (n.factorial : A) * hI.dpow n x = n • ((n-1).factorial : A) * hI.dpow n x,
  { rw [nsmul_eq_mul, ← nat.cast_mul, nat.mul_factorial_pred (nat.pos_of_ne_zero hn)] },
  rw [← factorial_mul_dpow_eq_pow hI _ _ hx, h_fac, smul_mul_assoc],
  exact hnI (I.mul_mem_left ((n - 1).factorial : A) (hI.dpow_mem hn hx))
end




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
1.3.1 : To be added (needs colimits of rings)

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