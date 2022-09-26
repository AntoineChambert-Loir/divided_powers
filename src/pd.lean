/- ACL and MIdFF, Lean 2022 meeting at Icerm -/

import tactic
import ring_theory.ideal.operations
import ring_theory.ideal.quotient
import ring_theory.ideal.operations
import linear_algebra.quotient
import ring_theory.tensor_product
import ring_theory.ideal.operations

import data.fin.tuple.nat_antidiagonal
import ring_theory.power_series.basic

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

section induction

namespace submodule
universes u v
variables {R : Type u} {M : Type v} {F : Type*} {G : Type*}
variables [comm_semiring R] [add_comm_monoid M] [module R M]
variables {I J : ideal R} {N P Q : submodule R M}

/- 
variables {x : M} {s : set M}
lemma span_induction_aux {p : M → Prop} (h : x ∈ span R s)
  (Hs : ∀ x ∈ s, p x) (H0 : p 0)
  (H1 : ∀ (x ∈ span R s) (y ∈ span R s), p x → p y → p (x + y))
  (H2 : ∀ (a : R) (x ∈ span R s), p x → p (a • x)) : p x :=
begin
  suffices : x ∈ span R s ∧ p x, exact this.2,
  exact span_induction h
  (λ x hx, ⟨submodule.subset_span hx, Hs x hx⟩)
  ⟨submodule.zero_mem (span R s), H0⟩
  (λ x y hx hy, ⟨submodule.add_mem (span R s) hx.1 hy.1, H1 x hx.1 y hy.1 hx.2 hy.2⟩)
  (λ a x hx, ⟨submodule.smul_mem (span R s) a hx.1, H2 a x hx.1 hx.2⟩),
end

theorem smul_induction_on_aux {p : M → Prop} {x} (H : x ∈ I • N)
  (Hb : ∀ (r ∈ I) (n ∈ N), p (r • n))
  (H1 : ∀ (x ∈ I • N) (y ∈ I • N), p x → p y → p (x + y)) : p x :=
begin
  suffices : x ∈ I • N ∧ p x, exact this.2, 
  exact submodule.smul_induction_on H
  (λ a ha x hx, ⟨(submodule.smul_mem_smul ha hx), Hb a ha x hx⟩)
  (λ x y hx hy, ⟨(I • N).add_mem hx.1 hy.1, H1 x hx.1 y hy.1 hx.2 hy.2⟩),
end  -/

lemma smul_induction_on' {x : M} (hx : x ∈ I • N) 
  {p : Π x, x ∈ I • N → Prop} 
  (Hb : ∀ (r : R) (hr : r ∈ I) (n : M) (hn : n ∈ N), p (r • n) (submodule.smul_mem_smul hr hn))
  (H1 : ∀ x hx y hy, p x hx → p y hy → p (x + y) (submodule.add_mem _ ‹_› ‹_›)) :
  p x hx :=
begin
  refine exists.elim _ (λ (h : x ∈ I • N) (H : p x h), H),
  exact submodule.smul_induction_on hx
    (λ a ha x hx, ⟨_, Hb _ ha _ hx⟩)
    (λ x y ⟨_, hx⟩ ⟨_, hy⟩,  ⟨_, H1 _ _ _ _ hx hy⟩),
end

-- TODO : add other if needed
end submodule

end induction

section auxiliary

/- To help distinguish the extreme cases in a finset.range(n+1).sum -/
lemma not_eq_or_aux {n m : ℕ} (hn : n ≠ 0) (hm : m ∈ finset.range(n + 1)) : m ≠ 0 ∨ n - m ≠ 0 :=
begin
  simp only [finset.mem_range, nat.lt_succ_iff] at hm,
  by_contradiction h,
  simp only [not_or_distrib, ne.def, not_not, tsub_eq_zero_iff_le, not_le, not_lt] at h,
  apply hn, rw ← le_zero_iff, rw ← h.1, exact h.2, 
end

lemma nat.self_sub_sub_eq {u v n : ℕ} (h : v ≤ u) (h' : u ≤ n) :
  n - v - (n - u) = u - v :=
begin 
  rw nat.sub_eq_iff_eq_add (tsub_le_tsub_left h n),
  rw ← nat.sub_add_comm h,
  rw add_comm,
  rw nat.sub_add_cancel h',
end


lemma function.extend_apply_first {α β γ : Type*} (f : α → β) (g : α → γ) (e' : β → γ)
  (hf : ∀ (a b : α), f a = f b → g a = g b) (a : α) :
  function.extend f g e' (f a) = g a :=
begin
  simp only [function.extend_def, dif_pos, exists_apply_eq_apply],
  apply hf,
  exact (classical.some_spec (exists_apply_eq_apply f a)),
end

/- TODO : There should be some general rewriting pattern 
for sums indexed by finset.nat_tuple_antidiagonal 
This one would first rewrite to 
(finset.nat_tuple_antidiagonal 4 n).sum (λ x, f(x0, x1, x2, x3)) 
and then one would apply the permutation (13)(24) -/
/-- Rewrites a 4-fold sum from variables (12)(34) to (13)(24) -/
lemma finset.sum_4_rw {α : Type*} [add_comm_monoid α] (f : ℕ × ℕ × ℕ × ℕ → α) (n : ℕ) : 
  finset.sum (finset.range (n + 1)) (λ k, 
    finset.sum (finset.range (k + 1)) (λ a, 
      finset.sum (finset.range (n - k + 1)) (λ c, 
        f(a, k-a,c, n - k - c)))) =
  finset.sum (finset.range (n + 1)) (λ l, 
    finset.sum (finset.range (l + 1)) (λ a, 
      finset.sum (finset.range (n - l + 1)) (λ b, 
        f(a, b, l - a, n - l - b)))) :=
begin
  rw finset.sum_sigma',
  rw finset.sum_sigma',
  rw finset.sum_sigma',
  rw finset.sum_sigma',
  let aux_i : (Σ (i : Σ (i : ℕ), ℕ), ℕ) → (Σ (i : Σ (i : ℕ), ℕ), ℕ) :=
  λ ⟨⟨k, a⟩, c⟩, ⟨⟨a + c, a⟩, k - a⟩,
  have aux_hi : ∀ (a : Σ (i : Σ (i : ℕ), ℕ), ℕ)
    (ha : a ∈ ((finset.range (n + 1)).sigma 
      (λ (x : ℕ), finset.range (x + 1))).sigma
        (λ (a : Σ (i : ℕ), ℕ), finset.range (n - a.fst + 1))),
    (λ (x : Σ (i : Σ (i : ℕ), ℕ), ℕ)
     (hx : x ∈ ((finset.range (n + 1)).sigma 
        (λ (a : ℕ), finset.range (a + 1))).sigma
           (λ (a : Σ (i : ℕ), ℕ), finset.range (n - a.fst + 1))), aux_i x) a ha ∈
    ((finset.range (n + 1)).sigma (λ (a : ℕ), finset.range (a + 1))).sigma
      (λ (x : Σ (i : ℕ), ℕ), finset.range (n - x.fst + 1)),
  { rintros ⟨⟨k, a⟩, c⟩ h,
    simp only [finset.mem_sigma, finset.mem_range, nat.lt_succ_iff] at h,
    simp_rw [aux_i, finset.mem_sigma, finset.mem_range, nat.lt_succ_iff], 
    split, split,
    { apply le_trans (add_le_add h.1.2 h.2) _,
      rw add_comm, rw nat.sub_add_cancel h.1.1, },
    { exact le_self_add, },
    { rw add_comm a c, rw ← nat.sub_sub n c a, 
      simp, rw nat.sub_add_cancel, 
      rw nat.le_sub_iff_right,
      rw nat.le_sub_iff_right at h, rw add_comm k c, exact h.2,
      exact h.1.1,
      apply le_trans h.2, exact nat.sub_le n k,
      rw nat.le_sub_iff_right, 
      rw nat.le_sub_iff_right at h,
      apply nat.le_of_add_le_add_right, 
      rw add_assoc a c _, rw add_comm n _,
      exact add_le_add h.1.2 h.2,
      exact h.1.1,
      apply le_trans h.2 _, apply nat.sub_le, }, },
  rw finset.sum_bij' (λ x hx, aux_i x) aux_hi _ (λ y hy, aux_i y) aux_hi _ _, 
  { rintros ⟨⟨k, a⟩, c⟩ h, 
    simp only [finset.mem_sigma, finset.mem_range, nat.lt_succ_iff] at h,
    apply congr_arg, 
    dsimp [aux_i],
    simp only [prod.mk.inj_iff],
    apply and.intro rfl, 
    apply and.intro rfl,
    split,
    { rw add_comm a c, rw nat.add_sub_cancel, },
    { simp only [nat.sub_sub],
      apply congr_arg2 _ rfl,
      rw [add_comm k c, add_comm a c, add_assoc],
      apply congr_arg2 _ rfl,
      rw add_comm, 
      rw nat.sub_add_cancel h.1.2, }, },
  { rintros ⟨⟨k, a⟩, c⟩ h,
    simp only [finset.mem_sigma, finset.mem_range, nat.lt_succ_iff] at h,
    simp_rw [aux_i],
    simp only [add_tsub_cancel_left, sigma.mk.inj_iff, heq_iff_eq, eq_self_iff_true, and_true], 
    { rw add_comm, rw nat.sub_add_cancel h.1.2, }, },
  { rintros ⟨⟨k, a⟩, c⟩ h,
    simp only [finset.mem_sigma, finset.mem_range, nat.lt_succ_iff] at h,
    simp_rw [aux_i],
    simp only [add_tsub_cancel_left, sigma.mk.inj_iff, heq_iff_eq, eq_self_iff_true, and_true], 
    { rw add_comm, rw nat.sub_add_cancel h.1.2, }, },
end

end auxiliary

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

/- A combinatorial lemma in search of a proof -/
lemma comb_lemma (m n s: ℕ) (hs : s ≤ m + n) : 
  (finset.filter (λ (x : ℕ × ℕ), x.fst + x.snd = s) ((finset.range (m + 1)).product (finset.range (n + 1)))).sum
  (λ (x : ℕ × ℕ), (s.choose x.fst) * ((m + n - s).choose (m - x.fst)))
  = (m + n).choose m := sorry
/- 
Algebraic proof :

(1+T)^(a+b) = ∑ (a + b choose z) T^z
= (1+T)^a (1+T)^b = ∑ (a choose x) T^x (b choose y) T^y
  = ∑ (a choose x) (b choose y) T^(x+y)
Coefficient de T^(m) :
 ∑ (a choose x) (b choose (m - x)) = (a+b  choose m)
 Prendre a = s, b = m + n - s, a + b = m + n car s ≤ m + n. 

 Combinatorial proof ? 

-/
end combinatorics

section divided_powers_definition

/- No need for this, Mario says…

structure is_divided_powers {A : Type*} [comm_ring A] (I : ideal A) (dpow : ℕ → A → A) : Prop :=
(dpow_null : ∀ {n x} (hx : x ∉ I), dpow n x = 0)
(dpow_zero : ∀ {x} (hx : x ∈ I), dpow 0 x = 1)
(dpow_one : ∀ {x} (hx : x ∈ I), dpow 1 x = x)
(dpow_mem : ∀ {n} (hn : n ≠ 0) {x} (hx : x ∈ I), dpow n x ∈ I)
(dpow_add : ∀ n {x y} (hx : x ∈ I) (hy : y ∈ I) , dpow n (x + y)
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
(dpow_add : ∀ n {x y} (hx : x ∈ I) (hy : y ∈ I) , dpow n (x + y)
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


end divided_powers_definition

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

variable (hI : divided_powers I)
include hI

/- Rewriting lemmas -/
lemma dpow_smul' (n : ℕ) {a : A} {x : A} (hx : x ∈ I) : hI.dpow n (a • x) = (a ^ n) • (hI.dpow n x) :=
by simp only [smul_eq_mul, hI.dpow_smul, hx]

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


section factorial_inv
variables {A : Type*} [comm_ring A] {I : ideal A}

lemma factorial_is_unit {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A))
  {m : ℕ} (hmn : m < n) : is_unit (m.factorial : A) :=
begin
  apply is_unit_of_dvd_unit _ hn_fac,
  obtain ⟨c, hc⟩ := nat.factorial_dvd_factorial (nat.le_pred_of_lt hmn),
  use (c : A),
  rw [← nat.cast_mul, hc],
end

noncomputable def factorial_inv {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A))
  {m : ℕ} (hmn : m < n) : A :=
(factorial_is_unit hn_fac hmn).unit.inv

@[simp]
lemma factorial_inv_mul {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ} (hmn : m < n) :
  (factorial_inv hn_fac hmn) * (m.factorial : A) = 1 :=
by rw [factorial_inv, units.inv_eq_coe_inv, is_unit.coe_inv_mul]

lemma eq_mul_factorial_inv_iff_mul_eq {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ}
  (hmn : m < n) {a b : A} : a = b * (factorial_inv hn_fac hmn) ↔ a * (m.factorial : A) = b := 
by rw [factorial_inv, units.inv_eq_coe_inv, units.eq_mul_inv_iff_mul_eq]; refl

lemma factorial_inv_mul_eq_iff_eq_mul {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ}
  (hmn : m < n) {a b : A} :  (factorial_inv hn_fac hmn) * a = b ↔ a = (m.factorial : A) * b :=
by rw [factorial_inv, units.inv_eq_coe_inv, units.inv_mul_eq_iff_eq_mul]; refl

lemma factorial_inv_pow_mul_eq_iff_eq_mul {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ}
  (hmn : m < n) {a b : A} { k : ℕ} : 
  (factorial_inv hn_fac hmn)^k * a = b ↔ a = (m.factorial : A)^k * b :=
begin
  rw [factorial_inv, units.inv_eq_coe_inv, ← units.coe_pow, inv_pow, units.inv_mul_eq_iff_eq_mul,
    units.coe_pow],
  refl,
end

@[simp]
lemma factorial_inv_zero' {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) (hn0 : n ≠ 0) :
  factorial_inv hn_fac (nat.pos_of_ne_zero hn0) = 1 :=
begin
  rw [← mul_one (factorial_inv hn_fac (nat.pos_of_ne_zero hn0))],
  convert factorial_inv_mul hn_fac (nat.pos_of_ne_zero hn0),
  rw [nat.factorial_zero, nat.cast_one],
end

@[simp]
lemma factorial_inv_one {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) (hn1 : 1 < n) :
  factorial_inv hn_fac hn1 = 1 :=
begin
  rw [← mul_one (factorial_inv hn_fac hn1)],
  convert factorial_inv_mul hn_fac hn1,
  rw [nat.factorial_one, nat.cast_one],
end

end factorial_inv

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

noncomputable def dpow (I : ideal A) {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) :
  ℕ → A → A :=
λ m x, if h : m < n ∧ x ∈ I then (factorial_inv hn_fac h.1) * x^m else 0

lemma dpow_dif_pos (I : ideal A) {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ}
  (hm : m < n) {x : A} (hx : x ∈ I) : dpow I hn_fac m x = (factorial_inv hn_fac hm) * x^m :=
by simp only [dpow]; rw dif_pos (and.intro hm hx)

lemma dpow_of_nmem (I : ideal A) {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ} {x : A}
  (hx : x ∉ I) : dpow I hn_fac m x = 0 :=
by simp only [dpow]; rw dif_neg (not_and_of_not_right _ hx)

lemma dpow_of_ge (I : ideal A) {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ}
  (hm : ¬ m < n) {x : A} : dpow I hn_fac m x = 0 :=
by simp only [dpow]; rw dif_neg (not_and_of_not_left _ hm)

lemma dpow_null {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ} {x : A}
  (hx : x ∉ I) : dpow I hn_fac m x = 0 := 
by simp only [dpow]; rw [dif_neg (not_and_of_not_right _ hx)]

lemma dpow_zero {n : ℕ} (hn0 : n ≠ 0) (hn_fac : is_unit ((n-1).factorial : A)) {x : A}
  (hx : x ∈ I) : dpow I hn_fac 0 x = 1 :=
begin
  simp only [dpow],
  rw [dif_pos (and.intro (nat.pos_of_ne_zero hn0) hx), pow_zero, mul_one],
  exact factorial_inv_zero' hn_fac hn0,
end

lemma dpow_one {n : ℕ} (hn0 : n ≠ 0) (hn_fac : is_unit ((n-1).factorial : A)) (hnI : I^n = 0)
  {x : A} (hx : x ∈ I) : dpow I hn_fac 1 x = x := 
begin
  simp only [dpow],
  split_ifs with h1,
  { rw [pow_one, factorial_inv_one, one_mul] },
  { simp only [hx, and_true, not_lt] at h1,
    have hn1 : n = 1 := le_antisymm h1 (nat.succ_le_of_lt (nat.pos_of_ne_zero hn0)),
    rw [hn1, pow_one] at hnI,
    rw [hnI, ideal.zero_eq_bot, ideal.mem_bot] at hx,
    exact hx.symm,  },
end

lemma dpow_mem {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ} (hn : m ≠ 0)
  {x : A} (hx : x ∈ I) : dpow I hn_fac m x ∈ I := 
begin
  simp only [dpow],
  split_ifs with h,
  { exact ideal.mul_mem_left I _ (ideal.pow_mem_of_mem I hx _ (nat.pos_of_ne_zero hn)) },
  { exact ideal.zero_mem I },
end

lemma dpow_add_dif_pos {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m : ℕ} (hmn : m < n) {x : A}
  (hx : x ∈ I) {y : A} (hy : y ∈ I) : dpow I hn_fac m (x + y) =
  (finset.range (m + 1)).sum (λ (k : ℕ), dpow I hn_fac k x * dpow I hn_fac (m - k) y) :=
begin
  rw dpow_dif_pos I hn_fac hmn (ideal.add_mem I hx hy),
  simp only [dpow],
  rw [factorial_inv_mul_eq_iff_eq_mul, finset.mul_sum, add_pow],
  apply finset.sum_congr rfl,
  intros k hk,
  rw [finset.mem_range, nat.lt_succ_iff] at hk,
  have hkxI : k < n ∧ x ∈ I := and.intro (lt_of_le_of_lt hk hmn) hx,
  have hkyI : m - k < n ∧ y ∈ I := and.intro (lt_of_le_of_lt (nat.sub_le m k) hmn) hy,
  have h_ch : (m.choose k : A) =
    (m.factorial : A) * (factorial_inv hn_fac hkxI.1) * (factorial_inv hn_fac hkyI.1),
  { have hadd : m = (m - k) + k := (tsub_add_cancel_iff_le.mpr hk).symm,
    rw [eq_mul_factorial_inv_iff_mul_eq, eq_mul_factorial_inv_iff_mul_eq],
    nth_rewrite 0 hadd,
    nth_rewrite 2 hadd,
    rw [← nat.cast_mul, ← nat.cast_mul, nat.add_choose_mul_factorial_mul_factorial], },
  rw [dif_pos hkxI, dif_pos hkyI, h_ch, ← mul_assoc, ← mul_assoc, mul_comm
    (factorial_inv hn_fac _) (y ^ (m - k)), mul_assoc _ (x^k), ← mul_assoc (x^k),
    mul_comm (x ^ k * y ^ (m - k)) (factorial_inv hn_fac _)],
    ring_nf,
end

lemma dpow_add {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) (hnI : I^n = 0) (m : ℕ) {x : A}
  (hx : x ∈ I) {y : A} (hy : y ∈ I) : dpow I hn_fac m (x + y) =
    (finset.range (m + 1)).sum (λ (k : ℕ), dpow I hn_fac k x * dpow I hn_fac (m - k) y) := 
begin
  by_cases hmn : m < n,
  { exact dpow_add_dif_pos hn_fac hmn hx hy },
  { rw [dpow_of_ge I hn_fac hmn, eq_comm],
    apply finset.sum_eq_zero,
    intros k hk,
    simp only [dpow],
    split_ifs with hkn hmkn,
    { rw [mul_assoc, mul_comm (x^k), mul_assoc, ← mul_assoc],
      apply mul_eq_zero_of_right,
      rw [← ideal.mem_bot, ← ideal.zero_eq_bot, ← hnI],
      have hIm : y ^ (m - k) * x ^ k ∈ I ^ m,
      { have hadd : m = (m - k) + k,
        { rw [eq_comm, tsub_add_cancel_iff_le],
          exact nat.le_of_lt_succ (finset.mem_range.mp hk) },
        nth_rewrite 1 hadd,
        rw pow_add,
        exact ideal.mul_mem_mul (ideal.pow_mem_pow hy _) (ideal.pow_mem_pow hx _) },
      have h_sub : I^m ≤ I^n := ideal.pow_le_pow (not_lt.mp hmn),
      convert set.mem_of_subset_of_mem h_sub hIm, },
    { rw mul_zero },
    { rw zero_mul },
    { rw mul_zero }}
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

lemma dpow_smul {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) (m : ℕ) {a x : A}
  (hx : x ∈ I) : dpow I hn_fac m (a * x) = a ^ m * dpow I hn_fac m x :=
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
end

lemma dpow_mul_dif_pos {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) {m k : ℕ} (hkm : k + m < n) 
  {x : A} (hx : x ∈ I) :
  dpow I hn_fac m x * dpow I hn_fac k x = ↑((k + m).choose m) * dpow I hn_fac (k + m) x := 
begin
  have hm : m < n := lt_of_le_of_lt le_add_self hkm,
  have hk : k < n := lt_of_le_of_lt le_self_add hkm,
  have h_fac : (factorial_inv hn_fac hm) * (factorial_inv hn_fac hk) =
    ↑((k + m).choose m) * (factorial_inv hn_fac hkm),
  { rw [eq_mul_factorial_inv_iff_mul_eq, mul_assoc, factorial_inv_mul_eq_iff_eq_mul,
      factorial_inv_mul_eq_iff_eq_mul],
    norm_cast,
    rw [← nat.add_choose_mul_factorial_mul_factorial, mul_assoc, mul_comm, mul_assoc] },
    rw [dpow_dif_pos _ _ hm hx, dpow_dif_pos _ _ hk hx, dpow_dif_pos _ _ hkm hx, mul_assoc,
      ← mul_assoc (x^m), mul_comm (x^m), mul_assoc _ (x^m), ← pow_add, ← mul_assoc, ← mul_assoc,
      add_comm, h_fac]
end

lemma dpow_mul {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A)) (hnI : I^n = 0) (m k : ℕ) {x : A}
  (hx : x ∈ I) :
  dpow I hn_fac m x * dpow I hn_fac k x = ↑((k + m).choose m) * dpow I hn_fac (k + m) x := 
begin
  by_cases hkm : k + m < n,
  { exact dpow_mul_dif_pos hn_fac hkm hx, },
  { by_cases hk : k < n,
    { by_cases hm : m < n,
      { have hxmk : x ^ (k + m) = 0,
        { exact ideal.mem_pow_eq_zero n (k + m) hnI (not_lt.mp hkm) hx },
        rw [dpow_dif_pos I hn_fac hk hx, dpow_dif_pos I hn_fac hm hx, dpow_of_ge I hn_fac hkm, 
          mul_assoc, ← mul_assoc (x^m), mul_comm (x^m), mul_assoc _ (x^m), ← pow_add, add_comm, 
          hxmk, mul_zero, mul_zero, mul_zero] },
      { rw [dpow_of_ge I hn_fac hkm, dpow_of_ge I hn_fac hm, zero_mul, mul_zero] }},
    { rw [dpow_of_ge I hn_fac hkm, dpow_of_ge I hn_fac hk, mul_zero, mul_zero] }}
end

lemma dpow_comp_dif_pos {n : ℕ} (hn0 : n ≠ 0) (hn_fac : is_unit ((n-1).factorial : A)) 
  {m k : ℕ} (hk : k ≠ 0) (hkm : m * k < n) {x : A} (hx : x ∈ I) :
  dpow I hn_fac m (dpow I hn_fac k x) = ↑(mchoose m k) * dpow I hn_fac (m * k) x := 
begin
  have hmn : m < n,
  { exact lt_of_le_of_lt (nat.le_mul_of_pos_right (nat.pos_of_ne_zero hk)) hkm },
  rw [dpow_dif_pos I hn_fac hkm hx, dpow_dif_pos I hn_fac hmn (dpow_mem hn_fac hk hx)],
  by_cases hm0 : m = 0,
  { simp only [hm0, zero_mul, pow_zero, mul_one, mchoose_zero, nat.cast_one, one_mul] },
  { have hkn : k < n,
    { exact lt_of_le_of_lt (nat.le_mul_of_pos_left (nat.pos_of_ne_zero hm0)) hkm },
    rw [dpow_dif_pos I hn_fac hkn hx],
    have h_fac' : (factorial_inv hn_fac hmn) * (factorial_inv hn_fac hkn) ^ m =
      ↑(mchoose m k) * (factorial_inv hn_fac hkm),
    { rw [eq_mul_factorial_inv_iff_mul_eq, mul_assoc, factorial_inv_mul_eq_iff_eq_mul,
        factorial_inv_pow_mul_eq_iff_eq_mul, ← mchoose_lemma _ (nat.pos_of_ne_zero hk),
        nat.cast_mul, nat.cast_mul, nat.cast_pow, mul_comm ↑m.factorial, mul_assoc] },
    rw [ mul_pow, ← pow_mul, mul_comm k, ← mul_assoc, ← mul_assoc, h_fac'] },
end

lemma dpow_comp {n : ℕ} (hn0 : n ≠ 0) (hn_fac : is_unit ((n-1).factorial : A)) (hnI : I^n = 0)
  (m : ℕ) {k : ℕ} (hk : k ≠ 0) {x : A} (hx : x ∈ I) :
  dpow I hn_fac m (dpow I hn_fac k x) = ↑(mchoose m k) * dpow I hn_fac (m * k) x :=
begin
  by_cases hmk : m * k < n,
  { exact dpow_comp_dif_pos hn0 hn_fac hk hmk hx },
  { by_cases hkn : k < n,
    { by_cases hmn : m < n,
      { rw [dpow_dif_pos I hn_fac hmn (dpow_mem hn_fac hk hx), dpow_dif_pos I hn_fac hkn hx,
          dpow_of_ge I hn_fac hmk, mul_zero, mul_pow, ← pow_mul, ← mul_assoc, mul_comm k,
          ideal.mem_pow_eq_zero n (m * k) hnI (not_lt.mp hmk) hx, mul_zero] },
      { rw [dpow_of_ge I hn_fac hmk, dpow_of_ge I hn_fac hmn, mul_zero] }},
    { rw [dpow_of_ge I hn_fac hmk],
      rw dpow_of_ge I hn_fac hkn,
      by_cases hm : m < n,
      { have hm_pos : 0 < m,
        { by_contra' hm0,
          rw [le_zero_iff.mp hm0, zero_mul] at hmk,
          exact hmk (nat.pos_of_ne_zero hn0),},
        rw [dpow_dif_pos I hn_fac hm I.zero_mem, zero_pow hm_pos, mul_zero, mul_zero] },
      { rw [dpow_of_ge I hn_fac hm, mul_zero] }}}
end

/-- Proposition 1.2.7 of [B74], part (ii). -/
noncomputable def divided_powers {n : ℕ} (hn0 : n ≠ 0) (hn_fac : is_unit ((n-1).factorial : A))
  (hnI : I^n = 0) : divided_powers I := 
{ dpow      := dpow I hn_fac,
  dpow_null := λ n x hx, dpow_null hn_fac hx,
  dpow_zero := λ x hx, dpow_zero hn0 hn_fac hx,
  dpow_one  := λ x hx, dpow_one hn0 hn_fac hnI hx,
  dpow_mem  := λ n hn x hx, dpow_mem hn_fac hn hx,
  dpow_add  := λ m x y hx hy, dpow_add hn_fac hnI m hx hy,
  dpow_smul := λ m a x hx, dpow_smul hn_fac m hx,
  dpow_mul  := λ m k x hx, dpow_mul hn_fac hnI m k hx,
  dpow_comp := λ m k hk x hx, dpow_comp hn0 hn_fac hnI m hk hx }

end of_invertible_factorial

end factorial

-- Instead of 1.2.1, I formalize example 2 from [BO], Section 3.
namespace Q_algebra

variables {R : Type*} [comm_ring R] [algebra ℚ R]

lemma factorial.is_unit (n : ℕ) : is_unit (n.factorial : R) :=
begin
  have hn : (n.factorial : R) = algebra_map ℚ R n.factorial,
  { rw [map_nat_cast] },
  rw hn,
  apply is_unit.map,
  exact is_unit_iff_ne_zero.mpr (nat.cast_ne_zero.mpr (nat.factorial_ne_zero n)),
end

variable (I : ideal R) 

noncomputable def dpow : ℕ → R → R :=
λ n, of_invertible_factorial.dpow I (factorial.is_unit (n + 1 - 1)) n

variable {I}
lemma dpow_def (n : ℕ) {x : R} (hx : x ∈ I) : 
  dpow I n x = (factorial_inv (factorial.is_unit (n + 1 - 1)) (n.lt_succ_self)) * x^n :=
begin
  simp only [dpow, of_invertible_factorial.dpow],
  rw dif_pos (and.intro (n.lt_succ_self) hx),
end

lemma dpow_one {x : R} (hx : x ∈ I) : dpow I 1 x = x :=
by rw [dpow_def 1 hx, pow_one, factorial_inv_one, one_mul]

lemma dpow_add (n : ℕ) {x y : R} (hx : x ∈ I) (hy : y ∈ I) :
  dpow I n (x + y) = (finset.range (n + 1)).sum (λ (k : ℕ), dpow I k x * dpow I (n - k) y) :=
begin
  simp only [dpow],
  rw of_invertible_factorial.dpow_add_dif_pos (factorial.is_unit (n + 1 - 1)) (n.lt_succ_self)
    hx hy,
  apply finset.sum_congr rfl,
  intros k hk,
  rw [finset.mem_range] at hk,
  rw [of_invertible_factorial.dpow_dif_pos _ _ hk hx,
    of_invertible_factorial.dpow_dif_pos _ _ k.lt_succ_self hx,
    of_invertible_factorial.dpow_dif_pos _ _ (n.sub_lt_succ k) hy,
    of_invertible_factorial.dpow_dif_pos _ _ (n - k).lt_succ_self hy],
  refl,
end

lemma dpow_mul (m n : ℕ) {x : R} (hx : x ∈ I) :
  dpow I m x * dpow I n x = ↑((n + m).choose m) * dpow I (n + m) x :=
begin
  simp only [dpow],
  rw [← of_invertible_factorial.dpow_mul_dif_pos (factorial.is_unit (n + m + 1 - 1)) 
    (n + m).lt_succ_self hx, of_invertible_factorial.dpow_dif_pos _ _ m.lt_succ_self hx,
    of_invertible_factorial.dpow_dif_pos _ _ n.lt_succ_self hx,
    of_invertible_factorial.dpow_dif_pos _ _ (nat.lt_add_of_zero_lt_left _ _(m.succ_pos)) hx,
    of_invertible_factorial.dpow_dif_pos _ _ _ hx],
  refl,
  { rw add_comm n;
    exact (nat.lt_add_of_zero_lt_left _ _(n.succ_pos)) }
end

lemma dpow_comp (m : ℕ) {k : ℕ} (hk : k ≠ 0) {x : R} (hx : x ∈ I) :
  dpow I m (dpow I k x) = ↑(mchoose m k) * dpow I (m * k) x := 
begin
  have hkIx : of_invertible_factorial.dpow I (factorial.is_unit (k + 1 - 1))  k x ∈ I,
  { apply of_invertible_factorial.dpow_mem _ hk hx,},
  have hmkIx : of_invertible_factorial.dpow I (factorial.is_unit (m * k + 1 - 1)) k x ∈ I,
  { apply of_invertible_factorial.dpow_mem _ hk hx,},
  have hmk : m < (m * k).succ := 
  nat.lt_succ_of_le (nat.le_mul_of_pos_right (nat.pos_of_ne_zero hk)),
  simp only [dpow],
  rw [← of_invertible_factorial.dpow_comp_dif_pos (nat.succ_ne_zero _) 
    (factorial.is_unit (m * k + 1 - 1)) hk (lt_add_one _) hx, 
    of_invertible_factorial.dpow_dif_pos _ _ m.lt_succ_self 
      (of_invertible_factorial.dpow_mem _ hk hx),
    of_invertible_factorial.dpow_dif_pos _ _ k.lt_succ_self hx,
    of_invertible_factorial.dpow_dif_pos _ _ hmk (of_invertible_factorial.dpow_mem _ hk hx)],
  by_cases hm : m = 0,
  { simp_rw hm,
    rw [pow_zero, pow_zero, mul_one, mul_one], refl,},
  { have hkm : k < m * k + 1 := 
    nat.lt_succ_of_le (nat.le_mul_of_pos_left (nat.pos_of_ne_zero hm)),
    rw [of_invertible_factorial.dpow_dif_pos _ _ hkm hx],
    refl },
end

noncomputable def divided_powers : divided_powers I := 
{ dpow      := dpow I,
  dpow_null := λ n x hx, of_invertible_factorial.dpow_null (factorial.is_unit n) hx,
  dpow_zero := λ x hx, of_invertible_factorial.dpow_zero one_ne_zero (factorial.is_unit 0) hx,
  dpow_one  := λ x hx, dpow_one hx,
  dpow_mem  := λ n hn x hx, of_invertible_factorial.dpow_mem (factorial.is_unit n) hn hx,
  dpow_add  := λ n x y hx hy, dpow_add n hx hy,
  dpow_smul := λ n a x hx, of_invertible_factorial.dpow_smul (factorial.is_unit n) n hx,
  dpow_mul  := λ m k x hx, dpow_mul m k hx,
  dpow_comp := λ m k hk x hx, dpow_comp m hk hx, }

end Q_algebra

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
    rw hI.dpow_add n hb hab', 
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


/-- If J is an ideal of A, then J ⬝ I is a sub-pd-ideal of I.
  (Berthelot, 1.6.1 (i)) -/
lemma is_sub_pd_ideal_prod (J : ideal A) : is_sub_pd_ideal hI (I • J) :=
begin
  split,
  exact ideal.mul_le_right,
  intros n hn x hx, revert n,
  apply submodule.smul_induction_on' hx,
  { -- mul 
    intros a ha b hb n hn,
    rw [algebra.id.smul_eq_mul, mul_comm a b, hI.dpow_smul n ha, mul_comm], 
    apply submodule.mul_mem_mul (hI.dpow_mem hn ha) (J.pow_mem_of_mem hb n (zero_lt_iff.mpr hn)), },
  { -- add 
    intros x hx y hy hx' hy' n hn, 
    rw hI.dpow_add n (ideal.mul_le_right hx) (ideal.mul_le_right hy),
    apply submodule.sum_mem (I • J),
    intros k hk, 
    cases not_eq_or_aux hn hk with hk' hk',
    { apply ideal.mul_mem_right _ (I • J), exact hx' k hk', },
    { apply ideal.mul_mem_left (I • J), exact hy' _ hk', } } 
end

/-- If J is another ideal of A with divided powers, 
then the divided powers of I and J coincide on I • J 
(Berthelot, 1.6.1 (ii))-/
lemma coincide_on_smul {J : ideal A} (hJ : divided_powers J) : 
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

/- TODO : 
* prove uniqueness
* add rfl lemma that gives analogue of dpow_quot_eq for the divided_powers 
that was just defined 
* maybe other… 
-/

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

noncomputable
def dpow_ideal_add {J : ideal A} (hJ : divided_powers J) :
  ℕ → A → A := λ n,
function.extend 
  (λ ⟨a, b⟩, (a : A) + (b : A) : I × J → A)
  (λ ⟨a, b⟩, finset.sum (finset.range (n + 1)) (λ k, (hI.dpow k (a : A)) * (hJ.dpow (n - k) (b : A))))
  (λ (a : A), 0)
 
lemma dpow_ideal_add_eq_aux {J : ideal A} (hJ : divided_powers J)
  (hIJ : ∀ (n : ℕ) {a} (ha : a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a)
  (n : ℕ) {a} (ha : a ∈ I) {b} (hb : b ∈ J) {a'} (ha' : a' ∈ I) {b'} (hb' : b' ∈ J)
  (H : a + b = a' + b') : 
  finset.sum (finset.range (n + 1)) (λ k, (hI.dpow k a) * (hJ.dpow (n - k) b)) 
    = finset.sum (finset.range (n + 1)) (λ k, (hI.dpow k a') * (hJ.dpow (n - k) b'))  :=
begin
  let c := a - a',
  suffices haa' : a = a' + c, 
  suffices hbb' : b' = b + c, 
  have hcI : c ∈ I := sub_mem ha ha',
  suffices hcJ : c ∈ J,
  rw [haa',  hbb'],
  have Ha'c : 
  (finset.range (n + 1)).sum (λ (k : ℕ), hI.dpow k (a' + c) * hJ.dpow (n - k) b)
   = (finset.range (n+1)).sum (λ (k : ℕ),
    (finset.range (k+1)).sum 
      (λ (l : ℕ), (hI.dpow l a') * (hJ.dpow (n-k) b) * (hI.dpow (k-l) c))),
  { apply finset.sum_congr rfl,
    intros k hk,
    rw hI.dpow_add k ha' hcI,
    rw finset.sum_mul, 
    apply finset.sum_congr rfl,
    intros l hl,
    ring, },
  rw Ha'c,
  rw finset.sum_sigma', 
  have Hbc : (finset.range (n + 1)).sum (λ (k : ℕ), hI.dpow k a' * hJ.dpow (n - k) (b + c))
   = (finset.range (n+1)).sum (λ (k : ℕ),
    (finset.range (n-k+1)).sum
      (λ (l : ℕ), (hI.dpow k a') * (hJ.dpow l b) * (hJ.dpow (n-k-l) c))),
  { apply finset.sum_congr rfl,
    intros k hk,
    rw hJ.dpow_add (n - k) hb hcJ,
    rw finset.mul_sum, ring_nf, },
  rw Hbc,
  rw finset.sum_sigma',
  
  let s := ((finset.range (n + 1)).sigma (λ (a : ℕ), finset.range (a + 1))),
  let i : Π (x : (Σ (i : ℕ), ℕ)), (x ∈ s) → (Σ (i : ℕ), ℕ) := λ ⟨k, m⟩ h, ⟨m, n-k⟩,
  let t := ((finset.range (n + 1)).sigma (λ (a : ℕ), finset.range (n - a + 1))),
  let j : Π (y : (Σ (i : ℕ), ℕ)), (y ∈ t) → (Σ (i : ℕ), ℕ) := λ ⟨k, m⟩ h, ⟨n-m,k⟩,
  /- 
  -- rw finset.sum_bij' (λ (⟨k,m⟩ : σ (ℕ → ℕ)), (⟨m, k-m⟩) _ _ (λ ⟨k, m), ⟨k+m,k⟩) _ _ _ ,

  -- s = (finset.range (n+1)).sigma (λ k, finset.range (k+1))
  -- ⟨k,m⟩, 0 ≤ m ≤ k ≤ n  correspond à [m,k-m,n-k]
  -- t = (finset.range (n+1)).sigma (λ k, finset.range (n-k+1))
  -- ⟨k, m⟩, 0 ≤ k ≤ n, et 0 ≤ m ≤ n -k
  -- correspond à [k, m, n-k-m]
  -- bijection : k' = m, m' = k -m (donc n-k'-m'=n-k)
  -- i := λ ⟨k,m⟩, ⟨m, k-m⟩
  -- j := λ ⟨k',m'⟩, ⟨k'+m',k'⟩

a'[x2] b[n-x1] c[x1-x2] = a'[y1] b[y2] c[n-y1-y2]
y1 = x2, y2=n-x1
x1 = n - y2, x2 = y1
((finset.range (n + 1)).sigma (λ (a : ℕ), finset.range (a + 1))).sum
    (λ (x : Σ (i : ℕ), ℕ), hI.dpow x.snd a' * hJ.dpow (n - x.fst) b * hI.dpow (x.fst - x.snd) c) =
  ((finset.range (n + 1)).sigma (λ (a : ℕ), finset.range (n - a + 1))).sum
    (λ (x : Σ (i : ℕ), ℕ), hI.dpow x.fst a' * hJ.dpow x.snd b * hJ.dpow (n - x.fst - x.snd) c)

  -- (finset.range (n+1))
  -- (λ k, finset.range (k+1)),
-/

  rw finset.sum_bij' i _ _ j _ _ ,
  { rintros ⟨k,m⟩ h, 
    change i ⟨n-m,k⟩ _ = _,
    change (⟨k,n - (n-m)⟩ : (Σ (i : ℕ), ℕ)) = _,
    simp only [eq_self_iff_true, heq_iff_eq, true_and],
    simp only [finset.mem_sigma, finset.mem_range, nat.lt_succ_iff] at h,
    apply nat.sub_sub_self , apply le_trans h.2, apply nat.sub_le, },
  { rintros ⟨k, m⟩ h, 
    change (⟨m, n - k⟩ : (Σ (i : ℕ), ℕ)) ∈ t, 
    simp only [finset.mem_sigma, finset.mem_range, nat.lt_succ_iff] at h ⊢,

    apply and.intro (le_trans h.2 h.1),
    apply tsub_le_tsub_left h.2, },

    { rintros ⟨u,v⟩ h, 
      -- split all factors
      apply congr_arg2,
      apply congr_arg2,
      -- a' : no problemo
      refl, 
      -- b : more difficult
      apply congr_arg2, refl, refl,      
      -- c :
      rw hIJ _ ⟨hcI, hcJ⟩,
      apply congr_arg2, 
      change u - v = n - v - (n - u),
      simp only [finset.mem_sigma, finset.mem_range, nat.lt_succ_iff] at h,
      rw nat.self_sub_sub_eq h.2 h.1, 
      refl, },

    { rintros ⟨k,m⟩ h,
      change (⟨n-m, k⟩ : (Σ (i : ℕ), ℕ)) ∈ s,
      simp only [finset.mem_sigma, finset.mem_range, nat.lt_succ_iff] at h ⊢,
      apply and.intro (nat.sub_le _ _),
      rw nat.le_sub_iff_right (le_trans h.2 (nat.sub_le n k)),
      rw add_comm, 
      rw ← nat.le_sub_iff_right h.1,
      exact h.2, },

    { rintros ⟨k,m⟩ h, 
      change j ⟨m, n - k⟩ _ = _,
      change (⟨n - (n-k), m⟩ : (Σ (i : ℕ), ℕ)) = _,
            simp only [finset.mem_sigma, finset.mem_range, nat.lt_succ_iff] at h,
      simp only [heq_iff_eq, eq_self_iff_true, and_true],
      exact nat.sub_sub_self h.1, },

    { rw ← (sub_eq_iff_eq_add'.mpr hbb'), exact sub_mem hb' hb },

    { rw ← sub_eq_iff_eq_add' at H, rw ← H, rw haa', ring, },

    { simp only [c], ring, },
end

lemma dpow_ideal_add_eq {J : ideal A} (hJ : divided_powers J)
  (hIJ : ∀ (n : ℕ) (a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a)
  (n) {a} (ha : a ∈ I) {b} (hb : b ∈ J) : 
  dpow_ideal_add hI hJ n (a + b) = finset.sum (finset.range (n + 1)) (λ k, (hI.dpow k a) * (hJ.dpow (n - k) b))  :=
begin
  simp only [dpow_ideal_add],
  convert function.extend_apply_first _ _ _ _ (⟨(⟨a, ha⟩ : I), (⟨b, hb⟩ : J)⟩ : I × J),
  rintros ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩, 
  intro H,
  refine dpow_ideal_add_eq_aux hI hJ _ n ha hb ha' hb' H,
  { intros n a, exact hIJ n a, },
end



noncomputable
def divided_powers_ideal_add {J : ideal A} (hJ : divided_powers J) 
  (hIJ : ∀ (n : ℕ) (a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a) : divided_powers (I + J) := { 
dpow := dpow_ideal_add hI hJ,
dpow_null := 
begin
  intros n x hx, 
  simp only [dpow_ideal_add], 
  rw function.extend_apply', 
  rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, h⟩, apply hx, 
  rw ← h,
--  change a + b ∈ I + J,
  exact submodule.add_mem_sup ha hb,
end,
dpow_zero := 
begin
  intro x, 
  rw [ideal.add_eq_sup, submodule.mem_sup], 
  rintro ⟨a, ha, b, hb, rfl⟩, 
  rw dpow_ideal_add_eq hI hJ hIJ (0 : ℕ) ha hb, 
  simp only [finset.range_one, zero_tsub, finset.sum_singleton],
  rw [hI.dpow_zero ha, hJ.dpow_zero hb, mul_one],
end,
dpow_one := 
begin
  intro x,
  rw [ideal.add_eq_sup, submodule.mem_sup], 
  rintro ⟨a, ha, b, hb, rfl⟩, 
  rw dpow_ideal_add_eq hI hJ hIJ _ ha hb, 
  suffices : finset.range (1 + 1) = {0, 1}, rw this,
  simp only [finset.sum_insert, finset.mem_singleton, nat.zero_ne_one, not_false_iff, 
    tsub_zero, finset.sum_singleton, tsub_self],
  rw [hI.dpow_zero ha, hI.dpow_one ha, hJ.dpow_zero hb, hJ.dpow_one hb],
  ring,
  { rw [finset.range_succ, finset.range_one], ext k, simp, exact or.comm, },
end,
dpow_mem := 
begin
  intros n hn x,
  rw [ideal.add_eq_sup, submodule.mem_sup], 
  rintro ⟨a, ha, b, hb, rfl⟩, 
  rw dpow_ideal_add_eq hI hJ hIJ _ ha hb, 
  apply submodule.sum_mem (I ⊔ J),
  intros k hk,
  cases not_eq_or_aux hn hk with hk hk,
  { apply submodule.mem_sup_left, apply ideal.mul_mem_right, 
    exact hI.dpow_mem hk ha,  },
  { apply submodule.mem_sup_right, apply ideal.mul_mem_left,
    exact hJ.dpow_mem hk hb, },
end,
dpow_add := 
begin
  intros n x y,
  rw [ideal.add_eq_sup, submodule.mem_sup], 
  rintro ⟨a, ha, b, hb, rfl⟩, 
  rw [submodule.mem_sup],
  rintro ⟨a', ha', b', hb', rfl⟩, 
  rw add_add_add_comm a b a' b',
  rw dpow_ideal_add_eq hI hJ hIJ n (submodule.add_mem I ha ha') (submodule.add_mem J hb hb'),

  let f : ℕ × ℕ × ℕ × ℕ → A := λ ⟨i,j,k,l⟩, 
    (hI.dpow i a) * (hI.dpow j a') * (hJ.dpow k b) * (hJ.dpow l b'), 
  have hf1 : ∀ (k ∈ finset.range (n + 1)),
    hI.dpow k (a + a') * hJ.dpow (n - k) (b + b') = 
    (finset.range (k + 1)).sum (λ i, (finset.range (n - k + 1)).sum (λ l, 
    hI.dpow i a * hI.dpow (k - i) a' * hJ.dpow l b * hJ.dpow (n - k - l) b')),
  { intros k hk, 
    rw hI.dpow_add k ha ha', rw hJ.dpow_add (n - k) hb hb', 
    rw finset.sum_mul, 
    apply finset.sum_congr rfl,
    intros i hi,
    rw finset.mul_sum,
    apply finset.sum_congr rfl,
    intros l hl,
    ring, },
  rw finset.sum_congr rfl hf1, 
  have hf2 : ∀ (k ∈ finset.range (n + 1)),
    hI.dpow_ideal_add hJ k (a + b) * hI.dpow_ideal_add hJ (n - k) (a' + b') = 
    (finset.range (k + 1)).sum (λ i, (finset.range (n - k + 1)).sum (λ l, 
    hI.dpow i a * hI.dpow l a' * hJ.dpow (k - i) b * hJ.dpow (n - k - l) b')),
  { intros k hk,
    rw dpow_ideal_add_eq hI hJ hIJ k ha hb,
    rw dpow_ideal_add_eq hI hJ hIJ (n - k) ha' hb',
    rw finset.sum_mul,
    apply finset.sum_congr rfl,
    intros i hi,
    rw finset.mul_sum,
    apply finset.sum_congr rfl,
    intros j hj,
    ring, },
  rw finset.sum_congr rfl hf2, 
  convert finset.sum_4_rw f n,
end,
dpow_smul := 
begin
  intros n c x,
  rw [ideal.add_eq_sup, submodule.mem_sup], 
  rintro ⟨a, ha, b, hb, rfl⟩, 
  rw dpow_ideal_add_eq hI hJ hIJ n ha hb, 
  rw mul_add, 
  rw dpow_ideal_add_eq hI hJ hIJ n (ideal.mul_mem_left I c ha) (ideal.mul_mem_left J c hb),
  rw finset.mul_sum, 
  apply finset.sum_congr rfl,
  intros k hk,
  simp only [finset.mem_range, nat.lt_succ_iff] at hk,
  rw hI.dpow_smul, rw hJ.dpow_smul, 
  simp only [← mul_assoc], 
  apply congr_arg2 (*) _ rfl,
  rw [mul_comm, ← mul_assoc], 
  apply congr_arg2 (*) _ rfl,
  rw [← pow_add, nat.sub_add_cancel hk], 
  exact hb,
  exact ha,
end,
dpow_mul := 
begin
  intros m n x,
  rw [ideal.add_eq_sup, submodule.mem_sup], 
  rintro ⟨a, ha, b, hb, rfl⟩, 
  rw dpow_ideal_add_eq hI hJ hIJ m ha hb, 
  rw dpow_ideal_add_eq hI hJ hIJ n ha hb, 
  rw finset.sum_mul, simp_rw finset.mul_sum,
  rw ← finset.sum_product',
  have hf : ∀ (xy : ℕ × ℕ) (hxy : xy ∈ (finset.range (m+1)).product (finset.range (n + 1))),
    hI.dpow xy.fst a * hJ.dpow (m - xy.fst) b * (hI.dpow xy.snd a * hJ.dpow (n -xy.snd) b)
    = ((xy.snd + xy.fst).choose xy.fst) * hI.dpow (xy.snd + xy.fst) a 
      *  (( n - xy.snd + (m - xy.fst)).choose (m - xy.fst)) * (hJ.dpow (n - xy.snd + (m - xy.fst)) b),
     { intros xy hxy, 
    have fI :=  hI.dpow_mul xy.fst xy.snd ha,
    have fJ := hJ.dpow_mul (m - xy.fst) (n - xy.snd) hb,
    rw mul_assoc,
    rw ← mul_assoc (hJ.dpow (m - xy.fst) b) _ _,
    rw mul_comm (hJ.dpow _ b) _,
    rw mul_assoc,
    rw hJ.dpow_mul _ _ hb,
    rw ← mul_assoc,
    rw hI.dpow_mul _ _ ha,
    simp only [mul_assoc], },
    rw finset.sum_congr rfl hf,
    let s : ℕ × ℕ → ℕ := λ xy, xy.fst + xy.snd,
    have hs : ∀ (xy ∈ (finset.range (m+1)).product (finset.range (n+1))),
      s xy ∈ finset.range (m + n + 1),
    { intros xy hxy,
      dsimp [s],
      simp only [finset.mem_product, finset.mem_range, nat.lt_succ_iff] at hxy ⊢,
      apply nat.add_le_add hxy.1 hxy.2,},
    rw ←  finset.sum_fiberwise_of_maps_to hs,
    let g : ℕ → A := λ (y : ℕ), (finset.filter (λ (x : ℕ × ℕ), (λ (xy : ℕ × ℕ), s xy) x = y)
   ((finset.range (m + 1)).product (finset.range (n + 1)))).sum
  (λ (x : ℕ × ℕ),
     ↑((x.snd + x.fst).choose x.fst) * hI.dpow (x.snd + x.fst) a * ↑((n - x.snd + (m - x.fst)).choose (m - x.fst)) *
       hJ.dpow (n - x.snd + (m - x.fst)) b),
    have hg : ∀ (y : ℕ), g y =
      (finset.filter (λ (x : ℕ × ℕ), (λ (xy : ℕ × ℕ), s xy) x = y)
  ((finset.range (m + 1)).product (finset.range (n + 1)))).sum
      (λ (x : ℕ × ℕ), (y.choose x.fst) * ((n + m - y).choose (m - x.fst))) 
        * (hI.dpow y a) * hJ.dpow (n + m - y) b,
    { intro y,
      dsimp [g, s],
      rw finset.sum_mul, rw finset.sum_mul,
      refine finset.sum_congr rfl _,
      intros xy hxy,
      simp only [finset.mem_filter, finset.mem_product, finset.mem_range, nat.lt_succ_iff] at hxy,
      rw [add_comm xy.snd xy.fst, hxy.2],
      suffices : n - xy.snd + (m - xy.fst) = n + m - y,
      rw this, ring,
      { apply symm,
        rw nat.sub_eq_iff_eq_add , rw ← hxy.2,
        rw ← add_assoc, 
        rw add_assoc (n - xy.snd),
        rw nat.sub_add_cancel hxy.1.1,
        rw add_assoc,
        rw add_comm m _,
        rw ← add_assoc,
        rw nat.sub_add_cancel hxy.1.2,
        rw ← hxy.2, rw add_comm n m, exact nat.add_le_add hxy.1.1 hxy.1.2, },},
    dsimp [g] at hg,
    rw finset.sum_congr rfl (λ y h, hg y),
  rw dpow_ideal_add_eq hI hJ hIJ (n + m) ha hb,
  rw finset.mul_sum,
  apply finset.sum_congr,
  { rw add_comm m n, },
  intros y hy,
  simp only [mul_assoc],
  apply congr_arg2, 
  { dsimp [s], 
    simp only [finset.mem_range, nat.lt_succ_iff] at hy,
    rw add_comm n m at hy,
    rw add_comm n m,
    rw ← comb_lemma m n y hy, 
    simp only [nat.cast_sum, nat.cast_mul], },
  refl,
end,
dpow_comp := sorry }



/- Questions 

* decide if the hypothesis for (n : ℕ) in dp-lemmas should be `n ≠ 0` or `0 < n`
 -- Decided !
* should we use • instead of * in `dpow_smul` ?
 -- We keep a * 
-/

/- 3.7 Lemma. Suppose R is a ring, В and С are R-algebras, and
I ⊆ В and J ⊆ С are augmentation ideals (i.e. there is a section of В → B/I, etc.) 
with P.D. structures γ and δ, respectively. 
Then the ideal К = Ker (В ⊗ С → B/I ⊗ C/J) has a unique P.D. structure ε 
such that (B,I,γ) → (В ⊗ С,К,ε) and
(C,J,δ) → (B ⊗ C,K,ε) are P.D. morphisms. -/

/- Lemma 3.7 of [BO] -> Change to 1.7.1 -/

open_locale tensor_product

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
  dpow_add  := sorry,
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

/- Comparison with Berthelot, Coho. cristalline

1.1 : done
1.2.1 (M) : follows from 1.2.7 - done (for ℚ-algebras).
1.2.2 (*) : To be added
1.2.4 : To be added if Cohen/Witt vectors rings exist
1.2.7 (M) : done
1.3 (pd -morphism) : done
1.3.1 : To be added (needs limits of rings)

1.4 : To be added, but difficult
1.5.: depends on 1.4  

1.6 : sub-pd-ideal : done
1.6.1 (A) : to be added [Done !]
1.6.2 (*) : to be added [That was already done ! dpow_quot]
1.6.4 (A) : to be added
(should we add the remark on page 33)
1.6.5 (A): to be added

1.7 : tensor product, see Roby

1.8 (M) to be added 

-/