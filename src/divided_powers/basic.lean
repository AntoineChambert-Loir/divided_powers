/- ACL and MIdFF, Lean 2022 meeting at Icerm -/
import ring_theory.power_series.basic
import algebra_lemmas
import combinatorics_lemmas
import data.nat.choose.multinomial

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

* N. Roby (1963). « Lois polynomes et lois formelles en théorie des modules ». Annales scientifiques de l’École Normale Supérieure 80 (3): 213‑348. https://doi.org/10.24033/asens.1124.

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

namespace divided_powers

section basic_lemmas

variables {A : Type*} [comm_ring A] {I : ideal A}

def dpow_exp (hI : divided_powers I) (a : A) := power_series.mk (λ n, hI.dpow n a)

lemma add_dpow_exp (hI : divided_powers I) {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
  hI.dpow_exp (a + b) = hI.dpow_exp (a) * hI.dpow_exp (b) :=
begin   
  simp only [dpow_exp],
  ext,
  simp only [power_series.coeff_mk, power_series.coeff_mul],
  rw [hI.dpow_add n ha hb, finset.nat.sum_antidiagonal_eq_sum_range_succ_mk], 
end

lemma eq_of_eq_on_ideal (hI : divided_powers I) (hI' : divided_powers I) 
  (h_eq : ∀ (n : ℕ) {x : A} (hx : x ∈ I), hI.dpow n x = hI'.dpow n x ) : hI = hI' :=
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

-- Golfed version of definition
noncomputable def dpow_of_dpow_exp (I : ideal A) (ε : I → power_series A) : ℕ → A → A := 
λ n, function.extend (λ (a : I), (a : A)) (λ (a : I), power_series.coeff A n (ε a)) 0

def divided_powers_of_dpow_exp (I : ideal A) (ε : I → power_series A)
  (hε_add : ∀ (a b : I), ε(a + b) = ε(a) * ε(b))
  (hε_zero : ε(0) = 1) -/


variable (hI : divided_powers I)

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
by rw [← mul_zero (0 : A), hI.dpow_smul n I.zero_mem, zero_pow' n hn, zero_mul, zero_mul]

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
lemma coincide_on_smul {J : ideal A} (hJ : divided_powers J) {n : ℕ} {a : A} (ha : a ∈ I • J) : 
  hI.dpow n a = hJ.dpow n a :=
begin
  revert n,
  apply submodule.smul_induction_on' ha,
  { intros a ha b hb n, 
    rw [algebra.id.smul_eq_mul, hJ.dpow_smul n hb, mul_comm a b, hI.dpow_smul n ha, 
      ← hJ.factorial_mul_dpow_eq_pow n b hb, ← hI.factorial_mul_dpow_eq_pow n a ha],
    ring, },
  { intros x hx y hy hx' hy' n, 
    rw [hI.dpow_add n (ideal.mul_le_right hx) (ideal.mul_le_right hy), 
      hJ.dpow_add n (ideal.mul_le_left hx) (ideal.mul_le_left hy)], 
    apply finset.sum_congr rfl,
    intros k hk,
    rw [hx', hy'], },
end

open finset

-- Also : can it be used to deduce dpow_comp from the rest?
/-- A generic “multinomial” theorem for divided powers — but without multinomial coefficients 
  — using only dpow_zero, dpow_add and dpow_eval_zero  -/
lemma sum_dpow_aux (dpow : ℕ → A → A) (dpow_zero : ∀ {x} (hx : x ∈ I), dpow 0 x = 1)
  (dpow_add : ∀ n {x y} (hx : x ∈ I) (hy : y ∈ I) , dpow n (x + y) =
    finset.sum (finset.range (n + 1)) (λ k, (dpow k x) * (dpow (n - k) y)))
  (dpow_eval_zero : ∀ {n : ℕ} (hn : n ≠ 0), dpow n 0 = 0) {ι : Type*} [decidable_eq ι]
  {s : finset ι} {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) : 
  ∀ (n : ℕ), dpow n (s.sum x) = 
    (finset.sym s n).sum (λ k, s.prod (λ i, dpow (multiset.count i k) (x i))) := 
begin
  induction s using finset.induction with a s ha ih,
  { rw sum_empty,
    rintro (_ | n),
    { rw [dpow_zero (I.zero_mem), sum_unique_nonempty, prod_empty],
      exact univ_nonempty },
    { rw [dpow_eval_zero (nat.succ_ne_zero n), sym_empty, sum_empty], }},
  { have hx' : ∀ i, i ∈ s → x i ∈ I := 
    λ i hi, hx i (finset.mem_insert_of_mem hi), 
    intro n,
    simp_rw [sum_insert ha, 
      dpow_add n (hx a (finset.mem_insert_self a s)) 
        (I.sum_mem (λ i, hx' i)),
      sum_range, ih hx', mul_sum, sum_sigma'], 

    refine (sum_bij' 
      (λ m _, sym.filter_ne a m) 
      (λ m hm, finset.mem_sigma.2 ⟨mem_univ _, _⟩)
      (λ m hm, _) 
      (λ m _, m.2.fill a m.1)
      _ 
      (λ m _, m.fill_filter_ne a) 
      -- explicit arguments above rather than m.fill_filter_ne a
      -- adjust once multinomial has been incorporated to mathlib
      (λ m hm, _)).symm,
    
  -- #3
    { convert sym_filter_ne_mem a hm, rw erase_insert ha },
  -- #4
    { dsimp only [sym.filter_ne, fin.coe_mk],
      rw finset.prod_insert ha, 
      apply congr_arg2 _ rfl, 
      apply finset.prod_congr rfl,
      intros i hi, simp only [subtype.val_eq_coe, sym.mk_coe], 
      apply congr_arg2 _ _ rfl,
      rw multiset.count_filter,
      rw if_pos _, 
      intro hi', apply ha, rw hi', exact hi, },
      
    { exact λ m hm, sym_fill_mem a (mem_sigma.1 hm).2 },
    { exact sym.filter_ne_fill a m (mt (mem_sym_iff.1 (mem_sigma.1 hm).2 a) ha) }},
end

/-- A “multinomial” theorem for divided powers — without multinomial coefficients -/
lemma sum_dpow {ι : Type*} [decidable_eq ι] {s : finset ι} {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) :
  ∀ (n : ℕ), hI.dpow n (s.sum x) = 
    (finset.sym s n).sum (λ k, s.prod (λ i, hI.dpow (multiset.count i k) (x i))) :=
sum_dpow_aux hI.dpow (λ x hx, hI.dpow_zero hx) 
  (λ n x y hx hy, hI.dpow_add n hx hy) (λ n hn, hI.dpow_eval_zero hn) hx

lemma prod_dpow_self {ι : Type*} [decidable_eq ι] {s : finset ι} {n : ι → ℕ} (a : A) (ha : a ∈ I) :
  s.prod (λ i, hI.dpow (n i) a) = nat.multinomial s n * hI.dpow (s.sum n) a :=
begin
  induction s using finset.induction with i s hi ih,
  { rw [finset.prod_empty, finset.sum_empty, hI.dpow_zero ha, nat.multinomial_nil, 
      nat.cast_one, mul_one] },
  { rw [finset.prod_insert hi, ih, ← mul_assoc, mul_comm (hI.dpow _ a), mul_assoc,
      hI.dpow_mul _ _ ha, ← finset.sum_insert hi, ← mul_assoc],
    apply congr_arg2 _ _ rfl,
    rw [mul_comm, nat.multinomial_insert s n hi, finset.sum_insert hi, nat.cast_mul], },
end

end basic_lemmas

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
 (A) : rewrite_4_sums -- Done, I think, but how could we simplify these lemmas?

(A) Simplify, 
  remove not_eq_or_aux (see REMOVE or MOVE) -- DONE
  Prove uniqueness of pd-structure when possible
    (ideal_add [Done], dpow_quot [Done])
(M) Complete the lattice structure

-/

example (M : Type*) [add_monoid M] : add_monoid (with_top M) := by refine with_top.add_monoid

/- Roby (1965):
 - Pregraded algebra (using mathlib's graded_algebra) - with_top unit (later, if needed)
 - Tensor product of graded algebras is a graded algebra
 - Add III' explicitly.
 - Proposition 1 -- I think this is essentially Lemma 3.6 of [BO].
 - Proposition 2
 - Proposition 3

 I just noticed that we are using dp and pd in different names, we should pick a convention.
-/

/- 
Idea of generalizing the theory to more general divisors systems
modeling x^n/n!, x^n/p^n, etc.
but it is not clear what to consider
Also, not clear it can really be done…

structure divisor_system {R : Type*} [comm_ring R] := 
(dpow_choose : ℕ → ℕ → R)
(dpow_mchoose : ℕ → ℕ → R)
-- (conditions : Prop)
Two options :
1) dpow n x = x^n/(c n)
Examples : c n = n.factorial,  c n = p ^ n
2) dpow n x = x ^ n / (d 1 * d 2 * ... * d n)
Examples : d n = n,  d n = p

dpow n (x + y) = (x+y)^n / c n
 = sum  (n.choose k) x ^(n -k) y ^k / c n
 = sum [(n.choose k) (c k) (c (n-k)) / c n] dpow (n - k) x * dpow k y 

  Case 1 : dpow_choose n k = 1 ;  case 2 : dpow_choose n k = choose

dpow m x * dpow n x = x ^ m * x ^ n / c m * c n
  = dpow (m + n) x * (c (n+m) / c m * c n)

   Case 1 : coeff = (n+m).choose m ; Case 2 :  = 1

dpow m (dpow n x) = (x ^n / c n) ^ m / c m = x ^ (m n) / ((c n ^ m) * c m)
 = [ ] * dpow (m n) x
  with [ ] = c (m n)/ (c n)^m (c m)

  Case 1 : [ ] = mchoose m n, case 2 : p^ (-m)

-/
