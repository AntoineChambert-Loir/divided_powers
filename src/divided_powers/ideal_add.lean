import divided_powers.rat_algebra
import basic_lemmas

open finset

namespace divided_powers

variables {A : Type*} [comm_ring A] {I : ideal A} (hI : divided_powers I)

namespace ideal_add

/-- Some complicated numerical coefficients for the proof of ideal_add.dpow_comp -/
private
def cnik := λ (n i : ℕ) (k : multiset ℕ),
    ite (i = 0) 
        (mchoose (multiset.count i k) n)
        (ite (i = n) 
          (mchoose (multiset.count i k) n) 
          ((multiset.count i k).factorial * (mchoose (multiset.count i k) i) * (mchoose (multiset.count i k) (n - i))))


/-- Divided power function on a sup of two ideals -/
noncomputable
def dpow {J : ideal A} (hJ : divided_powers J) :
  ℕ → A → A := λ n,
function.extend 
  (λ ⟨a, b⟩, (a : A) + (b : A) : I × J → A)
  (λ ⟨a, b⟩, finset.sum (finset.range (n + 1)) 
    (λ k, (hI.dpow k (a : A)) * (hJ.dpow (n - k) (b : A))))
  (λ (a : A), 0)
 
/-- Independence on choices for `dpow` -/
lemma dpow_eq_aux {J : ideal A} (hJ : divided_powers J)
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
  have Ha'c : (finset.range (n + 1)).sum (λ (k : ℕ), hI.dpow k (a' + c) * hJ.dpow (n - k) b)
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
      rw tsub_tsub_tsub_cancel_left h.1, 
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

lemma dpow_eq {J : ideal A} (hJ : divided_powers J)
  (hIJ : ∀ (n : ℕ) (a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a)
  (n) {a} (ha : a ∈ I) {b} (hb : b ∈ J) : 
  dpow hI hJ n (a + b) =
    finset.sum (finset.range (n + 1)) (λ k, (hI.dpow k a) * (hJ.dpow (n - k) b))  :=
begin
  simp only [dpow],
  convert function.extend_apply_first _ _ _ _ (⟨(⟨a, ha⟩ : I), (⟨b, hb⟩ : J)⟩ : I × J),
  rintros ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩, 
  intro H,
  refine dpow_eq_aux hI hJ _ n ha hb ha' hb' H,
  { intros n a, exact hIJ n a, },
end

lemma dpow_eq_of_mem_left {J : ideal A} (hJ : divided_powers J)
  (hIJ : ∀ (n : ℕ) (a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a)
  (n : ℕ) {x : A} (hx : x ∈ I) : dpow hI hJ n x = hI.dpow n x := 
begin
  rw ← add_zero x, 
  rw dpow_eq, 
  { rw finset.sum_eq_single n, 
    { simp only [nat.sub_self, add_zero, hJ.dpow_zero],
      rw [hJ.dpow_zero (J.zero_mem), mul_one], },
    { intros b hb hb', 
      rw [hJ.dpow_eval_zero, mul_zero], 
      intro h, apply hb', 
      rw [finset.mem_range, nat.lt_succ_iff] at hb, 
      rw [← nat.sub_add_cancel hb, h, zero_add], }, 
    { intro hn, exfalso, apply hn, rw finset.mem_range, 
      exact lt_add_one n, } },
  exact hIJ, exact hx, exact J.zero_mem,
end

lemma dpow_eq_of_mem_right {J : ideal A} (hJ : divided_powers J)
  (hIJ : ∀ (n : ℕ) (a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a)
  (n : ℕ) {x : A} (hx : x ∈ J) : dpow hI hJ n x = hJ.dpow n x := 
begin
  rw ← zero_add x, 
  rw dpow_eq, 
  { rw finset.sum_eq_single 0, 
    { simp only [nat.sub_zero, zero_add, hI.dpow_zero (I.zero_mem), one_mul], },
    { intros b hb hb', 
      rw [hI.dpow_eval_zero, zero_mul], exact hb', }, 
    { intro hn, exfalso, apply hn, rw finset.mem_range, 
      exact ne_zero.pos (n + 1), } },
  exact hIJ, exact I.zero_mem, exact hx,
end

lemma dpow_zero {J : ideal A} (hJ : divided_powers J) 
  (hIJ :  ∀ (n : ℕ) (a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a) :
∀ (x : A) (hx : x ∈ I + J), dpow hI hJ 0 x = 1:=
begin
  intro x,
  rw [ideal.add_eq_sup, submodule.mem_sup], 
  rintro ⟨a, ha, b, hb, rfl⟩, 
  rw dpow_eq hI hJ hIJ (0 : ℕ) ha hb, 
  simp only [finset.range_one, zero_tsub, finset.sum_singleton],
  rw [hI.dpow_zero ha, hJ.dpow_zero hb, mul_one],
end

lemma dpow_mul {J : ideal A} (hJ : divided_powers J)
(hIJ : ∀ (n : ℕ) (a : A), a ∈ I ⊓ J → hI.dpow n a = hJ.dpow n a)
(m n : ℕ) {x : A} : x ∈ I + J →
    dpow hI hJ m x * dpow hI hJ n x =
      ↑((m + n).choose m) * dpow hI hJ (m + n) x :=
begin
  rw [ideal.add_eq_sup, submodule.mem_sup],
  rintro ⟨a, ha, b, hb, rfl⟩, 
  rw dpow_eq hI hJ hIJ m ha hb, 
  rw ← finset.nat.sum_antidiagonal_eq_sum_range_succ
    (λ i j, hI.dpow i a * hJ.dpow j b),
  rw dpow_eq hI hJ hIJ n ha hb, 
  rw ← finset.nat.sum_antidiagonal_eq_sum_range_succ
    (λ k l, hI.dpow k a * hJ.dpow l b),
  rw finset.sum_mul, simp_rw finset.mul_sum,
  rw ← finset.sum_product',

  have hf : ∀ (x : (ℕ × ℕ) × (ℕ × ℕ)), 
    hI.dpow x.fst.fst a * hJ.dpow x.fst.snd b * (hI.dpow x.snd.fst a * hJ.dpow x.snd.snd b)
    = (x.fst.fst + x.snd.fst).choose (x.fst.fst) * (x.fst.snd + x.snd.snd).choose x.fst.snd
     * hI.dpow (x.fst.fst + x.snd.fst) a * hJ.dpow (x.fst.snd + x.snd.snd) b,
  { rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩,
    dsimp, 
    rw mul_assoc, rw ← mul_assoc (hJ.dpow j b) _ _, rw mul_comm (hJ.dpow j b),
    rw mul_assoc, rw hJ.dpow_mul j l hb,
    rw ← mul_assoc, rw hI.dpow_mul i k ha,
    ring, },

    rw finset.sum_congr rfl (λ x hx, hf x),

    let s : (ℕ × ℕ) × (ℕ × ℕ) → (ℕ × ℕ) := λ x, 
      ⟨x.fst.fst + x.snd.fst, x.fst.snd + x.snd.snd⟩, 
    have hs : ∀ (x ∈ finset.nat.antidiagonal m ×ˢ finset.nat.antidiagonal n), 
      s x ∈ finset.nat.antidiagonal (m + n),
    { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ h, dsimp [s],
      simp only [finset.nat.mem_antidiagonal, finset.mem_product] at h ⊢,
      rw [add_assoc, ← add_assoc k j l, add_comm k _, add_assoc, h.2, ← add_assoc, h.1], }, 
    rw ←  finset.sum_fiberwise_of_maps_to hs,
    

    have hs' : (finset.nat.antidiagonal (m + n)).sum
    (λ (y : ℕ × ℕ),
       (finset.filter (λ (x : (ℕ × ℕ) × ℕ × ℕ), (λ (x : (ℕ × ℕ) × ℕ × ℕ), s x) x = y)
          (finset.nat.antidiagonal m ×ˢ finset.nat.antidiagonal n)).sum
         (λ (x : (ℕ × ℕ) × ℕ × ℕ),
            ↑((x.fst.fst + x.snd.fst).choose x.fst.fst) * 
            ↑((x.fst.snd + x.snd.snd).choose x.fst.snd) * hI.dpow (x.fst.fst + x.snd.fst) a *
              hJ.dpow (x.fst.snd + x.snd.snd) b)) 
  = (finset.nat.antidiagonal (m + n)).sum
    (λ (y : ℕ × ℕ),
       (finset.filter 
          (λ (x : (ℕ × ℕ) × ℕ × ℕ), (λ (x : (ℕ × ℕ) × ℕ × ℕ), s x) x = y)
          (finset.nat.antidiagonal m ×ˢ finset.nat.antidiagonal n)).sum
         (λ (x : (ℕ × ℕ) × ℕ × ℕ),
            ↑((y.fst).choose x.fst.fst) * ↑((y.snd).choose x.fst.snd)) *
                hI.dpow (y.fst) a *
              hJ.dpow (y.snd) b),
{ apply finset.sum_congr rfl, rintros ⟨u,v⟩ hy,
  simp only [finset.sum_mul], 
  apply finset.sum_congr rfl, rintros ⟨⟨i,j⟩,⟨k,l⟩⟩ hx,
  simp [s] at hx,
  dsimp,
  rw hx.2.1, rw hx.2.2, },
  rw hs',

  rw dpow_eq hI hJ hIJ (m + n) ha hb, 
  rw ← finset.nat.sum_antidiagonal_eq_sum_range_succ
    (λ i j, hI.dpow i a * hJ.dpow j b),
  rw finset.mul_sum,
  apply finset.sum_congr rfl, rintros ⟨u,v⟩ h,
  -- simp only [nat.cast_sum, nat.cast_mul],
  -- rw finset.sum_mul, simp_rw finset.mul_sum,
  simp only [prod.mk.inj_iff],
  rw ← mul_assoc,
  apply congr_arg2 _ _ rfl,
  apply congr_arg2 _ _ rfl,


  simp only [← nat.cast_sum, ← nat.cast_mul],
  apply congr_arg,

  simp only [finset.nat.mem_antidiagonal] at h,

  rw rewriting_4_fold_sums h.symm (λ x, u.choose x.fst * v.choose x.snd) rfl _,
  { rw ← nat.add_choose_eq, rw h, },

  { intros x h, 
    cases h with h h;
    { simp only [nat.choose_eq_zero_of_lt h, zero_mul, mul_zero], } },
end

lemma dpow_mem {J : ideal A} (hJ : divided_powers J) 
  (hIJ :  ∀ (n : ℕ) (a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a) :
  ∀ {n : ℕ} (hn : n ≠ 0) {x : A} (hx : x ∈ I + J), 
  dpow hI hJ n x ∈ I + J :=
begin
  intros n hn x,
  rw [ideal.add_eq_sup, submodule.mem_sup], 
  rintro ⟨a, ha, b, hb, rfl⟩, 
  rw dpow_eq hI hJ hIJ _ ha hb, 
  apply submodule.sum_mem (I ⊔ J),
  intros k hk,
  by_cases hk0 : k = 0,
  { rw hk0, --rw tsub_zero,
    apply submodule.mem_sup_right, apply ideal.mul_mem_left,
    exact hJ.dpow_mem hn hb, },
  { apply submodule.mem_sup_left, apply ideal.mul_mem_right, 
    exact hI.dpow_mem hk0 ha, }
  end

lemma dpow_smul {J : ideal A} (hJ : divided_powers J) 
  (hIJ :  ∀ (n : ℕ) (a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a) :
∀ (n : ℕ) {c x : A} (hx : x ∈ I + J), 
  dpow hI hJ n (c * x) = (c ^ n) * dpow hI hJ n x :=
begin
  intros n c x,
  rw [ideal.add_eq_sup, submodule.mem_sup], 
  rintro ⟨a, ha, b, hb, rfl⟩, 
  rw dpow_eq hI hJ hIJ n ha hb, 
  rw mul_add, 
  rw dpow_eq hI hJ hIJ n (ideal.mul_mem_left I c ha) (ideal.mul_mem_left J c hb),
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
end

lemma dpow_add {J : ideal A} (hJ : divided_powers J) 
  (hIJ :  ∀ (n : ℕ) (a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a) : 
  ∀ (n : ℕ) {x y : A} (hx : x ∈ I + J) (hy : y ∈ I + J),
dpow hI hJ n (x + y) = finset.sum (finset.range (n + 1)) 
  (λ k, (dpow hI hJ k x) * (dpow hI hJ (n - k) y)) :=
begin
  intros n x y,
  rw [ideal.add_eq_sup, submodule.mem_sup], 
  rintro ⟨a, ha, b, hb, rfl⟩, 
  rw [submodule.mem_sup],
  rintro ⟨a', ha', b', hb', rfl⟩, 
  rw add_add_add_comm a b a' b',
  rw dpow_eq hI hJ hIJ n (submodule.add_mem I ha ha') (submodule.add_mem J hb hb'),

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
    dpow hI hJ k (a + b) * dpow hI hJ (n - k) (a' + b') = 
    (finset.range (k + 1)).sum (λ i, (finset.range (n - k + 1)).sum (λ l, 
    hI.dpow i a * hI.dpow l a' * hJ.dpow (k - i) b * hJ.dpow (n - k - l) b')),
  { intros k hk,
    rw dpow_eq hI hJ hIJ k ha hb,
    rw dpow_eq hI hJ hIJ (n - k) ha' hb',
    rw finset.sum_mul,
    apply finset.sum_congr rfl,
    intros i hi,
    rw finset.mul_sum,
    apply finset.sum_congr rfl,
    intros j hj,
    ring, },
  rw finset.sum_congr rfl hf2, 
  convert finset.sum_4_rw f n,
end




  /- si on développe, on obtient une somme indexée par
  les c : fin (n+1) → ℕ  de somme m 
  de  ∏   (hI.dpow k a)^(c k) (hJ.dpow (n-k) b)^(c k) 
  sans coefficients multinomiaux !
    par récurrence, en utilisant dpow_mul,
    a^[k] a^[k'] = (k + k')!/k! k'! a^ [k + k']
    a^[k] a^[k'] a^[k''] = (k+k'+k'')!/k!k'!k''!
   ∏ (hI.dpow k a)^(c k) = multinomial (k ^ (c k)) hI.dpow (∑ k (c k)) a
    tandis que Π (hJ.dpow (n-k) b)^(c k)
     = multinomial ((n-k)^ (c k)) hJ.dpow (∑ (n-k) c k) b
    la puissance est n∑ c k - ∑ k (c k) = n m - ∑ k (c k)
    = N!/∏ k!^(c k) * (nm - N)!/∏ (n-k)!^(c k) * a^[N] * b^[nm -N]
    
    Lorsqu'on somme sur les c de somme m et de poids N,
    il faudra trouver (mchoose m n)…
    Il est probable que le plus facile est d'identifier
    ce qui se passe pour Q[a,b] avec sa structure de puissances divisées canonique.


  -/

lemma dpow_comp_aux
{J : ideal A} (hJ : divided_powers J) 
  (hIJ :  ∀ (n : ℕ) (a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a) 
  (m : ℕ) {n : ℕ} (hn : n ≠ 0) 
{a : A} (ha : a ∈ I) {b : A} (hb : b ∈ J) :
dpow hI hJ m (dpow hI hJ n (a + b)) = 
finset.sum (finset.range (m * n + 1))
(λ (p : ℕ),
(finset.filter (λ (l : sym ℕ m), 
  (finset.range (n + 1)).sum (λ i, multiset.count i ↑l * i) = p) ((finset.range (n + 1)).sym m)).sum
  (λ (x : sym ℕ m),
    (finset.range (n + 1)).prod (λ (i : ℕ), (cnik n i ↑x))
    * (nat.multinomial (finset.range (n + 1)) (λ (i : ℕ), multiset.count i ↑x * i))
    * (nat.multinomial (finset.range (n + 1)) (λ (i : ℕ), multiset.count i ↑x * (n - i)))) * hI.dpow p a * hJ.dpow (m * n - p) b) 
:= 
begin
  rw dpow_eq hI hJ hIJ n ha hb, 
  rw dpow_sum_aux (dpow hI hJ) (dpow_zero hI hJ hIJ) (dpow_add hI hJ hIJ),
  
  /- i ≠0, n : 
   (a^[i]*b^[n-i])^[c i] 
    = a^[i]^ (c i) * (b^[n-i])^[c i]
    = (c i)! a^[i])^[c i] * b^[n-i]^[c i]
    = (c i)! * mchoose (i, c i) * mchoose (n-i, c i) 
    * a^[i * c i] * b^[(n-i) * c i]
  i = 0 : 
    (a^[0] * b^[n])^[c i]
     = b^[n]^[c i] = mchoose (c i) n * b ^[n * c i]
  i = n : 
    (a^[n] * b^[0]) ^[c i]
     = a^[n]^[c i] = mchoose (c i) n * a^[n * c i]
  -/

  have L1 : ∀ (k : sym ℕ m) (i : ℕ) (hi : i ∈ finset.range (n+1)),
    dpow hI hJ (multiset.count i ↑k) ((hI.dpow i a) * hJ.dpow (n-i) b)
    = (cnik n i ↑k) * hI.dpow ((multiset.count i ↑k) * i) a 
    * hJ.dpow ((multiset.count i ↑k) * (n - i)) b,
  { intros k i hi,
    simp only [cnik],
    by_cases hi2 : i = n,
    { rw hi2, rw nat.sub_self, 
      rw if_neg hn, rw if_pos rfl,
      simp only [mchoose_zero',mul_one, nat.cast_one, mul_zero, hJ.dpow_zero hb], 
      rw dpow_eq_of_mem_left hI hJ hIJ _ (hI.dpow_mem hn ha),
      rw hI.dpow_comp _ hn ha, },
    have hi2' : n - i ≠ 0,
    { intro h, apply hi2, 
      rw [finset.mem_range, nat.lt_succ_iff] at hi, 
      rw [← nat.sub_add_cancel hi, h, zero_add], } ,
    by_cases hi1 : i = 0,
    { rw hi1, rw mchoose_zero', rw hI.dpow_zero ha, rw nat.sub_zero, rw one_mul, 
      rw if_pos rfl,
      rw dpow_eq_of_mem_right hI hJ hIJ _ (hJ.dpow_mem hn hb),
      rw hJ.dpow_comp _ hn hb,
      rw mul_zero,
      rw hI.dpow_zero ha, 
      simp only [nat.cast_one, one_mul, mul_one], },
    -- i ≠ 0  and i ≠ n  
    { rw if_neg hi1, rw if_neg hi2, 
      rw [mul_comm, dpow_smul hI hJ hIJ, mul_comm], 
      rw dpow_eq_of_mem_left hI hJ hIJ _ (hI.dpow_mem hi1 ha), 
      rw ← hJ.factorial_mul_dpow_eq_pow (multiset.count i k),
      rw hI.dpow_comp _ hi1 ha, 
      rw hJ.dpow_comp _ hi2' hb, 
      simp only [← mul_assoc], apply congr_arg2 _ _ rfl,
      simp only [mul_assoc], rw mul_comm (hI.dpow _ a), 
      simp only [←  mul_assoc],
      apply congr_arg2 _ _ rfl,
      rw mul_comm ↑(mchoose _ i),
      simp only [nat.cast_mul],
      exact hJ.dpow_mem hi2' hb, 
      apply submodule.mem_sup_left, exact hI.dpow_mem hi1 ha, }, },
  

  let φ : sym ℕ m → ℕ  := λ k, (finset.range (n + 1)).sum (λ i, multiset.count i ↑k * i), 
  suffices hφ : ∀ (k : sym ℕ m), k ∈ (finset.range (n + 1)).sym m → 
    φ k ∈ finset.range (m * n + 1),
  
  rw ← finset.sum_fiberwise_of_maps_to hφ _,

  suffices L4 : ∀(p : ℕ) (hp : p ∈ finset.range (m * n + 1)),
  (finset.filter (λ (x : sym ℕ m), (λ (k : sym ℕ m), φ k) x = p) ((finset.range (n + 1)).sym m)).sum
    (λ (x : sym ℕ m),
    (finset.range (n + 1)).prod (λ (i : ℕ), dpow hI hJ (multiset.count i ↑x) (hI.dpow i a * hJ.dpow (n - i) b)))
  = (finset.filter (λ (x : sym ℕ m), (λ (k : sym ℕ m), φ k) x = p) ((finset.range (n + 1)).sym m)).sum
  (λ (k : sym ℕ m),
  (finset.range (n + 1)).prod (λ (i : ℕ), ↑(cnik n i ↑k)) *
      ↑(nat.multinomial (finset.range (n + 1)) (λ (i : ℕ), multiset.count i ↑k * i)) *
            ↑(nat.multinomial (finset.range (n + 1)) (λ (i : ℕ), multiset.count i ↑k * (n - i))) *
          hI.dpow p a *
        hJ.dpow (m * n - p) b),

  rw finset.sum_congr rfl L4, 
  simp_rw finset.sum_mul, 

  { -- L4
    intros p hp, 
    apply finset.sum_congr rfl,
    intros k hk,
    rw finset.mem_filter at hk,
    rw finset.prod_congr rfl (L1 k),
    rw finset.prod_mul_distrib, 
    rw finset.prod_mul_distrib,
    rw hI.prod_dpow_self _ ha, 
    rw hJ.prod_dpow_self _ hb,
    simp only [mul_assoc], apply congr_arg2 _ rfl,
    apply congr_arg2 _ rfl,
    rw sum_range_sym_mul_compl hk.1, 
    simp only [← mul_assoc], 
    simp only [← hk.2, φ],  apply congr_arg2 _ _ rfl,
    rw mul_comm, 

    apply_instance, apply_instance, },
  { -- hφ
    intros k hk,
    simp only [φ, finset.mem_range, nat.lt_succ_iff],
    exact range_sym_weighted_sum_le k hk, },
  { intros n hn, 
    rw dpow_eq_of_mem_left hI hJ hIJ n (I.zero_mem), 
    exact dpow_eval_zero hI hn, },
  { intros i hi, 
    by_cases hi0 : i = 0,
    { rw hi0,
      apply submodule.mem_sup_right, apply ideal.mul_mem_left,
      exact hJ.dpow_mem hn hb, },
    { apply submodule.mem_sup_left, apply ideal.mul_mem_right, 
      exact hI.dpow_mem hi0 ha, }, },
end

open polynomial

open_locale classical

lemma polynomial.inv_C_eq_C_inv {R : Type*} [comm_ring R] (a : R) :
  ring.inverse (C a) = C (ring.inverse a) :=
begin
  simp only [ring.inverse],
  by_cases ha : is_unit a,
  { simp only [dif_pos ha], 
    have hCa : is_unit (C a), 
    { rw ← is_unit.unit_spec ha, 
      exact ring_hom.is_unit_map C ha, },
    rw [dif_pos hCa], 
    apply is_unit.mul_right_cancel hCa, 
    rw ← map_mul, 
    simp only [is_unit.coe_inv_mul, map_one], },
  { simp only [ring.inverse, dif_neg ha, map_zero],
    rw dif_neg, 
    intro hCa,  apply ha, 
    rw is_unit_iff_exists_inv at hCa ⊢,
    obtain ⟨b, hb⟩ := hCa, 
    use b.coeff 0,
    convert congr_arg2 coeff hb rfl,
    rw polynomial.coeff_C_mul ,   
    simp only [coeff_one_zero],},
end

lemma dpow_comp_coeffs {m n p : ℕ} (hn : n ≠ 0) (hp : p ≤ m * n): 
mchoose m n =
  (finset.filter (λ (l : sym ℕ m),
  (finset.range (n + 1)).sum (λ (i : ℕ), multiset.count i ↑l * i) = p)
      ((finset.range (n + 1)).sym m)).sum (λ (x : sym ℕ m),
        (finset.range (n + 1)).prod (λ (i : ℕ), (cnik n i ↑x)) 
        * ((nat.multinomial (finset.range (n + 1)) (λ (i : ℕ), multiset.count i ↑x * i))
        * (nat.multinomial (finset.range (n + 1)) (λ (i : ℕ), multiset.count i ↑x * (n - i))))) := 
begin
  rw ← mul_left_inj' (pos_iff_ne_zero.mp (nat.choose_pos hp)),

  have : function.injective (coe : ℕ → ℚ) := nat.cast_injective,
  apply this, 
  simp only [nat.cast_mul, nat.cast_sum, nat.cast_prod, nat.cast_eq_zero], 
  
  conv_lhs { rw ← polynomial.coeff_X_add_one_pow ℚ (m * n) p, },
  let A := polynomial ℚ,
--   let X : A :=  1 1,
  let I : ideal A := ⊤,
  let hI : divided_powers I := rat_algebra.divided_powers ⊤,
  let hII : ∀ (n : ℕ) (a : A), a ∈ I ⊓ I → hI.dpow n a = hI.dpow n a := λ n a ha, rfl, 
  let h1 : (1 : A) ∈ I := submodule.mem_top, 
  let hX : X ∈ I := submodule.mem_top,

  suffices hdpow : ∀ (k : ℕ) (a : A) (ha : a ∈ I), 
  hI.dpow k a =  C (1/↑(k.factorial)) * a ^ k,
  rw ← hI.factorial_mul_dpow_eq_pow (m * n) (X + 1) (submodule.mem_top), 
  rw ← polynomial.coeff_C_mul,
  rw [← mul_assoc, mul_comm (C ↑(mchoose m n)), mul_assoc ],
  simp only [C_eq_nat_cast], 
  rw ← hI.dpow_comp m hn (submodule.mem_top), 
  rw [← dpow_eq_of_mem_left hI hI hII n (submodule.mem_top),
    ← dpow_eq_of_mem_left hI hI hII m (submodule.mem_top)],
  rw dpow_comp_aux hI hI hII m hn hX h1,
  rw [← C_eq_nat_cast ],
  simp only [finset.mul_sum],
  -- simp only [← C_eq_nat_cast, ← ring_hom.map_sum, ← ring_hom.map_prod],
  -- simp only [← ring_hom.map_sum, ← ring_hom.map_prod],
  simp only [finset.sum_mul, finset.mul_sum],
  simp only [finset_sum_coeff],

  rw finset.sum_eq_single p,

  { simp only [hdpow _ _ (submodule.mem_top), one_pow, mul_one, one_mul],
    simp_rw [polynomial.coeff_C_mul], 
    simp only [←C_eq_nat_cast, ← ring_hom.map_prod],
    simp_rw [mul_assoc, polynomial.coeff_C_mul, polynomial.coeff_mul_C], 
    simp only [coeff_X_pow_self p],
    apply finset.sum_congr rfl,
    intros x hx, 
    rw mul_comm,
    simp only [mul_assoc],
    apply congr_arg2 (*) rfl,
    apply congr_arg2 (*) rfl,
    apply congr_arg2 (*) rfl,
    rw ← nat.choose_mul_factorial_mul_factorial hp, 
    simp only [one_div, nat.cast_mul, one_mul],
    rw mul_comm, simp only [mul_assoc], rw mul_comm ↑(m * n - p).factorial,
    rw mul_comm, simp only [mul_assoc],
    convert mul_one _,
    rw ←mul_assoc,

    convert mul_one _,
    { rw mul_inv_cancel,
      simp only [ne.def, nat.cast_eq_zero], 
      exact nat.factorial_ne_zero _, },
    { rw mul_inv_cancel,
      simp only [ne.def, nat.cast_eq_zero], 
      exact nat.factorial_ne_zero _, }, },

  { intros k hk hk',
    rw finset.sum_eq_zero,
    intros x hx,
    simp only [hdpow _ _ (submodule.mem_top), one_pow, mul_one, one_mul],
    simp_rw [polynomial.coeff_C_mul], 
    simp only [←C_eq_nat_cast, ← ring_hom.map_prod],
    simp_rw [mul_assoc, polynomial.coeff_C_mul, polynomial.coeff_mul_C], 
    simp only [polynomial.coeff_X_pow , if_neg (ne.symm hk')],
    simp only [mul_zero, zero_mul], },
  
  { intro hp, 
    convert finset.sum_empty, 
    rw finset.eq_empty_iff_forall_not_mem , 
    intros x hx,
    simp only [finset.mem_filter] at hx, 
    apply hp, 
    rw [finset.mem_range, nat.lt_succ_iff],
    rw ← hx.2, 
    exact range_sym_weighted_sum_le x hx.1, },

  { intros k a ha, 
    simp only [rat_algebra.divided_powers_dpow_apply, rat_algebra.dpow, 
      of_invertible_factorial.dpow, dif_pos ha, one_div], 
    simp only [← C_eq_nat_cast],
    rw polynomial.inv_C_eq_C_inv, 
    simp only [ring.inverse_eq_inv'], },
end

include hI
lemma dpow_comp {J : ideal A} (hJ : divided_powers J) 
  (hIJ :  ∀ (n : ℕ) (a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a) 
  (m : ℕ) {n : ℕ} (hn : n ≠ 0) {x : A} (hx : x ∈ I + J) : 
  dpow hI hJ m (dpow hI hJ n x) =
    ↑(mchoose m n) * dpow hI hJ (m * n) x :=
begin
  rw [ideal.add_eq_sup, submodule.mem_sup] at hx, 
  obtain ⟨a, ha, b, hb, rfl⟩ := hx, 
  rw dpow_comp_aux hI hJ hIJ m hn ha hb, 
  rw dpow_add hI hJ hIJ _ (submodule.mem_sup_left ha) (submodule.mem_sup_right hb),
  rw finset.mul_sum, 
  apply finset.sum_congr rfl,
  intros p hp,
  rw dpow_eq_of_mem_left hI hJ hIJ _ ha, 
  rw dpow_eq_of_mem_right hI hJ hIJ _ hb,
  simp only [mul_assoc], apply congr_arg2 (*) _ rfl,
  -- it remains to check coefficients
  rw dpow_comp_coeffs hn (nat.lt_succ_iff.mp (finset.mem_range.mp hp)), 
  simp only [nat.cast_sum, nat.cast_mul, nat.cast_prod], 
end

-- MOVE dpow_null and dpow_one outside of the definition 
noncomputable
def divided_powers {J : ideal A} (hJ : divided_powers J) 
  (hIJ : ∀ (n : ℕ) (a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a) :
divided_powers (I + J) := { 
dpow := dpow hI hJ,
dpow_null := 
begin
  intros n x hx, 
  simp only [dpow], 
  rw function.extend_apply', 
  rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, h⟩, apply hx, 
  rw ← h,
--  change a + b ∈ I + J,
  exact submodule.add_mem_sup ha hb,
end,
dpow_zero := dpow_zero hI hJ hIJ, 
dpow_one := 
begin
  intro x,
  rw [ideal.add_eq_sup, submodule.mem_sup], 
  rintro ⟨a, ha, b, hb, rfl⟩, 
  rw dpow_eq hI hJ hIJ _ ha hb, 
  suffices : finset.range (1 + 1) = {0, 1}, rw this,
  simp only [finset.sum_insert, finset.mem_singleton, nat.zero_ne_one, not_false_iff, 
    tsub_zero, finset.sum_singleton, tsub_self],
  rw [hI.dpow_zero ha, hI.dpow_one ha, hJ.dpow_zero hb, hJ.dpow_one hb],
  ring,
  { rw [finset.range_succ, finset.range_one], ext k, simp, exact or.comm, },
end,
dpow_mem := λ n, dpow_mem hI hJ hIJ,
dpow_add := dpow_add hI hJ hIJ,
dpow_smul := dpow_smul hI hJ hIJ,
dpow_mul := dpow_mul hI hJ hIJ, 
dpow_comp := dpow_comp hI hJ hIJ, }

lemma dpow_unique {J : ideal A} (hJ : _root_.divided_powers J) 
  (hsup : _root_.divided_powers (I + J)) 
  (hI' : ∀ (n : ℕ) (a ∈ I), hI.dpow n a = hsup.dpow n a)
  (hJ' : ∀ (n : ℕ) (b ∈ J), hJ.dpow n b = hsup.dpow n b) :
let hIJ :  ∀ (n : ℕ) (a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a := 
λ n a ha, by simp only [hI' n a (submodule.mem_inf.mp ha).1, hJ' n a (submodule.mem_inf.mp ha).2] in 
  hsup = divided_powers hI hJ hIJ := 
begin
  intro hIJ,
  apply eq_of_eq_on_ideal, 
  intros n x hx, 
  rw [ideal.add_eq_sup, submodule.mem_sup] at hx, 
  obtain ⟨a, ha, b, hb, rfl⟩ := hx, 
  simp only [divided_powers, dpow_eq hI hJ hIJ n ha hb], 
  rw hsup.dpow_add n (submodule.mem_sup_left ha) (submodule.mem_sup_right hb), 
  apply finset.sum_congr rfl, 
  intros k hk,
  apply congr_arg2 (*) (hI' _ a ha).symm (hJ' _ b hb).symm, 
end

end ideal_add
end divided_powers