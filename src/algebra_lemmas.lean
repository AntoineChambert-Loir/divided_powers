import ring_theory.ideal.operations

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

section factorial
variables {A : Type*} [comm_ring A] {I : ideal A}

lemma factorial_is_unit {n : ℕ} (hn_fac : is_unit ((n-1).factorial : A))
  {m : ℕ} (hmn : m < n) : is_unit (m.factorial : A) :=
begin
  apply is_unit_of_dvd_unit _ hn_fac,
  obtain ⟨c, hc⟩ := nat.factorial_dvd_factorial (nat.le_pred_of_lt hmn),
  use (c : A),
  rw [← nat.cast_mul, hc],
end

lemma factorial.is_unit [algebra ℚ A] (n : ℕ) : is_unit (n.factorial : A) :=
begin
  have hn : (n.factorial : A) = algebra_map ℚ A n.factorial,
  { rw [map_nat_cast] },
  rw hn,
  apply is_unit.map,
  exact is_unit_iff_ne_zero.mpr (nat.cast_ne_zero.mpr (nat.factorial_ne_zero n)),
end

end factorial

section inverse

namespace ring 
lemma inverse_mul_eq_iff_eq_mul {M₀ : Type*} [comm_monoid_with_zero M₀] {a : M₀} (b c : M₀)
  (ha : is_unit a) : ring.inverse a * b = c ↔ b = a * c := 
⟨λ h, by rw [← h, ring.mul_inverse_cancel_left _ _ ha],
  λ h, by rw [h, ring.inverse_mul_cancel_left _ _ ha]⟩

lemma eq_mul_inverse_iff_mul_eq {M₀ : Type*} [comm_monoid_with_zero M₀] {a : M₀} (b c : M₀)
  (hc : is_unit c) : a = b * ring.inverse c ↔ a * c = b := 
⟨λ h, by rw [h, ring.inverse_mul_cancel_right _ _ hc],
  λ h, by rw [← h, ring.mul_inverse_cancel_right _ _ hc]⟩

lemma inverse_pow_mul_eq_iff_eq_mul {M₀ : Type*} [comm_monoid_with_zero M₀] {a : M₀}
  (b c : M₀) (ha : is_unit a) {k : ℕ} : (ring.inverse a)^k * b = c ↔ b = a^k * c :=
by rw [ring.inverse_pow, ring.inverse_mul_eq_iff_eq_mul _ _ (is_unit.pow _ ha)]
end ring

end inverse

lemma ideal.mem_pow_eq_zero {A : Type*} [comm_ring A] {I : ideal A} (n m : ℕ) (hnI : I^n = 0)
  (hmn : n ≤ m) {x : A} (hx : x ∈ I) : x ^ m = 0 :=
begin
  have hxn : x^n = 0,
  { rw [ideal.zero_eq_bot] at hnI,
    rw [← ideal.mem_bot, ← hnI],
    exact ideal.pow_mem_pow hx n },
  obtain ⟨c, hc⟩ := nat.exists_eq_add_of_le hmn,
  rw [hc, pow_add, hxn, zero_mul]
end
