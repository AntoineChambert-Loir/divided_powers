import ring_theory.ideal.operations

section induction

namespace submodule
universes u v
variables {R : Type u} {M : Type v} {F : Type*} {G : Type*}
variables [comm_semiring R] [add_comm_monoid M] [module R M]
variables {I J : ideal R} {N P Q : submodule R M}

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
  rw [← map_nat_cast (algebra_map ℚ A)],
  apply is_unit.map,
  exact is_unit_iff_ne_zero.mpr (nat.cast_ne_zero.mpr (nat.factorial_ne_zero n)),
end

end factorial

section inverse

namespace ring 
lemma inverse_pow_mul_eq_iff_eq_mul {M₀ : Type*} [comm_monoid_with_zero M₀] {a : M₀}
  (b c : M₀) (ha : is_unit a) {k : ℕ} : (ring.inverse a)^k * b = c ↔ b = a^k * c :=
by rw [ring.inverse_pow, ring.inverse_mul_eq_iff_eq_mul _ _ _ (is_unit.pow _ ha)]
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