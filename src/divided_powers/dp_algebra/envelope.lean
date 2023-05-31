import divided_powers.dp_algebra.dpow
import algebra_comp

universes u v w

open divided_powers ideal divided_power_algebra

def is_compatible_with {A : Type u} [comm_ring A] {I : ideal A} (hI : divided_powers I) {B : Type v}
  [comm_ring B]  {J : ideal B} (hJ : divided_powers J) (f : A →+* B) : Prop :=
∃ (hI' : divided_powers (I.map f)), 
    (∀ (n : ℕ) (a : A), hI'.dpow n (f a) = f (hI.dpow n a)) ∧ 
    (∀ (n : ℕ) (b : B) (hb : b ∈ J ⊓ (I.map f)), hJ.dpow n b = hI'.dpow n b)

-- I added hext (compatibility condition) and replaced `g` `h` and `h_comp` by 
-- `[algebra A C] [algebra B C] [is_scalar_tower A B C]`
def is_universal {A : Type u} [comm_ring A] {I : ideal A} (hI : divided_powers I) {B : Type v}
  [comm_ring B] [algebra A B] (J : ideal B) {D : Type v} [comm_ring D] (J' : ideal D)
  (hJ' : divided_powers J') (ψ : B →+* D) (hψ : J.map ψ ≤ J') :=
∀ (C : Type w) [comm_ring C], by exactI ∀ [algebra A C] [algebra B C], 
by exactI ∀ [is_scalar_tower A B C], by exactI ∀ (K : ideal C) (hK : divided_powers K)
  /- (g : pd_morphism hI hK) -/ /- (h : B →+* C) -/ (hh : J.map (algebra_map B C) ≤ K) 
  /- (hcomp : h ∘ (algebra_map A B) = algebra_map A C)  -/
  (hext : is_compatible_with hI hK (algebra_map A C)),
  ∃! (φ : pd_morphism hJ' hK), φ.to_ring_hom ∘ ψ = (algebra_map B C)

namespace divided_power_envelope


variables {A : Type u} [comm_ring A] {I : ideal A} (hI : divided_powers I) {B : Type v} 
  [comm_ring B] [algebra A B] (J : ideal B) 

section included

open divided_powers divided_power_algebra 

variables (hIJ : I.map (algebra_map A B) ≤ J)

inductive rel1 : _root_.rel (divided_power_algebra B J) (divided_power_algebra B J)
| rel {x : J} : rel1 (divided_power_algebra.ι B x) (algebra_map _ _ (x : B))

noncomputable def J1 : ideal (divided_power_algebra B J) := of_rel (rel1 J)

include hIJ

inductive rel2 : _root_.rel (divided_power_algebra B J) (divided_power_algebra B J)
| rel {x : I} {n : ℕ} : rel2
  (dp B n (⟨(algebra_map A B x), hIJ (ideal.mem_map_of_mem _ x.2)⟩ : J))
  (algebra_map _ _ (algebra_map A B (dpow hI n x )))

noncomputable def J2 : ideal (divided_power_algebra B J) := of_rel (rel2 hI J hIJ)

noncomputable def J12 : ideal (divided_power_algebra B J) := J1 J + J2 hI J hIJ

theorem J12_is_sub_pd_ideal : is_sub_pd_ideal (divided_power_algebra.divided_powers' B J)
  ((J12 hI J hIJ) ⊓ (divided_power_algebra.aug_ideal B J)) :=
sorry

def dp_envelope_of_included : Type v := (divided_power_algebra B J) ⧸ (J12 hI J hIJ)

noncomputable instance : comm_ring (dp_envelope_of_included hI J hIJ) := ideal.quotient.comm_ring _

noncomputable instance : algebra B (dp_envelope_of_included hI J hIJ) := ideal.quotient.algebra _

noncomputable instance algebra_of_included : algebra A (dp_envelope_of_included hI J hIJ) := 
algebra.comp A B (dp_envelope_of_included hI J hIJ)

instance is_scalar_tower_of_included : is_scalar_tower A B (dp_envelope_of_included hI J hIJ) :=
is_scalar_tower.comp A B (dp_envelope_of_included hI J hIJ)

noncomputable def dp_ideal_of_included : ideal (dp_envelope_of_included hI J hIJ) :=
(map (ideal.quotient.mk (J12 hI J hIJ)) (divided_power_algebra.aug_ideal B J))

lemma sub_ideal_dp_ideal_of_included : 
  J.map (algebra_map B (dp_envelope_of_included hI J hIJ)) ≤ (dp_ideal_of_included hI J hIJ) :=
begin
  intros x hx,
  rw dp_ideal_of_included,
  rw ideal.mem_map_iff_of_surjective,
  sorry,
  exact quotient.mk_surjective,
end

theorem dp_envelope_of_included_is_universal : is_universal hI J (dp_ideal_of_included hI J hIJ)
  (quot.divided_powers (divided_power_algebra.divided_powers' B J) (J12_is_sub_pd_ideal hI J hIJ))
  (algebra_map B (dp_envelope_of_included hI J hIJ)) (sub_ideal_dp_ideal_of_included hI J hIJ) :=
sorry

end included

section general

variables (I)

def J' : ideal B := J + I.map (algebra_map A B)

lemma sub_ideal_J' :  I.map (algebra_map A B) ≤ J' I J := 
le_sup_of_le_right (le_refl _)

variables {I}

def dp_envelope : Type v := 
(divided_power_algebra B (J' I J)) ⧸ (J12 hI (J' I J) (sub_ideal_J' I J))

noncomputable instance : comm_ring (dp_envelope hI J) := ideal.quotient.comm_ring _

noncomputable instance : algebra B (dp_envelope hI J) := ideal.quotient.algebra _

noncomputable instance algebra' : algebra A (dp_envelope hI J) := 
algebra.comp A B (dp_envelope hI J)

instance : is_scalar_tower A B (dp_envelope hI J) := 
is_scalar_tower.comp A B (dp_envelope hI J)

noncomputable def dp_ideal : ideal (dp_envelope hI J) :=
(ideal.map (ideal.quotient.mk (J12 hI (J' I J) (sub_ideal_J' I J))) 
  (divided_power_algebra.aug_ideal B (J' I J)))

lemma sub_ideal_dp_ideal : J.map (algebra_map B (dp_envelope hI J)) ≤ (dp_ideal hI J) :=
sorry

section 

/- def divided_powers_of_map {C : Type*} [comm_ring C] (f : A →+* C) [∀ c, decidable (c ∈ map f I)] :
  divided_powers (I.map f) :=
{ dpow      := λ n c,
  begin
    by_cases hc : c ∈ I.map f,
    { rw ideal.map at hc,
      --squeeze_simp at hc,
      --apply submodule.span_induction _ _ _ _ hc,
      sorry },
    { exact 0}
  end,
  dpow_null := sorry,
  dpow_zero := sorry,
  dpow_one  := sorry,
  dpow_mem  := sorry,
  dpow_add  := sorry,
  dpow_smul := sorry,
  dpow_mul  := sorry,
  dpow_comp := sorry }


end -/


theorem dp_envelope_is_universal : is_universal hI J (dp_ideal hI J) 
  (quot.divided_powers (divided_power_algebra.divided_powers' B (J' I J))
    (J12_is_sub_pd_ideal hI (J' I J) (sub_ideal_J' I J))) 
  (algebra_map B (dp_envelope hI J)) (sub_ideal_dp_ideal hI J) :=
begin
  rw is_universal,
  intros C _ _ _ _ K hK hJK hcomp,
  obtain ⟨hI', hI'_ext, hI'_int⟩ := hcomp,
  resetI,
  set K1 : ideal C := K + I.map (algebra_map A C) with hK1,
  set h1 : divided_powers K1 := ideal_add.divided_powers hK hI' hI'_int with h1_def,
  set g' : hI.pd_morphism h1 :=
  { to_ring_hom := algebra_map A C,
    ideal_comp  := le_sup_of_le_right (le_refl _),
    dpow_comp   := λ n a ha,
    begin
      -- TODO: add rw lemma for ideal_add.divided_powers.dpow = ideal_add.dpow
      rw ← hI'_ext, 
      exact ideal_add.dpow_eq_of_mem_right _ _ hI'_int _ (mem_map_of_mem (algebra_map A C) ha),
    end },
  have hg' : (J' I J).map (algebra_map B C) ≤ K1,
  { rw J',
    rw ideal.add_eq_sup,
    rw ideal.map_sup,
    rw sup_le_iff,
    split,
    { exact le_trans hJK (le_sup_of_le_left (le_refl _)) },
    { have : (algebra_map B C).comp (algebra_map A B) = (algebra_map A C) := sorry,
      rw ideal.map_map,
      rw this,
      exact le_trans hJK (le_sup_of_le_right (le_refl _)),
      },
  },

  have hI1 : is_compatible_with hI h1 (algebra_map A C),
  { rw is_compatible_with,
    use hI', use hI'_ext,
    intros n c hc,
    simp only [hK1, ideal.add_eq_sup, inf_of_le_right, le_sup_right] at hc,
    exact ideal_add.dpow_eq_of_mem_right _ _ hI'_int _ hc, },
  obtain ⟨φ, hφ, hφ_unique⟩ := 
  dp_envelope_of_included_is_universal hI (J' I J) (sub_ideal_J' I J) C _ h1 hg' hI1,
  -- TODO: generalize (map to sub-pd-structure)
  set ψ : (quot.divided_powers (divided_power_algebra.divided_powers' B (J' I J))
    (J12_is_sub_pd_ideal hI (J' I J) (sub_ideal_J' I J))).pd_morphism hK :=
   { to_ring_hom := φ.to_ring_hom,
     ideal_comp  := sorry,
     dpow_comp   := λ n a ha,
    begin
      obtain ⟨r, s⟩ := hI1,
      --rw ← hI'_ext, 
      --rw φ.dpow_comp,
      sorry
      -- TODO: add rw lemma for ideal_add.divided_powers.dpow = ideal_add.dpow
      /- rw ← hI'_ext, 
      exact ideal_add.dpow_eq_of_mem_right _ _ hI'_int _ (mem_map_of_mem (algebra_map A C) ha), -/
    end },
    use ψ,
    --simp only,
    use hφ,
    
    intros α hα,
    ext,
    { --have := hφ_unique (ideal_add.divided_powers α hI'),
      sorry },
    { sorry }

end

#exit

end general 

-- Theorem 3.19 Berthelot-Ogus
theorem exists_dp_envelope (A : Type u) [comm_ring A] {I : ideal A} (hI : divided_powers I)
  (B : Type v) [comm_ring B] [algebra A B] (J : ideal B) :
  ∃ (D : Type v) [hD : comm_ring D], by exactI ∃ {J' : ideal D} (hJ' : divided_powers J')
  (ψ : B →+* D) (hψ : J.map ψ ≤ J'), is_universal hI J J' hJ' ψ hψ :=
⟨(dp_envelope hI J), infer_instance, dp_ideal hI J,
  (quot.divided_powers (divided_power_algebra.divided_powers' B (J' I J))
    (J12_is_sub_pd_ideal hI (J' I J) (sub_ideal_J' I J))),
algebra_map B _, sub_ideal_dp_ideal hI J, dp_envelope_is_universal hI J⟩

end divided_power_envelope