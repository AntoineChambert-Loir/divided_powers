import divided_powers.dp_algebra
import algebra_comp

universes u v w

open divided_powers ideal divided_power_algebra

def is_universal {A : Type u} [comm_ring A] {I : ideal A} (hI : divided_powers I) {B : Type v}
  [comm_ring B] [algebra A B] (J : ideal B) {D : Type v} [comm_ring D] (J' : ideal D)
  (hJ' : divided_powers J') (ψ : B →+* D) (hψ : J.map ψ ≤ J') :=
∀ (C : Type w) [comm_ring C], by exactI ∀ (K : ideal C) (hK : divided_powers K)
  (g : pd_morphism hI hK) (h : B →+* C) (hh : J.map h ≤ K) 
  (hcomp : h ∘ (algebra_map A B) = g.to_ring_hom),
  ∃! (φ : pd_morphism hJ' hK), φ.to_ring_hom ∘ ψ = h 

namespace divided_power_envelope

variables {A : Type u} [comm_ring A] {I : ideal A} (hI : divided_powers I) {B : Type v} 
  [comm_ring B] [algebra A B] (J : ideal B) 

section included

variables (hIJ : I.map (algebra_map A B) ≤ J)

inductive rel1 : _root_.rel (divided_power_algebra B J) (divided_power_algebra B J)
| rel {x : J} : rel1 (ι B x) (algebra_map _ _ (x : B))

noncomputable def J1 : ideal (divided_power_algebra B J) := of_rel (rel1 J)

include hIJ

inductive rel2 : _root_.rel (divided_power_algebra B J) (divided_power_algebra B J)
| rel {x : I} {n : ℕ} : rel2
  (dp B n (⟨(algebra_map A B x), hIJ (ideal.mem_map_of_mem _ x.2)⟩ : J))
  (algebra_map _ _ (algebra_map A B (dpow hI n x )))

noncomputable def J2 : ideal (divided_power_algebra B J) := of_rel (rel2 hI J hIJ)

noncomputable def J12 : ideal (divided_power_algebra B J) := J1 J + J2 hI J hIJ

theorem J12_is_sub_pd_ideal : is_sub_pd_ideal (divided_power_algebra.divided_powers' B J)
  ((J12 hI J hIJ) ⊓ (aug_ideal B J)) :=
sorry

def dp_envelope_of_included : Type v := (divided_power_algebra B J) ⧸ (J12 hI J hIJ)

noncomputable instance : comm_ring (dp_envelope_of_included hI J hIJ) := ideal.quotient.comm_ring _

noncomputable instance : algebra B (dp_envelope_of_included hI J hIJ) := ideal.quotient.algebra _

noncomputable instance algebra_of_included : algebra A (dp_envelope_of_included hI J hIJ) := 
algebra.comp A B (dp_envelope_of_included hI J hIJ)

instance is_scalar_tower_of_included : is_scalar_tower A B (dp_envelope_of_included hI J hIJ) :=
is_scalar_tower.comp A B (dp_envelope_of_included hI J hIJ)

noncomputable def dp_ideal_of_included : ideal (dp_envelope_of_included hI J hIJ) :=
(map (ideal.quotient.mk (J12 hI J hIJ)) (aug_ideal B J))

lemma sub_ideal_dp_ideal_of_included : 
  J.map (algebra_map B (dp_envelope_of_included hI J hIJ)) ≤ (dp_ideal_of_included hI J hIJ) :=
sorry

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
(ideal.map (ideal.quotient.mk (J12 hI (J' I J) (sub_ideal_J' I J))) (aug_ideal B (J' I J)))

lemma sub_ideal_dp_ideal : J.map (algebra_map B (dp_envelope hI J)) ≤ (dp_ideal hI J) :=
sorry

theorem dp_envelope_is_universal : is_universal hI J (dp_ideal hI J) 
  (quot.divided_powers (divided_power_algebra.divided_powers' B (J' I J))
    (J12_is_sub_pd_ideal hI (J' I J) (sub_ideal_J' I J))) 
  (algebra_map B (dp_envelope hI J)) (sub_ideal_dp_ideal hI J) :=
sorry

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