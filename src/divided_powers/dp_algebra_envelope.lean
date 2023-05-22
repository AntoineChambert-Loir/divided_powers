import divided_powers.dp_algebra

open divided_powers ideal divided_power_algebra

def is_universal {A : Type*} [comm_ring A] {I : ideal A} (hI : divided_powers I) {B : Type*}
  [comm_ring B] [algebra A B] (J : ideal B) {D : Type*} [comm_ring D] (J' : ideal D)
  (hJ' : divided_powers J') (ψ : B →+* D) (hψ : ψ '' J ⊆ J') :=
∀ {C : Type*} [comm_ring C], by exactI ∀ (K : ideal C) (hK : divided_powers K)
  (g : pd_morphism hI hK) (h : B →+* C) (hh : h '' J ⊆ K) 
  (hcomp : h ∘ (algebra_map A B) = g.to_ring_hom),
  ∃! (φ : pd_morphism hJ' hK), φ.to_ring_hom ∘ ψ = h 

-- Theorem 3.19 Berthelot-Ogus
theorem exists_dp_envelope (A B : Type*) [comm_ring A] {I : ideal A} (hI : divided_powers I)
  [comm_ring B] [algebra A B] (J : ideal B) :
  ∃ (D : Type*) [hD : comm_ring D], by exactI ∃ {J' : ideal D} (hJ' : divided_powers J')
  (ψ : B →+* D) (hψ : ψ '' J ⊆ J'), is_universal hI J J' hJ' ψ hψ :=
sorry

namespace divided_power_envelope

variables {A B : Type*} [comm_ring A] {I : ideal A} (hI : divided_powers I) [comm_ring B] 
  [algebra A B] (J : ideal B) 

section included

variables (hIJ : (algebra_map A B)'' I ⊆ J)

inductive rel1 : _root_.rel (divided_power_algebra B J) (divided_power_algebra B J)
| rel {x : J} : rel1 (ι B x) (algebra_map _ _ (x : B))

noncomputable def J1 : ideal (divided_power_algebra B J) := of_rel (rel1 J)

include hIJ

inductive rel2 : _root_.rel (divided_power_algebra B J) (divided_power_algebra B J)
| rel {x : I} {n : ℕ} : rel2
  (dp B n (⟨(algebra_map A B x), hIJ ( set.mem_image_of_mem _ x.2)⟩ : J))
  (algebra_map _ _ (algebra_map A B (dpow hI n x ))) --(algebra_map _ _ (x : B))

noncomputable def J2 : ideal (divided_power_algebra B J) := of_rel (rel2 hI J hIJ)

noncomputable def J12 : ideal (divided_power_algebra B J) := J1 J + J2 hI J hIJ

theorem J12_is_sub_pd_ideal : is_sub_pd_ideal (divided_power_algebra.divided_powers' B J)
  ((J12 hI J hIJ) ⊓ (aug_ideal B J)) :=
sorry

def dp_envelope := (divided_power_algebra B J) ⧸ (J12 hI J hIJ)

noncomputable instance : comm_ring (dp_envelope hI J hIJ) := 
ideal.quotient.comm_ring _

noncomputable instance : algebra B (dp_envelope hI J hIJ) := 
ideal.quotient.algebra _

instance algebra' : algebra A (dp_envelope hI J hIJ) := 
sorry

instance : is_scalar_tower A B (dp_envelope hI J hIJ) := 
sorry

noncomputable def dp_ideal : ideal (dp_envelope hI J hIJ) :=
(map (ideal.quotient.mk (J12 hI J hIJ)) (aug_ideal B J))

lemma sub_ideal_dp_ideal : 
  (algebra_map B (dp_envelope hI J hIJ)) '' J ⊆ (dp_ideal hI J hIJ) :=
sorry

theorem dp_envelope_is_universal : is_universal hI J (dp_ideal hI J hIJ)
  (quot.divided_powers (divided_power_algebra.divided_powers' B J) (J12_is_sub_pd_ideal hI J hIJ))
  (algebra_map B (dp_envelope hI J hIJ)) (sub_ideal_dp_ideal hI J hIJ) :=
sorry

end included

namespace general

variables (I)

def J' : ideal B := J + I.map (algebra_map A B)

lemma sub_ideal_J' :  (algebra_map A B) '' I ⊆  J' I J := sorry

variables {I}

def dp_envelope := (divided_power_algebra B (J' I J)) ⧸ (J12 hI (J' I J) (sub_ideal_J' I J))

noncomputable instance : comm_ring (dp_envelope hI J) := ideal.quotient.comm_ring _

noncomputable instance : algebra B (dp_envelope hI J) := ideal.quotient.algebra _

instance algebra' : algebra A (dp_envelope hI J) := sorry

instance : is_scalar_tower A B (dp_envelope hI J) := sorry

noncomputable def dp_ideal : ideal (dp_envelope hI J) :=
(ideal.map (ideal.quotient.mk (J12 hI (J' I J) (sub_ideal_J' I J))) (aug_ideal B (J' I J)))

lemma sub_ideal_dp_ideal : (algebra_map B (dp_envelope hI J)) '' J ⊆ (dp_ideal hI J) :=
sorry

theorem dp_envelope_is_universal : is_universal hI J (dp_ideal hI J) 
  (quot.divided_powers (divided_power_algebra.divided_powers' B (J' I J))
    (J12_is_sub_pd_ideal hI (J' I J) (sub_ideal_J' I J))) 
  (algebra_map B (dp_envelope hI J)) (sub_ideal_dp_ideal hI J) :=
sorry

end general

end divided_power_envelope