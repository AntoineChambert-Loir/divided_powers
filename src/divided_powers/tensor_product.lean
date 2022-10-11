
import ring_theory.tensor_product
import divided_powers.basic

namespace divided_powers

open_locale tensor_product

/- 3.7 Lemma. Suppose R is a ring, В and С are R-algebras, and
I ⊆ В and J ⊆ С are augmentation ideals (i.e. there is a section of В → B/I, etc.) 
with P.D. structures γ and δ, respectively. 
Then the ideal К = Ker (В ⊗ С → B/I ⊗ C/J) has a unique P.D. structure ε 
such that (B,I,γ) → (В ⊗ С,К,ε) and
(C,J,δ) → (B ⊗ C,K,ε) are P.D. morphisms. -/

/- Lemma 3.7 of [BO] -> Change to 1.7.1 -/

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
  apply eq_of_eq_on_ideal,
  intros n x hx,
  sorry
end

end divided_powers