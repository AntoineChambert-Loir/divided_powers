import ring_theory.tensor_product

variables {R : Type*} [comm_ring R]
variables {A B : Type*} [comm_ring A] [comm_ring B] [algebra R A] [algebra R B]

example : semiring (tensor_product R A B) :=
begin
apply_instance, 
end

example : algebra R (tensor_product R A B) :=
begin
apply_instance,
end

variables {ι : Type*} [add_monoid ι] 

example : add_monoid (unit) := infer_instance

example : add_monoid (with_top unit) := infer_instance

example : with_top unit := unit.star

example : with_top unit := 0

example : (0 : with_top unit) = unit.star := rfl

example : with_top unit := ⊤

example : (unit.star  : with_top unit) ≠ (⊤ : with_top unit) := with_top.coe_ne_top

#check unit.star

#eval unit.star

