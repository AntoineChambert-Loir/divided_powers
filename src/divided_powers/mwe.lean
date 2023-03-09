import algebra.module.basic

variables (A : Type*) [comm_ring A] 

def foo /- (A : Type*) [comm_ring A] -/ : Prop := 
∃ (T : Type*) [comm_ring T], by exactI ∃ [module A T], true