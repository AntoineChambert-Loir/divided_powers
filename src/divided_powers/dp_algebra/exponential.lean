import divided_powers.dp_algebra.init
import mv_power_series.order
import mv_power_series.topology


variables (R : Type*) [semiring R]

def is_exponential (f : ℕ → R) : Prop := f 0 = 1 ∧ ∀ p q, f (p + q) = (nat.choose (p + q) q) * f p * f q

structure Exp (R : Type*) [semiring R] := 
(to_fun : ℕ → R)
(map_zero : to_fun 0 = 1)
(map_add : ∀ p q, to_fun (p + q) = (nat.choose (p + q) q) * to_fun p * to_fun q)

namespace Exp

instance fun_like : fun_like (Exp R) ℕ (λ _, R) :=
{ coe := Exp.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

@[simp] lemma to_fun_eq_coe {f : Exp R} : 
  f.to_fun = (f : ℕ → R) := rfl

@[ext] theorem ext {f g : Exp R} (h : ∀ n, f n = g n) : f = g := fun_like.ext f g h 

protected def copy (f : Exp R) (f' : ℕ → R) (h : f' = f) : Exp R :=
{ to_fun := f',
  map_zero := h.symm ▸ f.map_zero,
  map_add := h.symm ▸ f.map_add }

def add : (Exp R) → (Exp R) → (Exp R) := λ f g ,
{ to_fun := λ p, (finset.nat.antidiagonal p).sum 
  (λ rs, (f rs.1) * (g rs.2)), 
  map_zero := by
    simp only [finset.nat.antidiagonal_zero, finset.sum_singleton, ← to_fun_eq_coe, map_zero, mul_one],
  map_add := begin
    
  
    sorry 
  end
  
  }
example : add_comm_group (Exp R) := {
  
}
#print is_exponential
end exponential