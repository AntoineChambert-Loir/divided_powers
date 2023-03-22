-- import algebra.module.graded_module
import ring_theory.graded_algebra.homogeneous_ideal
import ring_theory.ideal.quotient

variables {ι : Type*} [decidable_eq ι] [add_monoid ι]
variables {A : Type*} [comm_ring A] 
variables {σ : Type*} [set_like σ A] [add_submonoid_class σ A] 

variable (𝒜 : ι → σ)
variable (rel : A → A → Prop) 

-- open_locale big_operators


/- 
def weights [graded_ring 𝒜] [Π (i : ι) (x : ↥(𝒜 i)), decidable (x ≠ 0)] (a : A) := 
dfinsupp.support (direct_sum.decompose 𝒜 a)

def is_homogenous [graded_ring 𝒜] [Π (i : ι) (x : ↥(𝒜 i)), decidable (x ≠ 0)] (a : A) :=
subsingleton (weights 𝒜 a)
-/

example (R S : Type*) [comm_ring R] [comm_ring S] (f : R →+* S)
 (I : submonoid R) : submonoid S :=  submonoid.map f I


def graded_quot (I : ideal A) [graded_ring 𝒜] (hI: ideal.is_homogeneous 𝒜 I) : ι → add_submonoid (A ⧸ I) := λ i, add_submonoid.map (ideal.quotient.mk I)
  ⟨𝒜 i, begin apply add_mem , end, begin apply zero_mem, end,⟩



def graded_quot (I : ideal A) [graded_ring 𝒜] (hI: ideal.is_homogeneous 𝒜 I) := false



