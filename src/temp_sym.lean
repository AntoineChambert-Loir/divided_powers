
/- Functions that come from the multinomial PR by Pim Otte and will eventually belong to data.sym.basic or data.sym.card -/

/- There are some sorry but this is OK -/

import tactic

import import data.finset.sym

section basic_sym

namespace sym

open finset function multiset 

variables (α : Type*) [decidable_eq α] (n : ℕ)

lemma mem_fill_iff' {a b : α} {i : fin (n + 1)} {s : sym α (n - i)} :
  a ∈ sym.fill b i s ↔ ((i : ℕ) ≠ 0 ∧ a = b) ∨ a ∈ s :=
by rw [sym.fill, sym.mem_cast, sym.mem_append_iff, or_comm, sym.mem_repeat]

end sym

open finset

namespace finset

variables {α : Type*} [decidable_eq α] {s t : finset α} {a b : α}

variables {n : ℕ} {m : sym α n}

@[simp] lemma mem_sym_iff' : m ∈ s.sym n ↔ ∀ a ∈ m, a ∈ s :=
begin
  induction n with n ih,
  { refine mem_singleton.trans ⟨_, λ _, sym.eq_nil_of_card_zero _⟩,
    rintro rfl,
    exact λ a ha, ha.elim },
  refine mem_sup.trans  ⟨_, λ h, _⟩,
  { rintro ⟨a, ha, he⟩ b hb,
    rw mem_image at he,
    obtain ⟨m, he, rfl⟩ := he,
    rw sym.mem_cons at hb,
    obtain rfl | hb := hb,
    { exact ha },
    { exact ih.1 he _ hb } },
  { obtain ⟨a, m, rfl⟩ := m.exists_eq_cons_of_succ,
    exact ⟨a, h _ $ sym.mem_cons_self _ _,
      mem_image_of_mem _ $ ih.2 $ λ b hb, h _ $ sym.mem_cons_of_mem hb⟩ }
end

end finset


end basic_sym

