
/- Functions that come from the multinomial PR by Pim Otte and will eventually belong to data.sym.basic or data.sym.card -/

/- There are some sorry but this is OK -/

import tactic

import import data.finset.sym

section basic_sym

namespace sym

open finset function multiset 

variables (α : Type*) [decidable_eq α] (n : ℕ)
lemma coe_fill {a : α} {i : fin (n + 1)} {m : sym α (n - i)} :
  (sym.fill a i m : multiset α) = m + repeat a i := rfl


lemma mem_fill_iff' {a b : α} {i : fin (n + 1)} {s : sym α (n - i)} :
  a ∈ sym.fill b i s ↔ ((i : ℕ) ≠ 0 ∧ a = b) ∨ a ∈ s :=
by rw [sym.fill, sym.mem_cast, sym.mem_append_iff, or_comm, sym.mem_repeat]


lemma filter_ne_fill [decidable_eq α] (a : α) (m : Σ i : fin (n + 1), sym α (n - i)) (h : a ∉ m.2) :
  (m.2.fill a m.1).filter_ne a = m := sorry 


lemma fill_filter_ne [decidable_eq α] (a : α) (m : sym α n) :
  (m.filter_ne a).2.fill a (m.filter_ne a).1 = m :=
subtype.ext begin
  dsimp only [coe_fill, filter_ne, subtype.coe_mk, fin.coe_mk],
  ext b, rw [count_add, count_filter, sym.coe_repeat, count_repeat],
  obtain rfl | h := eq_or_ne a b,
  { rw [if_pos rfl, if_neg (not_not.2 rfl), zero_add], refl },
  { rw [if_pos h, if_neg h.symm, add_zero], refl },
end

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

lemma sym_fill_mem (a : α) {i : fin (n + 1)} {m : sym α (n - i)} (h : m ∈ s.sym (n - i)) :
  m.fill a i ∈ (insert a s).sym n := sorry 
  /- 
mem_sym_iff'.2 $ λ b hb, mem_insert.2 $ (sym.mem_fill_iff'.1 hb).imp and.right $ mem_sym_iff.1 h b
 -/

lemma sym_filter_ne_mem (a : α) (h : m ∈ s.sym n) :
  (m.filter_ne a).2 ∈ (s.erase a).sym (n - (m.filter_ne a).1) :=
mem_sym_iff.2 $ λ b H, mem_erase.2 $ (multiset.mem_filter.1 H).symm.imp ne.symm $ mem_sym_iff.1 h b

end finset


end basic_sym

