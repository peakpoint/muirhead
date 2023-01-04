/-
Copyright (c) 2023 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/

import algebra.big_operators.fin
import algebra.big_operators.order
import algebra.order.ring.abs
import data.multiset.sort

open_locale big_operators

section

open finset

section defs

variables {α : Type*}
  [linear_ordered_add_comm_monoid α]
  [decidable_rel ((≤) : α → α → Prop)]
  {ι : Type*} [fintype ι]

def weakly_majorize (l₁ l₂ : ι → α) :=
  ∀ n,
    (((univ.val.map l₁).sort (≥)).take n).sum ≤
    (((univ.val.map l₂).sort (≥)).take n).sum

/-- Majorization. Note that `majorize p q` means `q` majorizes `p` -/
def majorize (l₁ l₂ : ι → α) := weakly_majorize l₁ l₂ ∧ ∑ i, l₁ i = ∑ i, l₂ i

lemma majorize_def (l₁ l₂ : ι → α) :
  majorize l₁ l₂ ↔
  (∀ n,
    (((univ.val.map l₁).sort (≥)).take n).sum ≤
    (((univ.val.map l₂).sort (≥)).take n).sum) ∧ ∑ i, l₁ i = ∑ i, l₂ i := iff.rfl

infix ` ≺w `:45 := weakly_majorize
infix ` ≺ `:45 := majorize

lemma weakly_majorize_def' (l₁ l₂ : ι → α) :
  l₁ ≺w l₂ ↔
  ∀ n ≤ fintype.card ι,
    (((univ.val.map l₁).sort (≥)).take n).sum ≤
    (((univ.val.map l₂).sort (≥)).take n).sum :=
begin
  split,
  { intros h n hn,
    apply h },
  { intros h n,
    cases le_total n (fintype.card ι) with hn' hn',
    { exact h n hn' },
    { have := h _ le_rfl,
      rwa [list.take_all_of_le, list.take_all_of_le] at this ⊢,
      all_goals { rwa [multiset.length_sort, multiset.card_map]; refl } } }
end

instance : decidable_rel (≺w) := λ (l₁ l₂ : ι → α),
by { rw weakly_majorize_def', exact nat.decidable_ball_le _ _ }

instance : decidable_rel (≺) := λ (l₁ l₂ : ι → α), and.decidable

instance majorize.preorder : preorder (ι → α) :=
{ le := (≺),
  le_refl := λ l, ⟨λ _, rfl.le, rfl⟩,
  le_trans := λ l₁ l₂ l₃ h₁ h₂,
    ⟨λ h, (h₁.1 h).trans (h₂.1 h), h₁.2.trans h₂.2⟩ }

end defs

variables {α : Type*}

lemma exists_lt_eq_gt
  [linear_ordered_cancel_add_comm_monoid α]
  [decidable_rel ((<) : α → α → Prop)]
  {n} {a b : fin n → α} (hab : a ≠ b) (h₁ : ∑ i, a i = ∑ i, b i)
  (h₂ : ∀ i, ((list.of_fn a).take i).sum ≤ ((list.of_fn b).take i).sum) :
  ∃ (k l : fin n), k < l ∧ a k < b k ∧ b l < a l ∧ (∀ i, k < i → i < l → a i = b i):=
begin
  have h_k : ∃ k, a k ≠ b k,
  { by_contra' h,
    apply hab,
    ext,
    apply h },
  let k := option.get (fin.is_some_find_iff.2 h_k),
  have hk : k ∈ fin.find (λ i, a i ≠ b i) := option.get_mem _,
  have hk₂ : ∀ i < k, a i = b i := λ i hi, not_not.1 (fin.find_min hk hi),
  have hkab : list.take k (list.of_fn a) = list.take k (list.of_fn b),
  { apply list.ext_le,
    { iterate 2 { rw [list.length_take, list.length_of_fn] } },
    intros i hi _,
    iterate 2 { rw [list.nth_le_take', list.nth_le_of_fn'] },
    rw [list.length_take, list.length_of_fn, min_eq_left fin.is_le'] at hi,
    apply hk₂,
    exact hi  },
  have ha_len : ↑k < (list.of_fn a).length := (list.length_of_fn a).symm ▸ k.is_lt,
  have hb_len : ↑k < (list.of_fn b).length := (list.length_of_fn b).symm ▸ k.is_lt,
  specialize h₂ (k + 1),
  rw [list.sum_take_succ _ _ ha_len, list.sum_take_succ _ _ hb_len,
    list.nth_le_of_fn, list.nth_le_of_fn, hkab, add_le_add_iff_left] at h₂,
  have hk₁ := lt_of_le_of_ne h₂ (fin.find_spec _ hk),
  have h_l : ∃ l, b l < a l,
  { by_contra' h,
    refine ne_of_lt _ h₁,
    exact sum_lt_sum (λ _ _, h _) ⟨k, mem_univ _, hk₁⟩ },
  let l := option.get (fin.is_some_find_iff.2 h_l),
  have hl : l ∈ fin.find (λ i, b i < a i) := option.get_mem _,
  have hl₁ : b l < a l := fin.find_spec _ hl,
  have hkl : k < l,
  { by_contra' h,
    cases eq_or_lt_of_le h with h' h',
    { rw h' at hl₁,
      exact hl₁.not_le h₂ },
    { rw hk₂ _ h' at hl₁,
      exact lt_irrefl _ hl₁ } },
  let s := univ.filter (λ k' : fin l,
    a (fin.cast_le fin.is_le' k') < b (fin.cast_le fin.is_le' k')),
  have hs : s.nonempty,
  { use [k, fin.lt_iff_coe_lt_coe.1 hkl],
    rw mem_filter,
    refine ⟨mem_univ _, _⟩,
    rwa [fin.cast_le_mk, fin.eta] },
  let k' := fin.cast_le fin.is_le' (max' s hs),
  use [k', l, fin.is_lt _, (mem_filter.1 (max'_mem s hs)).2, hl₁],
  intros i hk'i hil,
  refine eq_of_le_of_not_lt (le_of_not_lt (fin.find_min hl hil)) _,
  intros hi,
  refine lt_irrefl _ ((max'_lt_iff _ _).1
    (show s.max' hs < ⟨i, hil⟩, from hk'i) _ _),
  rw mem_filter,
  refine ⟨mem_univ _, _⟩,
  rwa [fin.cast_le_mk, fin.eta]
end

end
