/-
Copyright (c) 2023 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/

import ineq.majorize
import data.fin.tuple.sort

open_locale big_operators

open finset

variables {α : Type*}
  [linear_ordered_add_comm_monoid α]
  [decidable_rel ((≤) : α → α → Prop)]

section

variables {n : ℕ} {a b : fin n → α}

lemma monotone.sort_eq_of_fn (ha : monotone a) :
  (univ.val.map a).sort (≤) = list.of_fn a :=
begin
  apply list.eq_of_perm_of_sorted _ (multiset.sort_sorted _ _) (list.monotone.of_fn_sorted ha),
  rw [← multiset.coe_eq_coe, multiset.sort_eq],
  show multiset.map _ ↑(list.fin_range n) = _,
  rw multiset.coe_map,
  congr,
  apply list.ext_le,
  { rw [list.length_map, list.length_fin_range, list.length_of_fn] },
  intros,
  rw [list.nth_le_of_fn', list.nth_le_map', list.nth_le_fin_range]
end

lemma antitone.sort_eq_of_fn (ha : antitone a) :
  (univ.val.map a).sort (≥) = list.of_fn a :=
monotone.sort_eq_of_fn ha.dual_right

lemma antitone.majorize (ha : antitone a) (hb : antitone b) :
  majorize a b ↔
    (∀ i, ((list.of_fn a).take i).sum ≤ ((list.of_fn b).take i).sum)
    ∧ ∑ i, a i = ∑ i, b i :=
begin
  simp_rw [← ha.sort_eq_of_fn, ← hb.sort_eq_of_fn],
  refl
end

end

variables {ι : Type*} [fintype ι] (l : ι → α)

/-- Sort a vector. -/
def sort_desc : fin (fintype.card ι) → α :=
  λ i, list.nth_le ((univ.val.map l).sort (≥)) i $
    by rw [multiset.length_sort, multiset.card_map]; exact i.2

lemma sort_desc_antitone : antitone (sort_desc l) :=
begin
  intros i j h,
  have : fintype.card ι = ((univ.val.map ((@order_dual.to_dual α) ∘ l)).sort (≤)).length,
  { rw [multiset.length_sort, multiset.card_map], refl },
  let f := fin.cast this,
  rw sort_desc,
  exact ((univ.val.map ((@order_dual.to_dual α) ∘ l)).sort_sorted (≤)).nth_le_mono
    (show f i ≤ f j, from h)
end

lemma of_fn_sort_desc : list.of_fn (sort_desc l) = (univ.val.map l).sort (≥) :=
begin
  rw sort_desc,
  apply list.ext_le,
  { rw [list.length_of_fn, multiset.length_sort, multiset.card_map], refl },
  intros,
  apply list.nth_le_of_fn'
end

lemma map_sort_desc : univ.val.map (sort_desc l) = univ.val.map l :=
begin
  show multiset.map _ ↑(list.fin_range _) = _,
  rw multiset.coe_map,
  rw ← multiset.sort_eq (≥) (univ.val.map l),
  congr,
  apply list.ext_le,
  { rw [list.length_map, list.length_fin_range, multiset.length_sort, multiset.card_map], refl },
  intros,
  rw [list.nth_le_map', list.nth_le_fin_range],
  refl
end

lemma sum_sort_desc : ∑ i, sort_desc l i = ∑ i, l i :=
begin
  rw [finset.sum_eq_multiset_sum, finset.sum_eq_multiset_sum, map_sort_desc]
end

theorem sort_desc_majorize_iff (a b : ι → α) :
  majorize (sort_desc a) (sort_desc b) ↔ majorize a b :=
begin
  rw [majorize_def, majorize_def,
    ← of_fn_sort_desc a, ← of_fn_sort_desc b,
    antitone.sort_eq_of_fn (sort_desc_antitone a),
    antitone.sort_eq_of_fn (sort_desc_antitone b),
    sum_sort_desc,
    sum_sort_desc]
end
