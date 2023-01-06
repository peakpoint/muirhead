/-
Copyright (c) 2023 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/

import ineq.matrix
import ineq.fin

open_locale big_operators

open finset

variables {α : Type*} [linear_ordered_field α] [@decidable_rel α (≤)] [@decidable_rel α (<)]

theorem exists_doubly_stochastic' {n : ℕ} {p q : fin n → α}
  (hp : antitone p) (hq : antitone q)
  (hpq₁ : ∑ i, p i = ∑ i, q i)
  (hpq₂ : ∀ i, (((univ.val.map q).sort (≥)).take i).sum ≤
    (((univ.val.map p).sort (≥)).take i).sum) :
  ∃ M : matrix (fin n) (fin n) α, M.doubly_stochastic ∧ q = M.mul_vec p :=
begin
  induction ht : (univ.filter (λ i, p i ≠ q i)).card
    using nat.strong_induction_on with t h_ind generalizing p,
  by_cases ht0 : t = 0,
  { rw [ht0, card_eq_zero, filter_eq_empty_iff] at ht,
    use 1,
    rw matrix.one_mul_vec,
    refine ⟨matrix.doubly_stochastic_one, _⟩,
    ext,
    rw not_not.1 (ht _ (mem_univ _)) },
  rw ← ht at h_ind ht0,
  have hpq : p ≠ q,
  { rintro rfl,
    apply ht0,
    rw [card_eq_zero, filter_eq_empty_iff],
    intros,
    rw not_not },
  simp_rw [hp.sort_eq_of_fn, hq.sort_eq_of_fn] at hpq₂,
  obtain ⟨p', hp', hp'₁, hp'₂, h_card, M', hM'₁, hM'₂⟩ := exists_fn_lt p q hpq hp hq hpq₁ hpq₂,
  specialize h_ind _ h_card hp' (hp'₁.trans hpq₁),
  simp_rw [hp'.sort_eq_of_fn, hq.sort_eq_of_fn] at h_ind,
  obtain ⟨M, hM₁, hM₂⟩ := h_ind (λ _, (hp'₂ _).1) rfl,
  use [M.mul M'],
  refine ⟨hM₁.mul hM'₁, _⟩,
  rw [hM₂, hM'₂, matrix.mul_vec_mul_vec]
end

variables {ι : Type*} [fintype ι] [decidable_eq ι]

variables (l : ι → α)

noncomputable def sort_equiv :=
  (tuple.sort (λ i, order_dual.to_dual $ l ((fintype.equiv_fin ι).symm i))).trans
  (fintype.equiv_fin ι).symm

lemma comp_sort_equiv_eq_sort_desc : l ∘ sort_equiv l = sort_desc l :=
begin
  have : monotone (order_dual.to_dual ∘ l ∘ (sort_equiv l)) :=
    tuple.monotone_sort (order_dual.to_dual ∘ l ∘ (fintype.equiv_fin ι).symm),
  rw [← list.of_fn_inj, of_fn_sort_desc],
  refine list.eq_of_perm_of_sorted _
    (list.monotone_iff_of_fn_sorted.1 this) (multiset.sort_sorted _ _),
  rw [← multiset.coe_eq_coe, multiset.sort_eq, ← list.map_of_fn, ← multiset.coe_map],
  congr,
  ext i,
  rw [multiset.count_univ, multiset.coe_count, list.count_eq_one_of_mem],
  exact list.nodup_of_fn_of_injective (equiv.injective _),
  rw [list.mem_of_fn, function.surjective.range_eq (equiv.surjective _)],
  apply set.mem_univ
end

lemma sort_equiv_to_matrix_mul_vec :
  (sort_equiv l).to_pequiv.to_matrix.mul_vec l = sort_desc l :=
begin
  ext i,
  rw [← comp_sort_equiv_eq_sort_desc, sort_equiv],
  rw [equiv.to_pequiv_trans, pequiv.to_matrix_trans, pequiv.to_pequiv_mul_matrix,
    equiv.to_pequiv_symm, pequiv.to_matrix_symm, matrix.mul_vec, matrix.dot_product],
  simp_rw [matrix.transpose_apply, pequiv.to_matrix, equiv.to_pequiv_apply,
    option.mem_some_iff, boole_mul, ← equiv.eq_symm_apply],
  rw [sum_ite_eq', if_pos (mem_univ _)],
  refl
end

lemma vec_mul_sort_equiv_to_matrix :
  (sort_equiv l).to_pequiv.to_matrix.vec_mul (sort_desc l) = l :=
by rw [← sort_equiv_to_matrix_mul_vec, matrix.vec_mul_mul_vec, ← pequiv.to_matrix_symm,
  ← equiv.to_pequiv_symm, ← pequiv.to_matrix_trans, ← equiv.to_pequiv_trans,
  equiv.symm_trans_self, equiv.to_pequiv_refl, pequiv.to_matrix_refl, matrix.vec_mul_one]

/-- If `p` majorizes `q`, there exists a doubly stochastic matrix `M` such that `q = M p` -/
theorem majorize.exists_doubly_stochastic {p q : ι → α} (hpq : majorize q p) :
  ∃ M : matrix ι ι α, M.doubly_stochastic ∧ q = M.mul_vec p :=
begin
  rw ← sort_desc_majorize_iff q p at hpq,
  have hp := sort_desc_antitone p,
  have hq := sort_desc_antitone q,
  rw antitone.majorize hq hp at hpq,
  simp_rw [of_fn_sort_desc, ← map_sort_desc p, ← map_sort_desc q] at hpq,
  obtain ⟨M, hM, hM'⟩ := exists_doubly_stochastic' hp hq hpq.2.symm hpq.1,
  use [(sort_equiv q).symm.to_pequiv.to_matrix.mul (M.mul (sort_equiv p).to_pequiv.to_matrix),
    ((sort_equiv q).symm.doubly_stochastic α).mul
      (hM.mul ((sort_equiv p).doubly_stochastic α))],
  rw [← matrix.mul_vec_mul_vec, ← matrix.mul_vec_mul_vec, sort_equiv_to_matrix_mul_vec,
    ← hM', equiv.to_pequiv_symm, pequiv.to_matrix_symm, matrix.mul_vec_transpose,
    vec_mul_sort_equiv_to_matrix]
end
