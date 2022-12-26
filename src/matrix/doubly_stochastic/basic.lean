/-
Copyright (c) 2022 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/

import matrix.support

open_locale big_operators matrix

namespace matrix

variables {n α : Type} [fintype n] [ordered_add_comm_monoid α] [has_one α]

structure doubly_stochastic (M : matrix n n α) : Prop :=
  (nonneg : ∀ i j, 0 ≤ M i j)
  (row : ∀ i, ∑ j, M i j = 1)
  (col : ∀ j, ∑ i, M i j = 1)

namespace doubly_stochastic

variables {M : matrix n n α}

lemma le_one (hM : M.doubly_stochastic) (i j : n) : M i j ≤ 1 :=
calc M i j = ∑ j in {j}, M i j :
  finset.sum_singleton.symm
... ≤ ∑ j, M i j :
  finset.sum_le_sum_of_subset_of_nonneg (finset.subset_univ _) $ λ _ _ _, hM.nonneg _ _
... = 1 : hM.row i

lemma transpose (hM : M.doubly_stochastic) : Mᵀ.doubly_stochastic :=
  ⟨λ i j, hM.nonneg j i, hM.col, hM.row⟩

variables [ne_zero (1 : α)]

lemma apply_curry_finsupp_nonzero (hM : M.doubly_stochastic) (i : n) :
  M.finsupp.curry i ≠ 0 :=
begin
  intros h,
  apply @one_ne_zero α,
  rw ← hM.row i,
  apply finset.sum_eq_zero,
  intros j _,
  show M.finsupp (i, j) = _,
  rw [← finsupp.curry_apply, h, finsupp.zero_apply]
end

lemma card_finsupp_row_pos (hM : M.doubly_stochastic) (i : n) :
  0 < (M.finsupp.curry i).support.card :=
begin
  rw [finset.card_pos, finsupp.support_nonempty_iff],
  exact hM.apply_curry_finsupp_nonzero i
end

lemma card_univ_le_card_support (hM : M.doubly_stochastic) :
  fintype.card n ≤ M.support.card :=
calc fintype.card n = ∑ i, 1 :
  fintype.card_eq_sum_ones
... ≤ ∑ i, (M.finsupp.curry i).support.card :
  finset.sum_le_sum $ λ i _, hM.card_finsupp_row_pos _
... = M.support.card :
  M.support_card_eq_sum_row.symm

lemma card_support_finsupp_eq_one (hM : M.doubly_stochastic)
  (h : M.support.card = fintype.card n) (i : n) :
  (M.finsupp.curry i).support.card = 1 :=
begin
  symmetry,
  by_contra h₁,
  have h' := lt_of_le_of_ne (nat.one_le_of_lt (hM.card_finsupp_row_pos i)) h₁,
  apply h.symm.not_lt,
  calc fintype.card n
      = ∑ i, 1 :
    fintype.card_eq_sum_ones
  ... < ∑ i, (M.finsupp.curry i).support.card :
    finset.sum_lt_sum (λ i _, hM.card_finsupp_row_pos i) ⟨i, finset.mem_univ _, h'⟩
  ... = M.support.card : M.support_card_eq_sum_row.symm
end

lemma card_support_finsupp_col_eq_one (hM : M.doubly_stochastic)
  (h : M.support.card = fintype.card n) (j : n) :
  ((M.finsupp.equiv_map_domain (equiv.prod_comm n n)).curry j).support.card = 1 :=
by rw [finsupp.transpose', hM.transpose.card_support_finsupp_eq_one];
  rw [card_support_transpose, h]

lemma support_curry_inj (hM : M.doubly_stochastic)
  (hn : M.support.card = fintype.card n) (i₁ i₂ : n)
  (h : (M.finsupp.curry i₁).support = (M.finsupp.curry i₂).support) : i₁ = i₂ :=
begin
  obtain ⟨j₁, h₁⟩ := finsupp.card_support_eq_one.mp (hM.card_support_finsupp_eq_one hn i₁),
  obtain ⟨j₂, h₂⟩ := finsupp.card_support_eq_one.mp (hM.card_support_finsupp_eq_one hn i₂),
  rw [finsupp.support_eq_singleton.mpr h₁, finsupp.support_eq_singleton.mpr h₂,
    finset.singleton_inj] at h,
  rw h at *,
  rw [curry_finsupp_apply] at *,
  obtain ⟨i, hi⟩ := finsupp.card_support_eq_one.mp (hM.card_support_finsupp_col_eq_one hn j₂),
  have h₁':= fun_like.congr_fun hi.2 i₁,
  have h₂' := fun_like.congr_fun hi.2 i₂,
  iterate 2 {
    rw [finsupp.curry_apply, finsupp.equiv_map_domain_apply, equiv.prod_comm_symm,
      equiv.prod_comm_apply, prod.swap_prod_mk, finsupp_apply] at h₁' h₂' },
  rw h₁' at h₁,
  rw h₂' at h₂,
  rw finsupp.single_apply_ne_zero at h₁ h₂,
  rw [h₁.1.1, h₂.1.1],
end

lemma _root_.equiv.doubly_stochastic [zero_le_one_class α] [decidable_eq n] (σ : equiv.perm n) :
  (σ.to_pequiv.to_matrix : matrix n n α).doubly_stochastic :=
⟨λ i j, begin
  rw [pequiv.equiv_to_pequiv_to_matrix, one_apply],
  split_ifs,
  exact zero_le_one,
  exact le_rfl
end,
λ i, by simp_rw [pequiv.equiv_to_pequiv_to_matrix, one_apply];
  rw [finset.sum_ite_eq, if_pos]; exact finset.mem_univ _,
λ j, by simp_rw [pequiv.equiv_to_pequiv_to_matrix, one_apply, ← equiv.eq_symm_apply];
  rw [finset.sum_ite_eq', if_pos]; exact finset.mem_univ _⟩

/-- An `n` by `n` matrix is doubly stochastic and has exactly `n` non-zero entries
  iff it's a permutation matrix -/
lemma card_eq_card_support_iff [decidable_eq n] [zero_le_one_class α] :
  M.doubly_stochastic ∧ M.support.card = fintype.card n ↔
  ∃ σ : equiv.perm n, M = σ.to_pequiv.to_matrix :=
begin
  split,
  { rintro ⟨hM, hn⟩,
    have h := λ i, finsupp.card_support_eq_one.mp (hM.card_support_finsupp_eq_one hn i),
    refine ⟨equiv.of_bijective (λ i, classical.some $ h i) _, _⟩,
    { rw ← finite.injective_iff_bijective,
      intros i₁ i₂ hi,
      apply hM.support_curry_inj hn,
      have hi₁ := classical.some_spec (h i₁),
      have hi₂ := classical.some_spec (h i₂),
      rw ← finsupp.support_eq_singleton at hi₁ hi₂,
      rw [hi₁, hi₂, show classical.some _ = _, from hi] },
    { ext i j,
      have hi := classical.some_spec (h i),
      rw [pequiv.equiv_to_pequiv_to_matrix, equiv.of_bijective_apply, one_apply],
      split_ifs with h' h',
      { rw [← h', ← hM.row i],
        calc  M i (classical.some (h i))
            = ∑ j, finsupp.single (classical.some (h i))
                (M.finsupp.curry i (classical.some (h i))) j :
                by rw [finsupp.sum_univ_single, curry_finsupp_apply]
        ... = ∑ j, M i j :
                finset.sum_congr rfl $ λ j' _, by rw [← hi.2, curry_finsupp_apply] },
      { by_contra hMij,
        rw ← finsupp.support_eq_singleton at hi,
        rw [← curry_finsupp_apply M i j, ← ne.def, ← finsupp.mem_support_iff,
          hi, finset.mem_singleton] at hMij,
        exact h' hMij.symm } } },
  { rintro ⟨σ, rfl⟩,
    exact ⟨σ.doubly_stochastic, σ.card_support_to_matrix⟩ }
end

end doubly_stochastic

end matrix
