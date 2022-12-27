/-
Copyright (c) 2022 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/

import matrix.doubly_stochastic.basic
import analysis.convex.combination
import combinatorics.hall.finite

open_locale big_operators classical

open finset matrix

noncomputable theory

namespace matrix.doubly_stochastic

variables {n α : Type*} [fintype n] [linear_ordered_field α] {M : matrix n n α}

/-- Inequality used in the application of Hall. -/
lemma hall (hM : M.doubly_stochastic) (s : finset n) :
  s.card ≤ (s.bUnion (λ i, (M.finsupp.curry i).support)).card :=
let t := s.bUnion (λ i, (M.finsupp.curry i).support) in
nat.cast_le.mp $
  calc (s.card : α)
      = ∑ i in s, 1 :
          by rw [sum_const, nsmul_one]
  ... ≤ ∑ i in s, ∑ j in t, M i j : -- actually an equality but that's not needed
          sum_le_sum $ λ i hi, by {
            rw [← hM.row i, ← sum_filter_ne_zero],
            apply sum_le_sum_of_subset_of_nonneg,
            { intros j hj,
              rw mem_bUnion,
              use [i, hi],
              rw [finsupp.mem_support_iff, curry_finsupp_apply],
              exact (mem_filter.1 hj).2 },
            { intros,
              apply hM.nonneg } }
  ... ≤ ∑ i, ∑ j in t, M i j :
          sum_le_sum_of_subset_of_nonneg (subset_univ _) $
            λ _ _ _, sum_nonneg' $ λ _, hM.nonneg _ _
  ... = t.card :
          by rw sum_comm; simp_rw [hM.col]; rw [sum_const, nsmul_one]

theorem birkhoff (hM : M.doubly_stochastic) :
  M ∈ convex_hull α ((pequiv.to_matrix ∘ equiv.to_pequiv) '' set.univ : set (matrix n n α)) :=
begin
  cases (univ : finset n).eq_empty_or_nonempty with hn hn,
  { sorry },
  induction hM' : M.support.card using nat.strong_induction_on
    with N h_ind generalizing M,
  have h' := hM.card_univ_le_card_support,
  cases eq_or_lt_of_le h' with h h,
  { cases card_eq_card_support_iff.mp ⟨hM, h.symm⟩ with σ hσ,
    rw hσ,
    apply subset_convex_hull,
    exact ⟨σ, set.mem_univ _, rfl⟩ },
  obtain ⟨c, hc_inj, hc'⟩ := (all_card_le_bUnion_card_iff_exists_injective' _).1 hM.hall,
  let σ : equiv.perm n := equiv.of_bijective c (finite.injective_iff_bijective.mp hc_inj),
  have hc : ∀ i, M i (σ i) ≠ 0 :=
    λ i, (M.mem_support_curry_finsupp _ _).mp (hc' i),
  let x := (univ.image $ λ i, M i (c i)).min' (hn.image _),
  obtain ⟨a, _, ha : M a (σ a) = x⟩ := mem_image.mp (min'_mem _ _),
  have hx_min : ∀ i, x ≤ M i (σ i) :=
    λ i, min'_le _ _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩),
  set M' := M - x • σ.to_pequiv.to_matrix with hM',
  have h1x : 1 - x ≠ 0 := sorry,
  have hM_wz : univ.center_mass ![x, 1 - x] ![σ.to_pequiv.to_matrix, (1 - x)⁻¹ • M'] = M,
  sorry { rw [center_mass_eq_of_sum_1],
    all_goals {
      rw fin.sum_univ_two,
      iterate { rw [cons_val_zero, cons_val_one, head_cons] },
      try { rw smul_inv_smul₀ h1x },
      rw add_sub_cancel'_right } },
  rw ← hM_wz,
  apply (convex_convex_hull α _).center_mass_mem,
  sorry { intros i _,
    rw ← ha,
    fin_cases i,
    { apply hM.nonneg },
    { apply sub_nonneg_of_le,
      apply hM.le_one } },
  sorry { rw fin.sum_univ_two,
    calc 0 < 1 : zero_lt_one
    ... = _ : (add_sub_cancel'_right x _).symm },
  { sorry }
end

end matrix.doubly_stochastic
