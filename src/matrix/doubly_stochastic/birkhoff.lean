/-
Copyright (c) 2023 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/

import matrix.doubly_stochastic.basic
import analysis.convex.combination
import combinatorics.hall.finite

open_locale big_operators

open finset matrix

noncomputable theory

namespace matrix.doubly_stochastic

variables {m n α : Type*} [fintype m] [fintype n]
  [decidable_eq m] [decidable_eq n]
  [linear_ordered_field α] {M : matrix m n α}

/-- Inequality used in the application of Hall. -/
lemma hall (hM : M.doubly_stochastic) (s : finset m) :
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

/-- **Birkhoff's theorem** -/
theorem mem_convex_hull (hM : M.doubly_stochastic) :
  M ∈ convex_hull α ((pequiv.to_matrix ∘ equiv.to_pequiv) '' set.univ : set (matrix m n α)) :=
begin
  let e := fintype.equiv_of_card_eq hM.card_eq_card,
  cases (univ : finset m).eq_empty_or_nonempty with hm hm,
  { haveI := univ_eq_empty_iff.mp hm,
    apply subset_convex_hull,
    exact ⟨e, set.mem_univ _, subsingleton.elim _ _⟩ },
  induction hN : M.support.card using nat.strong_induction_on
    with N h_ind generalizing M,
  obtain ⟨c, hc_inj, hc⟩ := (all_card_le_bUnion_card_iff_exists_injective' _).1 hM.hall,
  let σ : m ≃ n := equiv.of_bijective c ⟨hc_inj, hc_inj.surjective_of_fintype e⟩,
  have hσ : ∀ i, M i (σ i) ≠ 0 :=
    λ i, (M.mem_support_curry_finsupp _ _).mp (hc i),
  let x := (univ.image $ λ i, M i (c i)).min' (hm.image _),
  obtain ⟨a, _, ha : M a (σ a) = x⟩ := mem_image.mp (min'_mem _ _),
  have hx_min : ∀ i, x ≤ M i (σ i) :=
    λ i, min'_le _ _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩),
  set M' := M - x • σ.to_pequiv.to_matrix with hM',
  have h1x_nonneg : 0 ≤ 1 - x := ha ▸ sub_nonneg_of_le (hM.le_one _ _),
  by_cases h1x : 1 - x = 0,
  { rw sub_eq_zero at h1x,
    apply subset_convex_hull,
    use [σ, set.mem_univ _],
    show σ.to_pequiv.to_matrix = M,
    ext i j,
    rw [pequiv.to_matrix, equiv.to_pequiv_apply],
    simp_rw [option.mem_some_iff],
    have hi' : M i (σ i) = 1 := le_antisymm (hM.le_one i _) (h1x.symm ▸ hx_min i),
    split_ifs with hij hij,
    { rw [← hij, hi'] },
    { exact (hM.row_eq_zero_of_ne hi' _ hij).symm } },
  have hM_wz : univ.center_mass ![x, 1 - x] ![σ.to_pequiv.to_matrix, (1 - x)⁻¹ • M'] = M,
  { rw [center_mass_eq_of_sum_1],
    all_goals {
      rw fin.sum_univ_two,
      iterate { rw [cons_val_zero, cons_val_one, head_cons] },
      try { rw smul_inv_smul₀ h1x },
      rw add_sub_cancel'_right } },
  rw ← hM_wz,
  apply (convex_convex_hull α _).center_mass_mem,
  { intros i _,
    fin_cases i,
    { rw ← ha,
      apply hM.nonneg },
    { exact h1x_nonneg } },
  { rw fin.sum_univ_two,
    calc 0 < 1 : zero_lt_one
    ... = _ : (add_sub_cancel'_right x _).symm },
  { intros i _,
    fin_cases i,
    { apply subset_convex_hull,
      exact ⟨σ, set.mem_univ _, rfl⟩ },
    show (1 - x)⁻¹ • M' ∈ _,
    refine h_ind _ _ _ rfl,
    { rw [← hN, support_smul_eq (inv_ne_zero h1x)],
      swap, apply_instance,
      apply card_lt_card,
      rw ssubset_iff,
      use [a, σ a],
      rw [insert_subset, subset_iff, not_mem_support_iff, mem_support_iff],
      refine ⟨_, hσ _, _⟩,
      { apply sub_eq_zero_of_eq,
        show _ = x • _,
        rw [pequiv.to_matrix, equiv.to_pequiv_apply],
        simp_rw [option.mem_some_iff],
        rw [if_pos rfl, smul_eq_mul, mul_one, ha] },
      { rintro ⟨i, j⟩ hij,
        rw mem_support_iff at hij ⊢,
        by_cases hj : j = σ i,
        { rw hj,
          apply hσ },
        { change M i j - x • _ ≠ 0 at hij,
          rw [pequiv.to_matrix, equiv.to_pequiv_apply] at hij,
          simp_rw [option.mem_some_iff] at hij,
          rw [if_neg (ne.symm hj), smul_zero, sub_zero] at hij,
          exact hij } } },
    { rw doubly_stochastic_iff,
      split,
      { intros i j,
        apply mul_nonneg (inv_nonneg_of_nonneg h1x_nonneg),
        apply sub_nonneg_of_le,
        show x • _ ≤ _,
        rw [pequiv.to_matrix, equiv.to_pequiv_apply],
        simp_rw [option.mem_some_iff],
        rw [smul_eq_mul, mul_boole],
        split_ifs with hj hj,
        { rw ← hj,
          apply hx_min },
        { apply hM.nonneg } },
      have hσ' := σ.doubly_stochastic α,
      simp_rw [pi.smul_apply, ← smul_sum, hM', pi.sub_apply, pi.smul_apply, sum_sub_distrib,
        ← smul_sum, hσ'.row, hσ'.col, hM.row, hM.col, smul_eq_mul, mul_one, inv_mul_cancel h1x],
      exact ⟨λ _, rfl, λ _, rfl⟩ } }
end

/-- **Birkhoff's theorem**, finset version. -/
theorem mem_convex_hull_finset (hM : M.doubly_stochastic) :
  M ∈ convex_hull α ((univ.image (pequiv.to_matrix ∘ equiv.to_pequiv) :
    finset (matrix m n α)) : set (matrix m n α)) :=
begin
  rw [finset.coe_image, finset.coe_univ],
  exact hM.mem_convex_hull
end

/-- **Birkhoff's theorem**, using a weight function. -/
theorem mem_convex_hull' (hM : M.doubly_stochastic) :
  ∃ c : (m ≃ n) → α,
    (∀ σ, 0 ≤ c σ) ∧
    ∑ σ, c σ = 1 ∧
    M = ∑ σ, c σ • σ.to_pequiv.to_matrix :=
begin
  have := hM.mem_convex_hull_finset,
  rw finset.mem_convex_hull at this,
  rcases this with ⟨c, hc0, hc1, hM'⟩,
  use (c ∘ pequiv.to_matrix ∘ equiv.to_pequiv),
  split,
  { intro σ,
    apply hc0,
    apply mem_image_of_mem,
    exact mem_univ _ },
  split,
  show ∑ (σ : m ≃ n), (c (pequiv.to_matrix (equiv.to_pequiv σ))) = 1,
  rw [← hc1, sum_image],
  swap,
  rw [← hM', center_mass_eq_of_sum_1 _ _ hc1, sum_image],
  refl,
  all_goals {
    intros σ₁ _ σ₂ _ h,
    have := pequiv.to_matrix_injective h,
    rw pequiv.ext_iff at this,
    ext i,
    specialize this i,
    rwa [equiv.to_pequiv_apply, equiv.to_pequiv_apply, option.some_inj] at this }
end

end matrix.doubly_stochastic
