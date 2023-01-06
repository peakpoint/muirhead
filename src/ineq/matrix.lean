/-
Copyright (c) 2023 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/

import ineq.majorize
import matrix.doubly_stochastic.basic
import algebra.order.group.min_max
import tactic.ring

open_locale big_operators

open finset

variables {α : Type*} [linear_ordered_field α] [@decidable_rel α (<)]

section

variables {n β : Type*} [linear_order n] [add_comm_monoid β]
variables (a : n) (s : finset n) (p : n → β)

private lemma sum_lt_le₁ :
  ∑ i in s, p i =
  ∑ i in s.filter (λ i, a ≤ i), p i +
  ∑ i in s.filter (λ i, i < a), p i :=
by simp_rw [← not_lt]; rw [add_comm, ← sum_ite]; simp_rw [if_t_t]

private lemma sum_lt_le₂ :
  ∑ i in s, p i =
  ∑ i in s.filter (λ i, a < i), p i +
  ∑ i in s.filter (λ i, i ≤ a), p i :=
by simp_rw [← not_lt, ← sum_ite, if_t_t]

example (P Q : Prop) (h : P → Q) : Q ∧ P ↔ P := and_iff_right_of_imp h

private lemma sum_lt_le₃ :
  ∑ i in s.filter (λ i, a ≤ i), p i =
  ∑ i in s.filter (λ i, a < i), p i +
  ∑ i in s.filter (λ i, i = a), p i :=
by rw [sum_lt_le₂ a, filter_filter, filter_filter];
  simp_rw [le_antisymm_iff, and_iff_right_of_imp (le_of_lt), and_comm]

end

private lemma and_imp_imp {a b c d e f : Prop} (h₁ : a → b → c) (h₂ : d → e → f) :
  (a ∧ d) → (b ∧ e) → (c ∧ f) := by itauto

lemma exists_fn_lt
  {n} (p q : fin n → α) (hpq : p ≠ q)
  (hp : antitone p)
  (hq : antitone q)
  (h₁ : ∑ i, p i = ∑ i, q i)
  (h₂ : ∀ i, ((list.of_fn q).take i).sum ≤ ((list.of_fn p).take i).sum) :
  ∃ p' : fin n → α,
    antitone p' ∧
    ∑ i, p' i = ∑ i, p i ∧
    (∀ i, ((list.of_fn q).take i).sum ≤ ((list.of_fn p').take i).sum ∧
      ((list.of_fn p').take i).sum ≤ ((list.of_fn p).take i).sum) ∧
    (univ.filter (λ i, p' i ≠ q i)).card <
    (univ.filter (λ i, p i ≠ q i)).card ∧
    ∃ M : matrix (fin n) (fin n) α,
      M.doubly_stochastic ∧
      p' = M.mul_vec p :=
begin
  obtain ⟨k, l, hkl, hqpk, hqpl, h⟩ := exists_lt_eq_gt hpq.symm h₁.symm h₂,
  have hqlk := hq hkl.le,
  set b := (p k + p l) / 2 with hb,
  set d := (p k - p l) / 2 with hd,
  set c := max (|q k - b|) (|q l - b|) with hc,
  have hbd₁ : b + d = p k,
  { rw [← add_div, add_add_sub_cancel, half_add_self] },
  have hbd₂ : b - d = p l,
  { rw [← sub_div, add_sub_sub_cancel, half_add_self] },
  have h0c : 0 ≤ c,
  { rw le_max_iff,
    left,
    exact abs_nonneg _ },
  have hcd : c < d,
   { rw [eq_comm, max_eq_iff] at hc,
    cases hc;
    rw [← hc.1, abs_lt, sub_lt_iff_lt_add', hbd₁,
      lt_sub_iff_add_lt', ← sub_eq_add_neg, hbd₂],
    { exact ⟨lt_of_lt_of_le hqpl hqlk, hqpk⟩ },
    { exact ⟨hqpl, lt_of_le_of_lt hqlk hqpk⟩ } },
  have hkbc₁ : b + c < p k := hbd₁ ▸ add_lt_add_left hcd b,
  have hkbc₂ : q k ≤ b + c,
  { rw [eq_comm, max_eq_iff] at hc,
    cases hc;
    rw [← hc.1, ← sub_le_iff_le_add'],
    { exact le_abs_self _ },
    { exact (le_abs_self _).trans hc.2 } },
  have hlbc₁ : p l < b - c := hbd₂ ▸ sub_lt_sub_left hcd b,
  have hlbc₂ : b - c ≤ q l,
  { rw [eq_comm, max_eq_iff] at hc,
    cases hc;
    rw [← hc.1, sub_le_comm, ← neg_sub],
    { exact (neg_le_abs_self _).trans hc.2 },
    { exact neg_le_abs_self _ } },
  let p' := λ j, ite (j = k) (b + c) (ite (j = l) (b - c) (p j)),
  have hp' : ∀ j, p' j = ite _ _ _ := λ _, rfl,
  have hk' : k ∈ univ.filter (λ x, ¬x = l) := mem_filter.2 ⟨mem_univ _, hkl.ne⟩,
  have hl' : l ∈ univ.filter (λ x, ¬x = k) := mem_filter.2 ⟨mem_univ _, hkl.ne.symm⟩,
  use p',
  refine ⟨_, _, _, _, _⟩,
  { intros i j hij,
    show ite _ _ _ ≤ ite _ _ _,
    split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈,
    { exact le_refl _ },
    { exfalso,
      rw [h₁, h₃] at hij,
      exact hkl.not_le hij },
    { rw h₁ at hij,
      exact hkbc₁.le.trans (hp hij) },
    { rw [sub_eq_add_neg, add_le_add_iff_left],
      exact neg_le_self h0c },
    { exact le_refl _ },
    { rw h₄ at hij,
      by_contra' h',
      have : k < i := hp.reflect_lt (
        calc p i < b - c : h'
        ... ≤ q l : hlbc₂
        ... ≤ q k : hqlk
        ... < p k : hqpk),
      rw ← h _ this (lt_of_le_of_ne hij h₆) at h',
      exact (lt_of_le_of_lt (hq hij) h').not_le hlbc₂ },
    { rw h₇ at hij,
      by_contra' h',
      have : j < l := hp.reflect_lt (
        calc p l < q l : hqpl
        ... ≤ q k : hqlk
        ... ≤ b + c : hkbc₂
        ... < p j : h' ),
      rw ← h _ (lt_of_le_of_ne' hij h₁) this at h',
      exact (lt_of_lt_of_le h' (hq hij)).not_le hkbc₂ },
    { rw h₈ at hij,
      exact (hp hij).trans hlbc₁.le },
    { exact hp hij } },
  { calc  ∑ i, ite (i = k) (b + c) (ite (i = l) (b - c) (p i))
        = (b + c) + ∑ i in univ.filter (λ i, ¬i = k), ite (i = l) (b - c) (p i) :
            by rw [sum_ite, filter_eq', if_pos (mem_univ _), sum_singleton]
    ... = p k + p l +
          ∑ i in (univ.filter (λ i, ¬i = k)).filter (λ i, ¬i = l), p i :
            by rw [sum_ite, filter_eq', if_pos hl', sum_singleton,
              ← add_assoc, add_add_sub_cancel, add_halves]
    ... = ∑ i in univ.filter (λ i, i = k), p i +
          ∑ i in (univ.filter (λ i, ¬i = k)).filter (λ i, i = l), p i +
          ∑ i in (univ.filter (λ i, ¬i = k)).filter (λ i, ¬i = l), p i :
            by rw [filter_eq', if_pos (mem_univ _), sum_singleton,
              filter_eq', if_pos hl', sum_singleton]
    ... = ∑ i, p i :
            by rw [add_assoc, ← sum_ite, ← sum_ite];
              simp_rw [if_t_t] },
  { have hp'₁ : ∀ {j}, j < k → p' j = p j,
    { intros j hj,
      rw [hp', if_neg hj.ne, if_neg (hj.trans hkl).ne] },
    have hp'₂ : ∀ {j}, l < j → p' j = p j,
    { intros j hj,
      rw [hp', if_neg (hkl.trans hj).ne', if_neg hj.ne'] },
    have hp'₃ : ∀ {j}, k < j → j < l → p' j = p j,
    { intros j hkj hjl,
      rw [hp', if_neg hkj.ne', if_neg hjl.ne] },
    have h_sum₁ : ∀ i : ℕ, i ≤ k →
      ∑ j in univ.filter (λ j, ↑j < i), p' j =
      ∑ j in univ.filter (λ j, ↑j < i), p j,
    { intros i hik,
      apply sum_congr rfl,
      intros j hj,
      rw mem_filter at hj,
      exact hp'₁ (show ↑j < ↑k, from lt_of_lt_of_le hj.2 hik) },
    have h_sum₂ :
      ∑ j in univ.filter (λ j, j ≤ l), p' j
      = ∑ j in univ.filter (λ j, j ≤ l), p j,
    { let s := univ.filter (λ j, j ≤ l),
      have hk : k ∈ s := mem_filter.2 ⟨mem_univ _, hkl.le⟩,
      have hl : l ∈ s.filter (λ j, ¬j = k) :=
        mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, le_rfl⟩, hkl.ne.symm⟩,
      calc  ∑ (j : fin n) in s, p' j
          = p k + p l + ∑ i in (s.filter (λ j, ¬j = k)).filter (λ j, ¬j = l), p i :
              by rw [sum_ite, filter_eq', if_pos hk, sum_singleton,
                sum_ite, filter_eq', if_pos hl, sum_singleton, ← add_assoc,
                add_add_sub_cancel, add_halves]
      ... = ∑ i in s.filter (λ j, j = k), p i +
            ∑ i in (s.filter (λ j, ¬j = k)).filter (λ j, j = l), p i +
            ∑ i in (s.filter (λ j, ¬j = k)).filter (λ j, ¬j = l), p i :
              by rw [filter_eq', if_pos hk, sum_singleton,
                filter_eq', if_pos hl, sum_singleton]
      ... = ∑ (j : fin n) in s, p j :
              by rw [add_assoc, ← sum_ite, ← sum_ite];
                simp_rw [if_t_t] },
    intros i,
    simp_rw [list.sum_take_of_fn] at ⊢ h₂,
    let s := univ.filter (λ j : fin n, ↑j < i),
    show ∑ _ in s, _ ≤ ∑ _ in s, p' _ ∧ ∑ _ in s, p' _ ≤ ∑ _ in s, _,
    rcases le_or_lt i k with hik | hki,
    { rw h_sum₁ _ hik,
      exact ⟨h₂ _, le_rfl⟩ },
    rcases le_or_lt i l with hil | hli,
    { have : k ∈ s := mem_filter.2 ⟨mem_univ _, hki⟩,
      iterate 3 { rw [sum_lt_le₁ k s, sum_lt_le₃, filter_eq', if_pos this, sum_singleton] },
      rw [hp' k, if_pos rfl],
      iterate { rw filter_filter },
      refine and_imp_imp add_le_add add_le_add _ _,
      refine and_imp_imp add_le_add add_le_add _ ⟨hkbc₂, hkbc₁.le⟩,
      { apply and.imp sum_le_sum sum_le_sum,
        rw ← forall_and_distrib,
        intro j,
        rw ← forall_and_distrib,
        intro hj,
        rw mem_filter at hj,
        have hjl : j < l := show ↑j < ↑l, from (lt_of_lt_of_le hj.2.1 hil),
        rw [hp'₃ hj.2.2 hjl, h _ hj.2.2 hjl],
        exact ⟨le_rfl, le_rfl⟩ },
      { simp_rw [fin.lt_iff_coe_lt_coe, ← lt_min_iff],
        rw h_sum₁ _ (min_le_right i k),
        exact ⟨h₂ _, le_rfl⟩ } },
    { iterate 3 { rw sum_lt_le₂ l s },
      iterate { rw filter_filter },
      have ha₁ : ∀ a, ↑a < i ∧ a ≤ l ↔ a ≤ l :=
        λ a, and_iff_right_of_imp (λ h, lt_of_le_of_lt h hli),
      simp_rw [ha₁],
      rw h_sum₂,
      convert and.intro (h₂ i) le_rfl using 2,
      all_goals { try {
        show _ = ∑ _ in s, _,
        rw sum_lt_le₂ l s,
        iterate { rw filter_filter },
        simp_rw [ha₁] } },
      all_goals { rw add_left_inj,
        apply sum_congr rfl,
        intros j hj,
        rw mem_filter at hj,
        rw hp'₂ hj.2.2 } } },
  { apply card_lt_card,
    rw ssubset_iff,
    have hc' : b + c = q k ∨ b - c = q l,
    { cases le_total (q k) b with hqkb hbqk,
      { have := abs_eq_neg_self.2 (sub_nonpos_of_le (hqlk.trans hqkb)),
        right,
        rw [hc, max_eq_right, this, sub_neg_eq_add, add_sub_cancel'_right],
        rw [this, abs_eq_neg_self.2 (sub_nonpos_of_le hqkb)],
        apply neg_le_neg,
        rwa sub_le_sub_iff_right },
      cases le_total b (q l) with hbql hqlb,
      { have := abs_eq_self.2 (sub_nonneg_of_le (hbql.trans hqlk)),
        left,
        rw [hc, max_eq_left, this, add_sub_cancel'_right],
        rw [this, abs_eq_self.2 (sub_nonneg_of_le hbql)],
        rwa sub_le_sub_iff_right },
      { rw [abs_eq_self.2 (sub_nonneg_of_le hbqk),
          abs_eq_neg_self.2 (sub_nonpos_of_le hqlb),
          neg_sub, eq_comm, max_eq_iff] at hc,
        cases hc;
        rw ← hc.1,
        { left,
          rw add_sub_cancel'_right },
        { right,
          rw sub_sub_cancel } } },
    cases hc',
    use k, swap, use l,
    all_goals { rw [mem_filter, insert_subset, mem_filter, subset_iff, ← hc'] },
    refine ⟨λ h', h'.2 _, ⟨mem_univ _, hlbc₁.ne⟩, _⟩,
    { rw [hp', if_neg hkl.ne.symm, if_pos rfl] },
    swap,
    refine ⟨λ h', h'.2 (if_pos rfl), ⟨mem_univ _, hkbc₁.ne.symm⟩, _⟩,
    all_goals { intros i hi,
      rw mem_filter at ⊢ hi,
      refine ⟨mem_univ _, _⟩,
      intros hi',
      apply hi.2,
      rw [← hi', hp', if_neg, if_neg] },
    all_goals { rintro rfl },
    repeat { exact hqpl.ne hi' },
    repeat { exact hqpk.ne hi'.symm } },
  { let M : matrix (fin n) (fin n) α := λ i j,
      if i = k ∧ j = l ∨ i = l ∧ j = k then (d - c) / (2 * d) else
        if i = j then (if i = k ∨ i = l then (d + c) / (2 * d) else 1) else 0,
    have hM : ∀ i j, M i j = ite _ _ _ := λ i j, rfl,
    have h0d : 0 < d := lt_of_le_of_lt h0c hcd,
    have h02d : 0 < 2 * d := mul_pos zero_lt_two h0d,
    use M,
    split,
    apply matrix.doubly_stochastic.of_transpose_eq_self,
    { ext i j,
      show ite _ _ _ = ite _ _ _,
      congr' 1,
      { rw [and_comm, or_comm, and_comm] },
      { by_cases hij : i = j,
        { rw hij },
        { rw [if_neg hij, if_neg (ne.symm hij)] } } },
    { intros i j,
      rw hM,
      split_ifs,
      { exact div_nonneg (sub_nonneg_of_le hcd.le) h02d.le },
      { exact div_nonneg (add_nonneg h0d.le h0c) h02d.le },
      { exact zero_le_one },
      { exact le_rfl } },
    { intro i,
      have hdc : (d - c) / (2 * d) + (d + c) / (2 * d) = 1,
      { rw [← add_div, sub_add_add_cancel, ← two_mul, div_self h02d.ne.symm] },
      rw [sum_ite, sum_ite, sum_ite, sum_const_zero, add_zero, sum_const, sum_const, sum_const],
      by_cases hik : i = k,
      simp_rw [hik, hkl.ne, eq_self_iff_true, true_and, false_and, or_false, not_true],
      swap,
      by_cases hil : i = l,
      simp_rw [hil, hkl.ne.symm, eq_self_iff_true, true_and, false_and, false_or, not_true],
      swap,
      { simp_rw [hik, hil, false_and, false_or, not_false_iff],
        iterate 2 { rw [filter_false, card_empty, zero_smul, zero_add, filter_true] },
        rw [filter_eq, if_pos (mem_univ _), card_singleton, one_smul] },
      all_goals {
        rw [filter_true, filter_false, card_empty, zero_smul, add_zero,
          filter_eq', if_pos (mem_univ _), card_singleton, one_smul,
          filter_eq, if_pos (mem_filter.2 ⟨mem_univ _, _⟩), card_singleton, one_smul, hdc] },
      { exact hkl.ne.symm },
      { exact hkl.ne } },
    { ext i,
      have hdc₁ : (d - c) / (2 * d) * p l + (d + c) / (2 * d) * p k = b + c,
      swap,
      have hdc₂ : (d - c) / (2 * d) * p k + (d + c) / (2 * d) * p l = b - c,
      all_goals { try {
        rw [← mul_div_right_comm, ← mul_div_right_comm,
          ← add_div, div_eq_iff h02d.ne.symm, hb, hd],
        ring } },
      rw [matrix.mul_vec, matrix.dot_product, hp'],
      simp_rw [hM, ite_mul, one_mul, zero_mul],
      rw [sum_ite, sum_ite, sum_ite, sum_const_zero, add_zero, ← mul_sum, ← mul_sum],
      split_ifs with hik hil,
      { simp_rw [hik, hkl.ne, eq_self_iff_true, true_and, true_or, false_and, or_false, not_true],
        rw [filter_false, sum_empty, add_zero,
          filter_true, filter_eq', if_pos (mem_univ _), sum_singleton,
          filter_eq, if_pos hk', sum_singleton, hdc₁] },
      { simp_rw [hil, hkl.ne.symm, eq_self_iff_true, true_and, or_true,
          false_and, false_or, not_true],
        rw [filter_false, sum_empty, add_zero,
          filter_true, filter_eq', if_pos (mem_univ _), sum_singleton,
          filter_eq, if_pos hl', sum_singleton, hdc₂] },
      { simp_rw [hik, hil, false_and, false_or, not_false_iff],
        iterate 2 { rw [filter_false, sum_empty, mul_zero, filter_true, zero_add] },
        rw [filter_eq, if_pos (mem_univ _), sum_singleton] } } }
end
