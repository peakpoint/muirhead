/-
Copyright (c) 2023 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/

import analysis.mean_inequalities
import matrix.doubly_stochastic.birkhoff
import ineq.symm_sum
import ineq.doubly_stochastic

open_locale big_operators

open finset

lemma real.prod_pow {ι : Type*} {a : ℝ} {s : finset ι} {f : ι → ℝ} (h : ∀ x ∈ s, 0 ≤ f x) :
  (∏ x in s, f x) ^ a = ∏ x in s, f x ^ a :=
begin
  induction s using finset.cons_induction with i s his hs,
  { exact real.one_rpow _ },
  rw finset.forall_mem_cons at h,
  rw [prod_cons, prod_cons, real.mul_rpow h.1 (prod_nonneg h.2), hs h.2]
end

variables {ι : Type*} [fintype ι] [decidable_eq ι]

private lemma symm_mean_right_sum_le {ι' : Type*} [fintype ι']
  (c : ι' → ℝ) (hc0 : ∀ i, 0 ≤ c i)
  (hc1 : ∑ i, c i = 1)
  (v : ι' → ι → ℝ) (z : ι → ℝ) (hz : ∀ i, 0 < z i) :
  symm_mean z (∑ i, c i • v i) ≤ ∑ i, c i * symm_mean z (v i) :=
begin
  simp_rw [symm_mean_def, mul_sum, sum_apply, pi.smul_apply, smul_eq_mul],
  rw sum_comm,
  apply sum_le_sum,
  intros σ _,
  calc  ∏ i, z i ^ ∑ j, c j * v j (σ i)
      = ∏ i, ∏ j, z i ^ (c j * v j (σ i)) :
          prod_congr rfl $ λ i _, real.rpow_sum_of_pos (hz _) _ _
  ... = ∏ i, ∏ j, (z i ^ v j (σ i)) ^ c j :
          prod_congr rfl $ λ i _, prod_congr rfl $ λ j _,
            by rw mul_comm; exact real.rpow_mul (hz _).le _ _
  ... = ∏ j, (∏ i, z i ^ v j (σ i)) ^ c j :
          by rw prod_comm; apply prod_congr rfl; intros j _;
            rw real.prod_pow;
            intros;
            exact (real.rpow_pos_of_pos (hz _) _).le
  ... ≤ ∑ j, c j * ∏ i, z i ^ v j (σ i) :
          real.geom_mean_le_arith_mean_weighted _ c _ (λ _ _, hc0 _) hc1 $
            λ _ _, prod_nonneg $ λ _ _, (real.rpow_pos_of_pos (hz _) _).le
end

/-- **Muirhead's Inequality** -/
theorem majorize.symm_mean_le_symm_mean {p q : ι → ℝ} (hpq : majorize q p)
  (z : ι → ℝ) (hz : ∀ i, 0 < z i) :
  symm_mean z q ≤ symm_mean z p :=
begin
  obtain ⟨M, hM, hM'⟩ := hpq.exists_doubly_stochastic,
  rcases hM.mem_convex_hull' with ⟨w, hw0, hw1, hMw⟩,
  rw [show q = matrix.mul_vec.add_monoid_hom_left p M, from hM', hMw, map_sum],
  rw [matrix.mul_vec.add_monoid_hom_left, add_monoid_hom.coe_mk],
  simp_rw [matrix.smul_mul_vec_assoc],
  convert symm_mean_right_sum_le w hw0 hw1 _ z hz,
  have : ∀ σ : ι ≃ ι, σ.to_pequiv.to_matrix.mul_vec p = p ∘ σ,
  { intro σ,
    ext i,
    rw [function.comp_app, matrix.mul_vec, matrix.dot_product],
    simp_rw [pequiv.equiv_to_pequiv_to_matrix, matrix.one_apply, boole_mul],
    rw [sum_ite_eq, if_pos (mem_univ _)] },
  simp_rw [this, symm_mean_equiv_right],
  rw [← sum_mul, hw1, one_mul]
end
