/-
Copyright (c) 2023 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/

import algebra.big_operators.order
import group_theory.perm.fin
import data.matrix.notation

open_locale big_operators

variables {ι α β : Type*} [decidable_eq ι] [fintype ι]

section symm_sum

variables [add_comm_monoid α]

/-- Symmetric sum. -/
def symm_sum (f : (ι → β) → α) (z : ι → β) :=
  ∑ (σ : equiv.perm ι), f (z ∘ σ)

lemma symm_sum_fin_one (f : (fin 1 → β) → α) (a) :
  symm_sum f ![a] = f ![a] :=
begin
  simp only [symm_sum, fintype.univ_of_subsingleton, equiv.symm_symm, equiv.symm_trans_self,
    equiv.equiv_congr_refl, equiv.coe_refl, function.embedding.coe_fn_mk, id.def,
    finset.sum_singleton, equiv.perm.coe_one, function.comp.right_id]
end

lemma symm_sum_fin_two (f : (fin 2 → β) → α) (a b) :
  symm_sum f ![a, b] = f ![a, b] + f ![b, a] :=
begin
  simp only [symm_sum],
  rw ← equiv.sum_comp equiv.perm.decompose_fin.symm,
  rw finset.sum_finset_product _ finset.univ (λ _, finset.univ),
  all_goals { try { apply_instance } },
  swap,
  { simp only [finset.mem_univ, and_self, forall_const] },
  rw [finset.sum_fin_eq_sum_range, finset.sum_range_succ, finset.sum_range_one,
    dif_pos (show 0 < 2, from dec_trivial),
    dif_pos (show 1 < 2, from dec_trivial)],
  simp only [fintype.univ_of_subsingleton, equiv.symm_symm, equiv.symm_trans_self,
    equiv.equiv_congr_refl, equiv.coe_refl, function.embedding.coe_fn_mk, id.def,
    fin.mk_zero, finset.sum_singleton, equiv.perm.decompose_fin_symm_of_one,
    equiv.swap_self, function.comp.right_id, fin.mk_one],
  congr' 2,
  ext i,
  fin_cases i;
  refl
end

end symm_sum

variables [comm_semiring α] [has_pow α β]

variables (z : ι → α) (w : ι → β)

-- I don't know what else to call it
def symm_mean := symm_sum (λ w', ∏ i, z i ^ w' i) w

lemma symm_mean_def : symm_mean z w = ∑ σ : equiv.perm ι, ∏ i, z i ^ w (σ i) := rfl

lemma symm_mean_def' : symm_mean z w = ∑ σ : equiv.perm ι, ∏ i, z (σ i) ^ w i :=
calc ∑ σ : equiv.perm ι, ∏ i, z i ^ w (σ i)
    = ∑ σ : equiv.perm ι, ∏ i, z (σ.symm (σ i)) ^ w (σ i) :
  by simp_rw [equiv.symm_apply_apply]
... = ∑ σ : equiv.perm ι, ∏ (i : ι), z (equiv.symm σ i) ^ w i :
  finset.sum_congr rfl $ λ σ _, equiv.prod_comp σ (λ i, z (σ.symm i) ^ w i)
... = ∑ σ : equiv.perm ι, ∏ (i : ι), z (σ i) ^ w i :
  function.bijective.sum_comp
    (show function.bijective (equiv.symm : equiv.perm ι → equiv.perm ι),
      from function.bijective_iff_has_inverse.2
        ⟨equiv.symm, λ _, equiv.symm_symm _, λ _, equiv.symm_symm _⟩)
    (λ σ : equiv.perm ι, ∏ (i : ι), z (σ i) ^ w i)

lemma symm_mean_fin_one (z : α) (w : β) : symm_mean ![z] ![w] = z ^ w :=
begin
  rw [symm_mean, symm_sum_fin_one, finset.prod_fin_eq_prod_range, finset.prod_range_one],
  refl
end

lemma symm_mean_fin_two (z₁ z₂ : α) (w₁ w₂ : β) :
  symm_mean ![z₁, z₂] ![w₁, w₂] = z₁ ^ w₁ * z₂ ^ w₂ + z₁ ^ w₂ * z₂ ^ w₁ :=
begin
  rw [symm_mean, symm_sum_fin_two],
  iterate 2 { rw [finset.prod_fin_eq_prod_range, finset.prod_range_succ, finset.prod_range_one] },
  refl
end

lemma symm_mean_equiv_left (σ : equiv.perm ι) : symm_mean (z ∘ σ) w = symm_mean z w :=
begin
  rw [symm_mean_def', symm_mean_def'],
  exact function.bijective.sum_comp (group.mul_left_bijective σ)
    (λ σ' : equiv.perm ι, ∏ i, z (σ' i) ^ w i)
end

lemma symm_mean_equiv_right (σ : equiv.perm ι) : symm_mean z (w ∘ σ) = symm_mean z w :=
function.bijective.sum_comp (group.mul_left_bijective σ)
  (λ σ' : equiv.perm ι, ∏ i, z i ^ w (σ' i))
