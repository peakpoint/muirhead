/-
Copyright (c) 2022 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/

import data.matrix.pequiv

noncomputable theory

open_locale big_operators matrix

namespace matrix

variables {n m α : Type*} [fintype n] [fintype m]

section

variables [has_zero α]

/-- A matrix as a finitely supported function -/
def finsupp (M : matrix n m α) : (n × m) →₀ α :=
  finsupp.of_support_finite (function.uncurry M) (set.to_finite _)

lemma finsupp_apply {M : matrix n m α} (i j) : M.finsupp (i, j) = M i j := rfl

end

lemma curry_finsupp_apply [add_comm_monoid α] (M : matrix n m α) (i j) :
  M.finsupp.curry i j = M i j :=
by rw [finsupp.curry_apply, finsupp_apply]

namespace finsupp

variables [add_comm_monoid α] {M : matrix n m α}

lemma transpose :
  M.finsupp.map_domain prod.swap = Mᵀ.finsupp :=
begin
  ext ⟨j, i⟩,
  exact finsupp.map_domain_apply prod.swap_injective _ (i, j)
end

lemma transpose' :
  M.finsupp.equiv_map_domain (equiv.prod_comm n m) = Mᵀ.finsupp :=
begin
  ext ⟨j, i⟩,
  exact finsupp.equiv_map_domain_apply _ _ (j, i)
end

end finsupp

/-- The non-zero entries of `M` defined as the support of `M.finsupp`. -/
def support [has_zero α] (M : matrix n m α) : finset (n × m) := M.finsupp.support

section support

variable (M : matrix n m α)

section

variables [has_zero α]

lemma mem_support_iff' (a : n × m) : a ∈ M.support ↔ M a.1 a.2 ≠ 0 :=
  finsupp.mem_support_iff

lemma mem_support_iff (i j) : (i, j) ∈ M.support ↔ M i j ≠ 0 :=
  finsupp.mem_support_iff

lemma mem_support_transpose (i j) : (i, j) ∈ Mᵀ.support ↔ M j i ≠ 0 :=
  mem_support_iff _ _ _

lemma support_transpose' :
  M.support.map (equiv.prod_comm n m).to_embedding = Mᵀ.support :=
begin
  ext ⟨i, j⟩,
  rw [finset.mem_map_equiv, equiv.prod_comm_symm, equiv.prod_comm_apply,
    prod.swap_prod_mk, mem_support_iff, mem_support_iff],
  refl
end

lemma card_support_transpose :
  Mᵀ.support.card = M.support.card :=
by rw [← support_transpose', finset.card_map]

lemma support_transpose [decidable_eq n] [decidable_eq m] :
  M.support.image prod.swap = Mᵀ.support :=
begin
  rw [← support_transpose', finset.map_eq_image], refl
end

end

variables [add_comm_monoid α]

lemma finsupp_eq_sum_row :
  M.finsupp = ∑ i, (M.finsupp.curry i).map_domain (prod.mk i) :=
begin
  classical,
  ext ⟨i, j⟩,
  have : ∑ i' in {i}ᶜ, (M.finsupp.curry i').map_domain (prod.mk i') (i, j) = 0,
  { apply finset.sum_eq_zero,
    intros _ hi',
    apply finsupp.map_domain_notin_range,
    rintro ⟨_, h⟩,
    rw [finset.mem_compl, finset.not_mem_singleton] at hi',
    exact hi' (prod.mk.inj h).1 },
  rw [finsupp.coe_finset_sum, finset.sum_apply, fintype.sum_eq_add_sum_compl i,
    finsupp.map_domain_apply (prod.mk.inj_left i), finsupp.curry_apply, this, add_zero]
end

lemma support_card_eq_sum_row :
  M.support.card = ∑ i, (M.finsupp.curry i).support.card :=
begin
  classical,
  conv_lhs { rw [support, finsupp_eq_sum_row] },
  have : ∀ i₁ i₂, i₁ ≠ i₂ → disjoint
    ((M.finsupp.curry i₁).map_domain (prod.mk i₁)).support
    ((M.finsupp.curry i₂).map_domain (prod.mk i₂)).support,
  { intros x y h,
    rw finset.disjoint_iff_ne,
    rintros ⟨i₁, j₁⟩ h₁ ⟨i₂, j₂⟩ h₂ h',
    rw [finsupp.map_domain_support_of_injective (prod.mk.inj_left _)] at h₁ h₂,
    all_goals { try { apply_instance } },
    rw [finset.mem_image] at h₁ h₂,
    rcases h₁ with ⟨a, _, ha⟩,
    rcases h₂ with ⟨b, _, hb⟩,
    rw [← ha, ← hb] at h',
    exact h (prod.mk.inj h').1 },
  rw [finsupp.support_sum_eq_bUnion _ this, finset.card_bUnion],
  apply finset.sum_congr rfl,
  intros i _,
  have h := prod.mk.inj_left i,
  rw [finsupp.map_domain_support_of_injective h, finset.card_image_of_injective _ h],
  { intros, apply this, assumption }
end

lemma _root_.equiv.card_support_to_matrix
  [has_one α] [ne_zero (1 : α)] [decidable_eq n] (σ : equiv.perm n) :
  (σ.to_pequiv.to_matrix : matrix n n α).support.card = fintype.card n :=
begin
  suffices h : σ.to_pequiv.to_matrix.support = finset.univ.image (λ i, (i, σ i)),
  { rw [h, finset.card_image_of_injective, fintype.card],
    intros _ _ hp,
    exact (prod.mk.inj hp).1 },
  ext ⟨i, j⟩,
  rw [mem_support_iff, pequiv.equiv_to_pequiv_to_matrix, finset.mem_image,
    one_apply, ne.ite_ne_right_iff (one_ne_zero' α)],
  simp_rw [prod.mk.inj_iff, finset.mem_univ, exists_true_left, exists_eq_left]
end

end support

end matrix
