/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.ZMod.IntUnitsPower

/-!
# Permutations

-/

@[expose] public section

namespace Equiv.Perm

variable {n : ℕ}

/-- Given `i : Fin (n + 2)` and `σ : Perm (Fin (n + 1)`, this is the permutation
of `Fin (n + 2)` which sends `0` to `i` and `j.succ` to `i.succAbove (σ j)`. -/
noncomputable def equivSuccSymm (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    Perm (Fin (n + 2)) :=
  Equiv.ofBijective
    (Fin.cases i (Fin.succAbove i ∘ σ)) (by
      rw [Nat.bijective_iff_injective_and_card]
      refine ⟨fun j k h ↦ ?_, rfl⟩
      obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;>
        obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_eq_succ <;> aesop)

@[simp]
lemma equivSuccSymm_zero (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    equivSuccSymm i σ 0 = i := rfl

@[simp]
lemma equivSuccSymm_succ (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    equivSuccSymm i σ j.succ = i.succAbove (σ j) := rfl

@[simp]
lemma equivSuccSymm_symm_eq_zero (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    (equivSuccSymm i σ).symm i = 0 :=
  (equivSuccSymm i σ).injective (by simp)

@[simp]
lemma equivSuccSymm_symm_succAbove (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    (equivSuccSymm i σ).symm (i.succAbove (σ j)) = j.succ :=
  (equivSuccSymm i σ).injective (by simp)

variable (n) in
lemma equivSuccSymm_uncurry_bijective : Function.Bijective (equivSuccSymm (n := n)).uncurry := by
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨fun ⟨i, σ⟩ ⟨i', σ'⟩ h ↦ ?_, ?_⟩
  · obtain rfl : i = i' := by simpa using DFunLike.congr_fun h 0
    obtain rfl : σ = σ' := by
      ext j : 1
      simpa using DFunLike.congr_fun h j.succ
    rfl
  · rw [Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin,
      Nat.factorial_succ (n + 1)]

/-- A bijection between `Perm (Fin (n + 2))` and `Fin (n + 2) × Perm (Fin (n + 1))`.
See `equivSuccSymm` for the definition of the inverse map. -/
noncomputable def equivSucc : Perm (Fin (n + 2)) ≃ Fin (n + 2) × Perm (Fin (n + 1)) :=
  (Equiv.ofBijective _ (equivSuccSymm_uncurry_bijective n)).symm

@[simp]
lemma equivSucc_symm (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    equivSucc.symm ⟨i, σ⟩ = equivSuccSymm i σ := rfl

@[simp]
lemma sign_equivSuccSymm (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    (equivSuccSymm i σ).sign = (-1) ^ i.val * σ.sign := by
  sorry

end Equiv.Perm
