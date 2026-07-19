/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# ...

-/

@[expose] public section

open CategoryTheory Pretriangulated HomologicalComplex Limits

variable {C : Type*} [Category* C] [Preadditive C]

namespace CochainComplex

variable [HasZeroObject C] [HasBinaryBiproducts C]
  (S : ShortComplex (CochainComplex C ℤ))

lemma trianglehOfDegreewiseSplit_distinguished
    (σ : ∀ n, (S.map (eval _ _ n)).Splitting) :
    trianglehOfDegreewiseSplit S σ ∈ distTriang _ :=
  (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit ..).2
    ⟨_, σ, ⟨Iso.refl _⟩⟩

lemma homotopyEquivalences_shortComplexF_iff_of_splitting
    (σ : ∀ n, (S.map (eval _ _ n)).Splitting) :
    homotopyEquivalences _ _ S.f ↔ Nonempty (Homotopy (𝟙 S.X₃) 0) := by
  rw [← HomotopyCategory.isZero_quotient_obj_iff,
    ← isIso_quotient_map_iff_homotopyEquivalences]
  exact (Triangle.isZero₃_iff_isIso₁ _ (trianglehOfDegreewiseSplit_distinguished S σ)).symm

end CochainComplex

namespace ChainComplex

variable [HasZeroObject C] [HasBinaryBiproducts C]
  (S : ShortComplex (ChainComplex C ℕ))

lemma homotopyEquivalences_shortComplexF_iff_of_degreewiseSplit
    (σ : ∀ n, (S.map (eval _ _ n)).Splitting) :
    homotopyEquivalences _ _ S.f ↔ Nonempty (Homotopy (𝟙 S.X₃) 0) := by
  sorry

end ChainComplex
