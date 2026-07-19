/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Homotopy equivalences and degreewise split mono

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

set_option backward.defeqAttrib.useBackward true in
lemma homotopyEquivalences_shortComplexF_iff_of_degreewiseSplit
    (σ : ∀ n, (S.map (eval _ _ n)).Splitting) :
    homotopyEquivalences _ _ S.f ↔ Nonempty (Homotopy (𝟙 S.X₃) 0) := by
  let e := ComplexShape.embeddingDownNat
  let σ' (n : ℤ) : ((S.map (e.extendFunctor C)).map (eval _ _ n)).Splitting :=
    Nonempty.some (by
      by_cases hn : ∃ i, e.f i = n
      · obtain ⟨i, rfl⟩ := hn
        -- this should be generalized and made a separate def
        let iso : e.extendFunctor C ⋙ eval _ _ (e.f i) ≅ eval C (.down ℕ) i :=
          NatIso.ofComponents (fun K ↦ K.extendXIso e rfl) (fun f ↦ by
            simp [extendMap_f _ _ rfl])
        exact ⟨(σ i).ofIso (S.mapNatIso iso.symm)⟩
      · exact ⟨{
          r := 0
          s := 0
          f_r := (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _
          s_g := (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _
          id := (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _ }⟩)
  have := CochainComplex.homotopyEquivalences_shortComplexF_iff_of_splitting _ σ'
  dsimp at this
  rw [homotopyEquivalences_extendMap_iff] at this
  rw [this]
  -- TODO: add a lemma `Homotopy.extendMap_iff`
  apply Equiv.nonempty_congr
  refine Equiv.trans ?_ (Homotopy.extendEquiv e ..).symm
  simp
  rfl

end ChainComplex
