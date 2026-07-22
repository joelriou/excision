/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# ...

-/

@[expose] public section

namespace Convexity

-- TODO: remove `stdSimplex`
/-- The bijection between `StdSimplex ℝ ι` and `stdSimplex ℝ ι`. -/
@[simps]
noncomputable def StdSimplex.equiv
    {R ι : Type*} [Semiring R] [PartialOrder R] [IsOrderedAddMonoid R] [Fintype ι] :
    StdSimplex R ι ≃ stdSimplex R ι where
  toFun s := ⟨s.weights, s.nonneg, by
    have := s.total
    rwa [Finsupp.sum_fintype _ _ (by simp)] at this ⟩
  invFun s :=
    { weights := ∑ (i : ι), .single i (s i)
      nonneg := Finset.sum_nonneg (by simp)
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
        rw [← s.2.2]
        congr
        ext i
        rw [Finset.sum_eq_single i (by aesop) (by simp)]
        simp
        rfl }
  left_inv s := by
    ext i
    dsimp
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ Finsupp.single_eq_of_ne' hj) (by simp),
      Finsupp.single_eq_same]
    rfl
  right_inv s := by
    ext i
    change (∑ (i : ι), Finsupp.single i (s i)) i = s i
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    rw [Finset.sum_eq_single i (by aesop) (by simp)]
    simp

end Convexity
