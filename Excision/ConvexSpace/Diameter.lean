/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Excision.ConvexSpace.StdSimplex
public import Excision.ConvexSpace.Top
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Module

/-!
# Diameter of the subdivision of affine

-/

@[expose] public section

namespace Convexity

namespace ConvexSpace

namespace AffineMap

variable {n : ℕ} {X E : Type*} [ConvexSpace ℝ X] [NormedAddCommGroup E]
  [ConvexSpace ℝ E]

/-- The diameter of the range of an affine map to a normed real vector space. -/
noncomputable def diam (f : ConvexSpace.AffineMap ℝ X E) : ℝ :=
  Metric.diam (Set.range f)

lemma diam_nonneg (f : ConvexSpace.AffineMap ℝ X E) :
    0 ≤ f.diam :=
  Metric.diam_nonneg

variable [NormedSpace ℝ E] [IsModuleConvexSpace ℝ E]

lemma diam_sd_le
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) E)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (s.sd σ).diam ≤ n / (n + 1) * s.diam := by
  have : IsModuleConvexSpace ℝ E := inferInstance
  sorry

lemma diam_sdIter_le
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) E)
    {k : ℕ} (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    (s.sdIter σ).diam ≤ (n / (n + 1)) ^ k * s.diam := by
  induction k with
  | zero => simp
  | succ k hk =>
    nth_rw 2 [add_comm k 1]
    rw [sdIter_succ, pow_add, pow_one, mul_assoc]
    exact (diam_sd_le _ _).trans (mul_le_mul_of_nonneg_left (hk _) (by positivity))

end AffineMap

end ConvexSpace

@[simp]
lemma StdSimplex.diam_equiv_image_range_affineMap
    {α β : Type*} [Fintype β] (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ α) (StdSimplex ℝ β)) :
    Metric.diam (StdSimplex.equiv '' (Set.range s)) = (StdSimplex.ι.comp s).diam := by
  rw [← isometry_subtype_coe.diam_image]
  dsimp [ConvexSpace.AffineMap.diam]
  rw [Set.range_comp, ← Set.image_comp]
  rfl

end Convexity
