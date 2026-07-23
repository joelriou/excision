/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Excision.SingularHomology.Subdivision

/-!
# ...

-/

universe w

@[expose] public section

open Convexity

namespace Convexity.ConvexSpace.AffineMap

variable {ι ι₁ ι₂ : Type*} [Fintype ι] [Fintype ι₁] [Fintype ι₂]

/-- The diameter of a simplex in the standard simplex. -/
noncomputable def diam (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ ι₁) (StdSimplex ℝ ι₂)) : ℝ :=
  Metric.diam (Set.range s.toContinuousMap)

lemma zero_le_diam (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ ι₁) (StdSimplex ℝ ι₂)) :
    0 ≤ s.diam :=
  Metric.diam_nonneg

lemma diam_sd_le {n : ℕ} (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) (StdSimplex ℝ ι))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (s.sd σ).diam ≤ n / (n + 1) * s.diam := by
  sorry

lemma diam_sdIter_le
    {n : ℕ} (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) (StdSimplex ℝ ι))
    {k : ℕ} (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    (s.sdIter σ).diam ≤ (n / (n + 1)) ^ k * s.diam := by
  induction k with
  | zero => simp
  | succ k hk =>
    nth_rw 2 [add_comm k 1]
    rw [sdIter_succ, pow_add, pow_one, mul_assoc]
    exact (diam_sd_le _ _).trans (mul_le_mul_of_nonneg_left (hk _) (by positivity))

end Convexity.ConvexSpace.AffineMap
