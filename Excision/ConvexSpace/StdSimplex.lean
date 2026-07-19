/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Excision.ConvexSpace.AffineMap

/-!
# API for the standard simplex

-/

@[expose] public section

namespace Convexity

namespace StdSimplex

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

@[simp]
lemma iConvexComb_single {M : Type*} (x : StdSimplex R M) :
    x.iConvexComb single = x := by
  aesop

@[ext]
lemma affineMap_ext {M : Type*} {Y : Type*} [ConvexSpace R Y]
    {f g : ConvexSpace.AffineMap R (StdSimplex R M) Y}
    (h : ∀ (i : M), f (.single i) = g (.single i)) : f = g := by
  ext x
  conv_lhs => rw [← iConvexComb_single x]
  conv_rhs => rw [← iConvexComb_single x]
  rw [f.isAffineMap.map_iConvexComb, g.isAffineMap.map_iConvexComb]
  aesop

/-- The (bundled) affine map `StdSimplex R M → StdSimplex R N` induced
by a map `f : M → N`. -/
@[simps, implicit_reducible]
noncomputable def affineMap {M N : Type*} (f : M → N) :
    ConvexSpace.AffineMap R (StdSimplex R M) (StdSimplex R N) where
  toFun := map f

@[simp]
lemma sConvexComb_map_iConvexComb {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y)
    (s : StdSimplex R (StdSimplex R M)) :
    sConvexComb (map (fun s ↦ iConvexComb s f) s) = iConvexComb (sConvexComb s) f :=
  calc
    _ = iConvexComb s fun s ↦ sConvexComb (map f s) := sConvexComb_map _ _
    _ = sConvexComb (map f (sConvexComb s)) := by
        rw [StdSimplex.map_sConvexComb, sConvexComb_sConvexComb, sConvexComb_map,
          iConvexComb_map]

/-- Constructor for (bundled) affine maps from a standard simplex to a convex space. -/
@[simps, implicit_reducible]
noncomputable def affineMapMk {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y) :
    ConvexSpace.AffineMap R (StdSimplex R M) Y where
  toFun s := iConvexComb s f
  isAffineMap_toFun.map_sConvexComb s := by simp

open BigOperators

@[simps]
noncomputable def isobarycenter
    {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
    {M : Type*} [Nonempty M] [Fintype M] : StdSimplex K M where
  weights := ∑ (m : M), .single m (Fintype.card M)⁻¹
  nonneg := Finset.sum_nonneg (by simp)
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp

end StdSimplex

namespace ConvexSpace.AffineMap

variable {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
  {M : Type*} [Nonempty M] [Fintype M] {Y : Type*} [ConvexSpace K Y]
  (f : ConvexSpace.AffineMap K (StdSimplex K M) Y)

noncomputable def isobarycenter : Y := f .isobarycenter

end ConvexSpace.AffineMap

end Convexity
