/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Bundled affine maps between convex spaces

-/

@[expose] public section

namespace Convexity

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

namespace ConvexSpace

@[fun_prop]
lemma isAffineMap_const {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (y : Y) :
    IsAffineMap R (fun (_ : X) ↦ y) where
  map_sConvexComb _ := by simp

variable (R) in
/-- The type of (bundled) affine maps between two convex spaces. -/
protected structure AffineMap
    (X Y : Type*) [ConvexSpace R X] [ConvexSpace R Y] where
  /-- The underlying map of an affine map between convex spaces. -/
  toFun : X → Y
  isAffineMap_toFun : IsAffineMap R toFun := by fun_prop

namespace AffineMap

instance {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] :
    FunLike (ConvexSpace.AffineMap R X Y) X Y where
  coe := ConvexSpace.AffineMap.toFun
  coe_injective := fun ⟨f, _⟩ ⟨g, _⟩ h ↦ by simpa

@[ext]
lemma ext {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    {f g : ConvexSpace.AffineMap R X Y} (h : (f : X → Y) = g) : f = g :=
  DFunLike.coe_injective h

@[fun_prop]
lemma isAffineMap
    {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    (f : ConvexSpace.AffineMap R X Y) :
    IsAffineMap R f :=
  f.isAffineMap_toFun

/-- The composition of bundled affine maps between convex spaces. -/
@[simps, implicit_reducible]
def comp
    {X Y Z : Type*} [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z]
    (g : ConvexSpace.AffineMap R Y Z) (f : ConvexSpace.AffineMap R X Y) :
    ConvexSpace.AffineMap R X Z where
  toFun := g ∘ f

/-- A constant map between convex spaces, as a bundled affine map. -/
@[simps, implicit_reducible]
def const {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (y : Y) :
    ConvexSpace.AffineMap R X Y where
  toFun _ := y

end AffineMap

end ConvexSpace

end Convexity
