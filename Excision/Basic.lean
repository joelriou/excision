/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# ...

-/

@[expose] public section

open AlgebraicTopology CategoryTheory

lemma SimplexCategory.δ_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    SimplexCategory.δ i j = Fin.succAbove i j := rfl

lemma SimplexCategory.σ_apply {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    SimplexCategory.σ i j = Fin.predAbove i j := rfl

namespace Convexity

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

variable (R) in
/-- The type of (bundled) affine maps between two convex spaces. -/
protected structure ConvexSpace.AffineMap
    (X Y : Type*) [ConvexSpace R X] [ConvexSpace R Y] where
  /-- The underlying map of an affine map between convex spaces. -/
  toFun : X → Y
  isAffineMap_toFun : IsAffineMap R toFun := by fun_prop

open Topology

instance {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] :
    FunLike (ConvexSpace.AffineMap R X Y) X Y where
  coe := ConvexSpace.AffineMap.toFun
  coe_injective := fun ⟨f, _⟩ ⟨g, _⟩ h ↦ by simpa

@[ext]
lemma ConvexSpace.AffineMap.ext {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    {f g : ConvexSpace.AffineMap R X Y} (h : (f : X → Y) = g) : f = g :=
  DFunLike.coe_injective h

@[fun_prop]
lemma ConvexSpace.AffineMap.isAffineMap
    {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    (f : ConvexSpace.AffineMap R X Y) :
    IsAffineMap R f :=
  f.isAffineMap_toFun

@[simp]
lemma StdSimplex.iConvexComb_single {M : Type*} (x : StdSimplex R M) :
    x.iConvexComb single = x := by
  aesop

@[ext]
lemma StdSimplex.affineMap_ext {M : Type*} {Y : Type*} [ConvexSpace R Y]
    {f g : ConvexSpace.AffineMap R (StdSimplex R M) Y}
    (h : ∀ (i : M), f (.single i) = g (.single i)) : f = g := by
  ext x
  conv_lhs => rw [← StdSimplex.iConvexComb_single x]
  conv_rhs => rw [← StdSimplex.iConvexComb_single x]
  rw [f.isAffineMap.map_iConvexComb, g.isAffineMap.map_iConvexComb]
  aesop

/-- The (bundled) affine map `StdSimplex R M → StdSimplex R N` induced
by a map `f : M → N`. -/
@[simps, implicit_reducible]
noncomputable def StdSimplex.affineMap {M N : Type*} (f : M → N) :
    ConvexSpace.AffineMap R (StdSimplex R M) (StdSimplex R N) where
  toFun := StdSimplex.map f

@[simp]
lemma StdSimplex.sConvexComb_map_iConvexComb {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y)
    (s : StdSimplex R (StdSimplex R M)) :
    sConvexComb (map (fun s ↦ iConvexComb s f) s) = iConvexComb (sConvexComb s) f :=
  calc
    _ = iConvexComb s fun s ↦ sConvexComb (map f s) := sConvexComb_map _ _
    _ = sConvexComb (map f (sConvexComb s)) := by
        rw [StdSimplex.map_sConvexComb, sConvexComb_sConvexComb, sConvexComb_map,
          iConvexComb_map]

/-- Constructor for (bundled) affine maps from a standard simplex to a convex space. -/
@[simps, implicit_reducible]
noncomputable def StdSimplex.affineMapMk {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y) :
    ConvexSpace.AffineMap R (StdSimplex R M) Y where
  toFun s := iConvexComb s f
  isAffineMap_toFun.map_sConvexComb s := by simp

@[fun_prop]
lemma isAffineMap_const {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (y : Y) :
    IsAffineMap R (fun (_ : X) ↦ y) where
  map_sConvexComb _ := by simp

namespace ConvexSpace

/-- The composition of bundled affine maps between convex spaces. -/
@[simps, implicit_reducible]
def AffineMap.comp
    {X Y Z : Type*} [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z]
    (g : ConvexSpace.AffineMap R Y Z) (f : ConvexSpace.AffineMap R X Y) :
    ConvexSpace.AffineMap R X Z where
  toFun := g ∘ f

/-- A constant map between convex spaces, as a bundled affine map. -/
@[simps, implicit_reducible]
def AffineMap.const {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (y : Y) :
    ConvexSpace.AffineMap R X Y where
  toFun _ := y

variable (Y : Type*) [ConvexSpace R Y]

variable (R) in
/-- Given a convex space `Y`, this is the simplicial set whose `n`-simplices are
affine maps from the `n`-dimensional standard simplex to `Y`. -/
protected noncomputable abbrev toSSet : SSet where
  obj n := ConvexSpace.AffineMap R (StdSimplex R (Fin (n.unop.len + 1))) Y
  map f := ↾fun g ↦ g.comp (StdSimplex.affineMap f.unop)
  map_comp _ _ := by
    ext
    dsimp
    rw [← StdSimplex.map_comp]
    rfl

variable (R) in
/-- Given a convex space `Y`, this is the augmented simplicial set
whose `n`-simplices are affine maps from the `n`-dimensional standard simplex to `Y`. -/
noncomputable abbrev toSSetAugmented : SSet.Augmented where
  left := ConvexSpace.toSSet R Y
  right := PUnit
  hom.app _ := ↾fun _ ↦ .unit

attribute [local simp] SimplicialObject.δ_def SimplexCategory.δ_apply
  SimplicialObject.σ_def SimplexCategory.σ_apply in
variable {Y} in
/-- Given a convex space `Y` (over a semiring `R`) and `y : Y`, this is an extra degeneracy
for `ConvexSpace.toSSetAugmented R Y`. In degree `0`, it is given by `[y]`, and otherwise
it sends a `n`-simplex `[y₀, ..., yₙ]` to `[y, y₀, ..., yₙ]`, where affine maps
from the standard `n`-simplex to `Y` are identified to tuples `[y₀, ..., yₙ]` given
by the images of the vertices. -/
@[simps]
noncomputable def extraDegeneracy (y : Y) : (toSSetAugmented R Y).ExtraDegeneracy where
  s' := ↾fun _ ↦ .const y
  s n := ↾fun f ↦ StdSimplex.affineMapMk (Fin.cases y (fun i ↦ f (.single i)))
  s₀_comp_δ₁ := by dsimp; ext _ i; fin_cases i; simp
  s_comp_δ n i := by ext _ j; obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp
  s_comp_σ n i := by ext _ j; obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp

end ConvexSpace

end Convexity
