/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Excision.ConvexSpace.StdSimplex
public import Excision.SimplexCategory.Basic
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Affine simplices in the singular simplicial set of a convex space

-/

universe w u

@[expose] public section

open CategoryTheory Limits

namespace Convexity

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

namespace ConvexSpace

variable (Y : Type w) [ConvexSpace R Y]

variable {Y} in
/-- The cone of an affine map from the standard simplex. -/
noncomputable def AffineMap.cone
    {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin n)) Y) (y : Y) :
    ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y :=
  StdSimplex.affineMapMk (Fin.cases y (fun i ↦ s (.single i)))

variable {Y} in
lemma AffineMap.cone_def
    {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin n)) Y) (y : Y) :
    s.cone y = StdSimplex.affineMapMk (Fin.cases y (fun i ↦ s (.single i))) := rfl

@[simp]
lemma AffineMap.cone_mk₁ (y y₀ : Y) :
    (StdSimplex.affineMapMk (R := R) ![y₀]).cone y =
      StdSimplex.affineMapMk ![y, y₀] := by
  rw [cone_def]
  congr
  ext i
  fin_cases i <;> aesop

@[simp]
lemma AffineMap.cone_mk₂ (y y₀ y₁ : Y) :
    (StdSimplex.affineMapMk (R := R) ![y₀, y₁]).cone y =
      StdSimplex.affineMapMk ![y, y₀, y₁] := by
  rw [cone_def]
  congr
  ext i
  fin_cases i <;> aesop

variable (R) in
/-- Given a convex space `Y`, this is the simplicial set whose `n`-simplices are
affine maps from the `n`-dimensional standard simplex to `Y`. -/
noncomputable abbrev toSSet : SSet where
  obj n := ConvexSpace.AffineMap R (StdSimplex R (Fin (n.unop.len + 1))) Y
  map f := ↾fun g ↦ g.comp (StdSimplex.affineMap f.unop)
  map_comp _ _ := by
    ext
    dsimp
    rw [← StdSimplex.map_comp]
    rfl

@[simp]
lemma toSSet_δ_zero (y : Y) {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y) :
    (toSSet R Y).δ 0 (s.cone y) = s := by
  ext
  simp [SimplicialObject.δ_def, SimplexCategory.δ_apply,
    AffineMap.cone_def, StdSimplex.affineMapMk_toFun]

section

variable {Y}

attribute [local simp] SimplicialObject.δ_def SimplexCategory.δ_apply

@[simp]
lemma toSSet_δ_zero_affineMapMk₂ (y₀ y₁ : Y) :
    (toSSet R Y).δ 0 (StdSimplex.affineMapMk ![y₀, y₁]) =
      StdSimplex.affineMapMk ![y₁] := by
  ext i; fin_cases i; simp

@[simp]
lemma toSSet_δ_one_affineMapMk₂ (y₀ y₁ : Y) :
    (toSSet R Y).δ 1 (StdSimplex.affineMapMk ![y₀, y₁]) =
      StdSimplex.affineMapMk ![y₀] := by
  ext i; fin_cases i; simp

@[simp]
lemma toSSet_δ_zero_affineMapMk₃ (y₀ y₁ y₂ : Y) :
    (toSSet R Y).δ 0 (StdSimplex.affineMapMk ![y₀, y₁, y₂]) =
      StdSimplex.affineMapMk ![y₁, y₂] := by
  ext i; fin_cases i <;> simp

@[simp]
lemma toSSet_δ_one_affineMapMk₃ (y₀ y₁ y₂ : Y) :
    (toSSet R Y).δ 1 (StdSimplex.affineMapMk ![y₀, y₁, y₂]) =
      StdSimplex.affineMapMk ![y₀, y₂] := by
  ext i; fin_cases i <;> simp

@[simp]
lemma toSSet_δ_two_affineMapMk₃ (y₀ y₁ y₂ : Y) :
    (toSSet R Y).δ 2 (StdSimplex.affineMapMk ![y₀, y₁, y₂]) =
      StdSimplex.affineMapMk ![y₀, y₁] := by
  ext i; fin_cases i <;> simp [Fin.succAbove]

end

variable (R) in
/-- Given a convex space `Y`, this is the augmented simplicial set
whose `n`-simplices are affine maps from the `n`-dimensional standard simplex to `Y`. -/
noncomputable abbrev toSSetAugmented : SSet.Augmented where
  left := toSSet R Y
  right := PUnit
  hom.app _ := ↾fun _ ↦ .unit

attribute [local simp] SimplicialObject.δ_def SimplexCategory.δ_apply
  SimplicialObject.σ_def SimplexCategory.σ_apply AffineMap.cone_def
  StdSimplex.affineMapMk_toFun in
variable {Y} in
/-- Given a convex space `Y` (over a semiring `R`) and `y : Y`, this is an extra degeneracy
for `ConvexSpace.toSSetAugmented R Y`. In degree `0`, it is given by `[y]`, and otherwise
it sends a `n`-simplex `[y₀, ..., yₙ]` to `[y, y₀, ..., yₙ]`, where affine maps
from the standard `n`-simplex to `Y` are identified to tuples `[y₀, ..., yₙ]` given
by the images of the vertices. -/
@[simps]
noncomputable def toSSet.extraDegeneracy (y : Y) :
    (toSSetAugmented R Y).ExtraDegeneracy where
  s' := ↾fun _ ↦ .const y
  s n := ↾fun f ↦ f.cone y
  s₀_comp_δ₁ := by ext _ i; fin_cases i; simp
  s_comp_δ _ _ := by ext _ j; obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp
  s_comp_σ _ _ := by ext _ j; obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp

variable {Y} {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{max u w} C]

/-- Given a convex space `Y`, `y : Y` and `n : ℕ`, this is the morphism from
affine `n`-chains (with coefficients in `M`) to affine `n + 1`-chains which
sends a simplex `[y₀, ..., yₙ]` to `[y, y₀, ..., yₙ]`. -/
noncomputable def toSSet.cone (y : Y) (M : C) (n : ℕ) :
    ((toSSet R Y).chainComplex M).X n ⟶
      ((toSSet R Y).chainComplex M).X (n + 1) :=
  ((extraDegeneracy y).map (sigmaConst.obj M)).s n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma toSSet.ι_cone
    (y : Y) (M : C) {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y) :
    SSet.ιChainComplex _ s ≫ toSSet.cone (R := R) y M n =
      SSet.ιChainComplex _ (s.cone y) := by
  simp [cone, SimplicialObject.Augmented.ExtraDegeneracy.map, SSet.ιChainComplex]

end ConvexSpace

end Convexity
