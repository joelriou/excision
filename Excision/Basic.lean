/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

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
@[ext]
protected structure ConvexSpace.AffineMap
    (X Y : Type*) [ConvexSpace R X] [ConvexSpace R Y] where
  hom : X → Y
  isAffineMap : IsAffineMap R hom := by fun_prop

@[simp]
lemma StdSimplex.iConvexComb_single {M : Type*} (x : StdSimplex R M) :
    x.iConvexComb single = x := by
  aesop

@[ext]
lemma StdSimplex.affineMap_ext {M : Type*} {Y : Type*} [ConvexSpace R Y]
    {f g : ConvexSpace.AffineMap R (StdSimplex R M) Y}
    (h : ∀ (i : M), f.hom (.single i) = g.hom (.single i)) : f = g := by
  ext x
  conv_lhs => rw [← StdSimplex.iConvexComb_single x]
  conv_rhs => rw [← StdSimplex.iConvexComb_single x]
  rw [f.isAffineMap.map_iConvexComb, g.isAffineMap.map_iConvexComb]
  aesop

attribute [fun_prop] ConvexSpace.AffineMap.isAffineMap

@[simps, implicit_reducible]
noncomputable def StdSimplex.affineMap {M N : Type*} (f : M → N) :
    ConvexSpace.AffineMap R (StdSimplex R M) (StdSimplex R N) where
  hom := StdSimplex.map f

@[simp]
lemma StdSimplex.sConvexComb_map_iConvexComb {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y)
    (s : StdSimplex R (StdSimplex R M)) :
    sConvexComb (map (fun s ↦ iConvexComb s f) s) = iConvexComb (sConvexComb s) f :=
  calc
    _ = iConvexComb s fun s ↦ sConvexComb (map f s) := sConvexComb_map _ _
    _ = sConvexComb (map f (sConvexComb s)) := by
        rw [StdSimplex.map_sConvexComb, sConvexComb_sConvexComb, sConvexComb_map,
          iConvexComb_map]

@[simps, implicit_reducible]
noncomputable def StdSimplex.affineMapMk {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y) :
    ConvexSpace.AffineMap R (StdSimplex R M) Y where
  hom s := iConvexComb s f
  isAffineMap.map_sConvexComb s := by simp

@[fun_prop]
lemma isAffineMap_const {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (y : Y) :
    IsAffineMap R (fun (_ : X) ↦ y) where
  map_sConvexComb _ := by simp

namespace ConvexSpace

@[simps, implicit_reducible]
def AffineMap.comp
    {X Y Z : Type*} [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z]
    (g : ConvexSpace.AffineMap R Y Z) (f : ConvexSpace.AffineMap R X Y) :
    ConvexSpace.AffineMap R X Z where
  hom := g.hom ∘ f.hom

@[simps, implicit_reducible]
def AffineMap.const {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (y : Y) :
    ConvexSpace.AffineMap R X Y where
  hom _ := y

variable (Y : Type*) [ConvexSpace R Y]

variable (R) in
@[simps, implicit_reducible]
protected noncomputable def toSSet : SSet where
  obj n := ConvexSpace.AffineMap R (StdSimplex R (Fin (n.unop.len + 1))) Y
  map f := ↾fun g ↦ g.comp (StdSimplex.affineMap f.unop)
  map_comp _ _ := by
    ext
    dsimp
    rw [← StdSimplex.map_comp]
    rfl

variable (R) in
@[simps, implicit_reducible]
noncomputable def toAugmentedSSet : SSet.Augmented where
  left := ConvexSpace.toSSet R Y
  right := PUnit
  hom.app _ := ↾fun _ ↦ .unit

attribute [local simp] SimplicialObject.δ_def SimplexCategory.δ_apply
  SimplicialObject.σ_def SimplexCategory.σ_apply in
@[simps]
noncomputable def extraDegeneracy (y : Y) : (toAugmentedSSet R Y).ExtraDegeneracy where
  s' := ↾fun _ ↦ .const y
  s n := ↾(fun f ↦ StdSimplex.affineMapMk (Fin.cases y (fun i ↦ f.hom (StdSimplex.single i))))
  s₀_comp_δ₁ := by dsimp ;ext _ i; fin_cases i; simp
  s_comp_δ₀ n := by dsimp; ext _ i; simp
  s_comp_δ n i := by
    dsimp
    ext z j
    obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp
  s_comp_σ n i := by
    dsimp
    ext z j
    obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp

end ConvexSpace

end Convexity
