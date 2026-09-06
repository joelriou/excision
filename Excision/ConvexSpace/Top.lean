/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology
public import Excision.ConvexSpace.ToSSet

/-!
# ...

-/

@[expose] public section

open CategoryTheory Convexity Opposite Simplicial

lemma TopCat.toSSet_map_app_toSSetObjEquiv_symm
    {Y Z : TopCat.{w}} (f : Y ⟶ Z) {n : ℕ}
    (x : C(StdSimplex ℝ (Fin (n + 1)), Y)) :
    (toSSet.map f).app (op ⦋n⦌) ((toSSetObjEquiv _ _).symm x) =
    (toSSetObjEquiv _ _).symm (f.hom.comp x) := rfl

/-namespace stdSimplex

@[fun_prop]
lemma continuous_apply {ι : Type*} [Fintype ι] (i : ι) :
    Continuous (fun (s : stdSimplex ℝ ι) ↦ s i) :=
  (_root_.continuous_apply i).comp continuous_subtype_val

lemma total {ι : Type*} [Fintype ι] (s : stdSimplex ℝ ι) :
    ∑ (i : ι), s i = 1 := s.2.2

lemma apply_nonneg {ι : Type*} [Fintype ι] (x : stdSimplex ℝ ι) (i : ι) :
    0 ≤ x i :=
  x.2.1 i

@[simp]
lemma map_id {ι : Type*} [Fintype ι] :
    stdSimplex.map (S := ℝ) (id : ι → ι) = id := by
  aesop

end stdSimplex-/

namespace Convexity

/-- The inclusion of `StdSimplex ℝ α` to `α → ℝ`, as an affine map. -/
@[simps]
def StdSimplex.ι {α : Type*} :
    ConvexSpace.AffineMap ℝ (StdSimplex ℝ α) (α → ℝ) where
  toFun s := s.weights
  isAffineMap_toFun.map_sConvexComb s := by
    ext i
    induction s using StdSimplex.rec' with
    | sum n w m hw₀ hw =>
      dsimp
      simp only [weights_sConvexComb, Finsupp.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
        smul_eq_mul, iConvexComb_eq_sum, weights_map, Finsupp.mapDomain_finsetSum,
        Finsupp.mapDomain_single]
      rw [Finsupp.sum_finsetSum _ _ _ (by simp) (by simp [add_mul]),
        Finsupp.sum_finsetSum _ _ _ (by simp) (by simp [add_mul])]
      congr
      simp

@[fun_prop]
lemma StdSimplex.continuous_of_affineMap' {ι₁ ι₂ : Type*} [Finite ι₂]
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ ι₁) (StdSimplex ℝ ι₂)) :
    Continuous s := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ ι₂).continuous_iff]
  change Continuous (StdSimplex.ι.comp s)
  fun_prop

/-- The continuous map in `C(stdSimplex ℝ ι₁, stdSimplex ℝ ι₂)` that is given
by an affine map from `StdSimplex ℝ ι₁` to `StdSimplex ℝ ι₂`. -/
noncomputable def ConvexSpace.AffineMap.toContinuousMap
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ ι₁) (StdSimplex ℝ ι₂)) :
    C(StdSimplex ℝ ι₁, StdSimplex ℝ ι₂) where
  toFun := s


lemma ConvexSpace.AffineMap.toContinuousMap_comp
    {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ ι₂) (StdSimplex ℝ ι₃))
    (t : ConvexSpace.AffineMap ℝ (StdSimplex ℝ ι₁) (StdSimplex ℝ ι₂)) :
    (s.comp t).toContinuousMap = s.toContinuousMap.comp t.toContinuousMap := by
  ext
  simp [toContinuousMap]

@[simp]
lemma ConvexSpace.AffineMap.toContinuousMap_id
    (ι : Type*) [Fintype ι] :
    (ConvexSpace.AffineMap.id (StdSimplex ℝ ι)).toContinuousMap = .id _ := rfl

/-- The inclusion of affine maps into continuous maps between standard simplices,
as a morphism of simplicial sets. -/
noncomputable def StdSimplex.toSSetNatTrans (ι : Type*) [Fintype ι] :
    ConvexSpace.toSSet ℝ (StdSimplex ℝ ι) ⟶
      TopCat.toSSet.obj (.of (StdSimplex ℝ ι)) where
  app _ := ↾((TopCat.toSSetObjEquiv _ _).symm ∘ ConvexSpace.AffineMap.toContinuousMap)

@[simp]
lemma StdSimplex.toSSetNatTrans_app_apply {n : ℕ} {ι : Type*} [Fintype ι]
    (x : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) (StdSimplex ℝ ι)) :
    (StdSimplex.toSSetNatTrans ι).app (op ⦋n⦌) x =
      (TopCat.toSSetObjEquiv _ _).symm x.toContinuousMap := rfl

@[reassoc]
lemma StdSimplex.toSSetNatTrans_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (StdSimplex.affineMap f).toSSetMap ≫ StdSimplex.toSSetNatTrans _ =
    StdSimplex.toSSetNatTrans _ ≫
      TopCat.toSSet.map (SimplexCategory.toTop₀.map f) := rfl

end Convexity

open Convexity

namespace TopCat

lemma δ_toSSetObjEquiv_symm {X : TopCat} {n : ℕ}
    (x : C(StdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    (toSSet.obj X).δ i ((toSSetObjEquiv _ _).symm x) =
    (toSSetObjEquiv _ _).symm (x.comp
      (Convexity.StdSimplex.affineMap i.succAbove).toContinuousMap) :=
  rfl

end TopCat
