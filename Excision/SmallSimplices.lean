/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.Order.CompletePartialOrder

/-!
# Small simplices lemma

-/

universe w

@[expose] public section

open CategoryTheory Limits HomologicalComplex

namespace TopCat

variable {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)

/-- Let `U : ι → Set X` be a family of subsets of a topological space `X : TopCat`.
This is the subcomplex of the singular simplicial set `toSSet.obj X` of `X`
consisting of simplices that are contained in some `U i`. -/
noncomputable def toSSet.subcomplexOfSets : (toSSet.obj X).Subcomplex :=
  ⨆ (i : ι), SSet.Subcomplex.range (toSSet.map (ofHom (X := U i) ⟨Subtype.val, by fun_prop⟩))

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

lemma toSSet.homotopyEquivalences_chainComplexMap_subComplexOfSets_ι
    (hU : ⋃ (i : ι), interior (U i) = Set.univ) (R : C) :
    homotopyEquivalences _ _
      (SSet.chainComplexMap (TopCat.toSSet.subcomplexOfSets U).ι R) := by
  sorry

end TopCat
