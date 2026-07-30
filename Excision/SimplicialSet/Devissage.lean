/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Excision.SimplicialSet.RelativeHomology

/-!
# ...

-/

universe w

@[expose] public section

open CategoryTheory Limits Simplicial HomologicalComplex

namespace SSetPair

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : SSetPair.{w}}

lemma homotopyEquivalence_chainComplexMap_iff_of_mono
    (f : X ⟶ Y) (R : C)
    (Z : Y.right.Subcomplex)
    (h₀ : Z = SSet.Subcomplex.range Y.hom ⊔ SSet.Subcomplex.range f.right)
    (h₁ : Mono f.right) (h₂ : SSet.Subcomplex.range (f.left ≫ Y.hom) =
      SSet.Subcomplex.range Y.hom ⊓ SSet.Subcomplex.range f.right) :
    homotopyEquivalences _ _ (chainComplexMap f R) ↔
      homotopyEquivalences _ _ (SSet.chainComplexMap Z.ι R) := by
  sorry

end SSetPair
