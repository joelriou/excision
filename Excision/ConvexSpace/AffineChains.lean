/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Excision.ConvexSpace.ToSSet
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# ...

-/

@[expose] public section

open CategoryTheory Limits

namespace Convexity

variable {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{w} C]
  (Y : Type w) [ConvexSpace ℝ Y] (R : C)

namespace ConvexSpace.toSSet

noncomputable def hSd : ∀ (n : ℕ),
    ((ConvexSpace.toSSet ℝ Y).chainComplex R).X n ⟶
      ((ConvexSpace.toSSet ℝ Y).chainComplex R).X (n + 1)
  | Nat.zero => 0
  | Nat.succ n =>
      Sigma.desc (fun s ↦
        (SSet.ιChainComplex _ s -
          SSet.ιChainComplex _ s ≫ ((ConvexSpace.toSSet ℝ Y).chainComplex R).d (n + 1) n ≫ hSd n) ≫
            ConvexSpace.toSSet.cone s.isobarycenter _ (n + 1))

noncomputable def hSd' (i j : ℕ) :
    ((ConvexSpace.toSSet ℝ Y).chainComplex R).X i ⟶ ((ConvexSpace.toSSet ℝ Y).chainComplex R).X j :=
  if hij : i + 1 = j then hSd Y R i ≫ eqToHom (by simp [hij]) else 0

lemma hSd'_eq (n : ℕ) : hSd' Y R n (n + 1) = hSd Y R n := by simp [hSd']

lemma hSd'_zero (i j : ℕ) (hij : i + 1 ≠ j) : hSd' Y R i j = 0 := by grind [hSd']

noncomputable def sd :
    (ConvexSpace.toSSet ℝ Y).chainComplex R ⟶ (ConvexSpace.toSSet ℝ Y).chainComplex R :=
  𝟙 _ - Homotopy.nullHomotopicMap (hSd' Y R)

noncomputable def homotopySdId : Homotopy (𝟙 _) (sd Y R) :=
  Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [sd])) (.nullHomotopy (hSd' Y R) (hSd'_zero Y R)))

end ConvexSpace.toSSet

end Convexity
