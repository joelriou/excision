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

/-- The data that is part of the homotopy between the identity and
the subdivision endomorphism `sd Y R` of the complex of affine
chains with coefficients in `R` in the convex space `Y`.
(We mostly follow the proof in Proposition 2.21 in Hatcher's book.
It seems that this can be zero for `n = 0` though, which is different
from the definition in the book.) -/
noncomputable def hSd : ∀ (n : ℕ),
    ((toSSet ℝ Y).chainComplex R).X n ⟶
      ((toSSet ℝ Y).chainComplex R).X (n + 1)
  | Nat.zero => 0
  | Nat.succ n =>
      Sigma.desc (fun s ↦
        (SSet.ιChainComplex _ s -
          SSet.ιChainComplex _ s ≫ ((toSSet ℝ Y).chainComplex R).d (n + 1) n ≫ hSd n) ≫
            toSSet.cone s.isobarycenter _ (n + 1))

@[inherit_doc hSd]
noncomputable def hSd' (n m : ℕ) :
    ((toSSet ℝ Y).chainComplex R).X n ⟶ ((toSSet ℝ Y).chainComplex R).X m :=
  if h : n + 1 = m then hSd Y R n ≫ eqToHom (by simp [h]) else 0

lemma hSd'_eq (n : ℕ) : hSd' Y R n (n + 1) = hSd Y R n := by simp [hSd']

lemma hSd'_zero (n m : ℕ) (h : n + 1 ≠ m) : hSd' Y R n m = 0 := by grind [hSd']

/-- The subdivision operator on the complex of affine chains with coefficients
in `R` of a convex space `Y`. By definition, it is homotopic to the identity
(see `homotopyIdSd`). -/
noncomputable def sd :
    (toSSet ℝ Y).chainComplex R ⟶ (toSSet ℝ Y).chainComplex R :=
  𝟙 _ - Homotopy.nullHomotopicMap (hSd' Y R)

/-- The homotopy from the identity to the subdivision endomorphism `sd Y R`
of the complex of affine chains with coefficients in `R` in the convex space `Y`. -/
noncomputable def homotopyIdSd : Homotopy (𝟙 _) (sd Y R) :=
  Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [sd])) (.nullHomotopy (hSd' Y R) (hSd'_zero Y R)))

-- TODO: equational lemma for `sd`

end ConvexSpace.toSSet

end Convexity
