/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Excision.SimplicialSet.RelativeHomology
public import Excision.HomotopyCategory.HomotopyEquivalences

/-!
# ...

-/

universe w

@[expose] public section

open CategoryTheory Limits Simplicial HomologicalComplex

namespace SSet.Subcomplex

variable {X : SSet.{w}} (A : X.Subcomplex)

@[simp] lemma pair_left : A.pair.left = A := rfl
@[simp] lemma pair_right : A.pair.right = X := rfl
@[simp] lemma pair_hom : A.pair.hom = A.ι := rfl

end SSet.Subcomplex

namespace SSetPair

section

variable {X Y : SSet.{w}} (i : X ⟶ Y) [Mono i]

@[simp] lemma of_left : (of i).left = X := rfl
@[simp] lemma of_right : (of i).right = Y := rfl
@[simp] lemma of_hom : (of i).hom = i := rfl

end

section

/-- Constructor for morphisms in `SSetPair`. -/
abbrev homMk {X Y : SSetPair.{w}} (f₁ : X.left ⟶ Y.left) (f₂ : X.right ⟶ Y.right)
    (w : f₁ ≫ Y.hom = X.hom ≫ f₂ := by cat_disch) :
    X ⟶ Y:=
  MorphismProperty.Arrow.homMk f₁ f₂ w

/-- Constructor for isomorphisms in `SSetPair`. -/
abbrev isoMk {X Y : SSetPair.{w}} (e₁ : X.left ≅ Y.left) (e₂ : X.right ≅ Y.right)
    (w : e₁.hom ≫ Y.hom = X.hom ≫ e₂.hom := by cat_disch) :
    X ≅ Y :=
  MorphismProperty.Arrow.isoMk e₁ e₂ w

end

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

section

variable {X : SSet.{w}} (A B : X.Subcomplex)

/-- The morphism from the pair `(B, A ⊓ B)` to `(X, A)` when `A` and `B` are subcomplexes
of `X`. -/
def homOfSubcomplexes :
    of (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) ⟶ A.pair :=
  MorphismProperty.Arrow.homMk (SSet.Subcomplex.homOfLE (by simp)) B.ι (by simp) (by simp) (by simp)

lemma homotopyEquivalences_chainComplexMap_homOfSubcomplexes (R : C) :
    homotopyEquivalences _ _ (chainComplexMap (homOfSubcomplexes A B) R) ↔
      homotopyEquivalences _ _ (SSet.chainComplexMap (A ⊔ B).ι R) := by
  sorry

end

lemma mono_left_of_mono_right {X Y : SSetPair.{w}}
    (f : X ⟶ Y) [Mono f.right] :
    Mono f.left :=
  mono_of_mono_fac f.w

lemma homotopyEquivalence_chainComplexMap_iff_of_mono {X Y : SSetPair.{w}}
    (f : X ⟶ Y) (R : C)
    (Z : Y.right.Subcomplex)
    (h₀ : Z = SSet.Subcomplex.range Y.hom ⊔ SSet.Subcomplex.range f.right)
    (h₁ : Mono f.right) (h₂ : SSet.Subcomplex.range (f.left ≫ Y.hom) =
      SSet.Subcomplex.range Y.hom ⊓ SSet.Subcomplex.range f.right) :
    homotopyEquivalences _ _ (chainComplexMap f R) ↔
      homotopyEquivalences _ _ (SSet.chainComplexMap Z.ι R) := by
  subst h₀
  rw [← homotopyEquivalences_chainComplexMap_homOfSubcomplexes]
  have := mono_left_of_mono_right f
  suffices Arrow.mk f ≅ Arrow.mk (homOfSubcomplexes (SSet.Subcomplex.range Y.hom)
      (SSet.Subcomplex.range f.right)) from
    MorphismProperty.arrow_mk_iso_iff _
      (((chainComplexFunctor C).obj R).mapArrow.mapIso this)
  refine Arrow.isoMk
    (SSetPair.isoMk
      (asIso (SSet.Subcomplex.toRange (f.left ≫ Y.hom)) ≪≫
      SSet.Subcomplex.eqToIso h₂) (asIso (SSet.Subcomplex.toRange (f.right)) :) ?_)
    (SSetPair.isoMk (asIso (SSet.Subcomplex.toRange Y.hom) :) (Iso.refl _))
  dsimp
  rw [← cancel_mono (SSet.Subcomplex.ι _)]
  simpa using f.w

end SSetPair
