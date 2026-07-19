/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic


/-!
# Constructor for natural transformations on singular chains

-/

@[expose] public section

universe w v u

open AlgebraicTopology CategoryTheory Limits Simplicial

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The singular chain complex of a topological space with coefficients in `R`. -/
noncomputable abbrev singularChainComplex (X : TopCat.{w}) (R : C) :
    ChainComplex C ℕ :=
  ((singularChainComplexFunctor C).obj R).obj X

/-- Inclusion of a summand of an object in the singular chain complex of
a topological space. -/
noncomputable abbrev ιSingularChainComplexX
    (X : TopCat.{w}) {R : C} {n : ℕ} (x : (toSSet.obj X) _⦋n⦌) :
    R ⟶ (X.singularChainComplex R).X n :=
  Sigma.ι (fun _ ↦ R) x
variable (n : ℕ)

/-- The universal element in `(toSSet.obj (SimplexCategory.toTop ^⦋n⦌)) _⦋n⦌`. -/
noncomputable def toSSet.univObj (n : ℕ) :
    (toSSet.obj (SimplexCategory.toTop ^⦋n⦌)) _⦋n⦌ := ⟨𝟙 _⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ιSingularChainComplex_map
    {X Y : TopCat.{w}} (f : X ⟶ Y) {R : C} {n : ℕ} (x : (toSSet.obj X) _⦋n⦌) :
    X.ιSingularChainComplexX (R := R) x ≫
      (((singularChainComplexFunctor C).obj R).map f).f n =
        Y.ιSingularChainComplexX ((toSSet.map f).app _ x) := by
  simp [singularChainComplexFunctor, ιSingularChainComplexX,
    SSet.chainComplexFunctor]

end TopCat
