/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Excision.SingularHomology.Basic


/-!
# Constructor for natural transformations on singular chains

-/

@[expose] public section

universe w v u

open CategoryTheory Limits Simplicial

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  [Preadditive C]

namespace singularChainComplexFunctor

variable {R : C} {n : ℕ} {F : TopCat.{w} ⥤ C}

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Constructor for natural transformations from the functor of `n`-singular chains. -/
noncomputable def natTransMk (f : R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌)) :
    (singularChainComplexFunctor C).obj R ⋙ HomologicalComplex.eval _ _ n ⟶ F where
  app X := Sigma.desc (fun s ↦ f ≫ F.map s.down)
  naturality {X Y} g := Sigma.hom_ext _ _ (fun s ↦ by
    simp [singularChainComplexFunctor, SSet.chainComplexFunctor, ← Functor.map_comp]
    rfl)

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma ι_natTransMk (f : R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌))
    (X : TopCat.{w}) (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    dsimp% X.ιSingularChainComplexX s ≫ (natTransMk f).app X =
      f ≫ F.map s.down :=
  Sigma.ι_desc ..

set_option backward.isDefEq.respectTransparency false in
lemma natTrans_ext
    {f g : (singularChainComplexFunctor C).obj R ⋙ HomologicalComplex.eval _ _ n ⟶ F}
    (h : TopCat.ιSingularChainComplexX _ (TopCat.toSSet.univObj n) ≫ f.app _ =
      TopCat.ιSingularChainComplexX _ (TopCat.toSSet.univObj n) ≫ g.app _) :
    f = g := by
  ext X
  refine Sigma.hom_ext _ _ (fun s ↦ ?_)
  simpa [Category.assoc, ← NatTrans.naturality] using! h =≫ F.map s.down

end singularChainComplexFunctor

end AlgebraicTopology
