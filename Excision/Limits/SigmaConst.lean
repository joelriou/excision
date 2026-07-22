/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# ...

-/

universe v u

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] [HasCoproducts.{max u v} C]

/-- The isomorphism `(sigmaConst.obj X).obj (ULift.{v} T) ≅ (sigmaConst.obj X).obj T`
when `T : Type u`. -/
@[no_expose]
noncomputable def sigmaConstObjObjULiftIso (X : C) (T : Type u) :
    haveI : HasCoproducts.{u} C := hasCoproducts_shrink
    (sigmaConst.obj X).obj (ULift.{v} T) ≅ (sigmaConst.obj X).obj T :=
  haveI : HasCoproducts.{u} C := hasCoproducts_shrink
  Sigma.reindex Equiv.ulift.{v, u} (fun (_ : T) ↦ X)

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma ι_sigmaConstObjObjULiftIso_hom (X : C) {T : Type u} (t : ULift.{v} T) :
    haveI : HasCoproducts.{u} C := hasCoproducts_shrink
    dsimp% Sigma.ι _ t ≫ (sigmaConstObjObjULiftIso.{v} X T).hom =
      Sigma.ι (fun _ ↦ X) t.down := by
  haveI : HasCoproducts.{u} C := hasCoproducts_shrink
  exact Sigma.ι_reindex_hom Equiv.ulift.{v, u} (fun (_ : T) ↦ X) t

set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism `(sigmaConst.obj X).obj (ULift.{v} T) ≅ (sigmaConst.obj X).obj T`
for `X : C` and `T : Type u`, as an isomorphism of functors `C ⥤ Type u ⥤ C`. -/
@[simps!]
noncomputable def sigmaConstULiftIso :
  haveI : HasCoproducts.{u} C := hasCoproducts_shrink
  sigmaConst.{max u v} ⋙
    (Functor.whiskeringLeft _ _ C).obj uliftFunctor.{v, u} ≅
  sigmaConst.{u} :=
  haveI : HasCoproducts.{u} C := hasCoproducts_shrink
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents (sigmaConstObjObjULiftIso _))

end CategoryTheory
