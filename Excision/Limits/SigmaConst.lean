/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# ...

-/

universe v u

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C]

section

variable [HasCoproducts.{max u v} C]

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

set_option backward.isDefEq.respectTransparency false in
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

end

open Classical in
set_option backward.defeqAttrib.useBackward true in
instance [HasCoproducts.{u} C] {T₁ T₂ : Type u} (f : T₁ ⟶ T₂) [Mono f] [Preadditive C] (X : C) :
    IsSplitMono ((sigmaConst.obj X).map f) := by
  have (t₂ : T₂) (ht₂ : t₂ ∈ Set.range f) : ∃ t₁, f t₁ = t₂ := ht₂
  choose t₁ ht₁ using this
  have (t : T₁) : t₁ (f t) (by simp) = t := injective_of_mono f (ht₁ _ _)
  exact ⟨⟨{
    retraction :=
      Sigma.desc (fun t₂ ↦
        if ht₂ : t₂ ∈ Set.range f then Sigma.ι (fun _ ↦ X) (t₁ t₂ ht₂) else 0)
  }⟩⟩

end CategoryTheory
