/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Homotopy

/-!
# Properties of homotopy equivalences

-/

-- #42321

universe w

@[expose] public section

open CategoryTheory HomologicalComplex
variable {ι : Type*} {c : ComplexShape ι} {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex C c}

namespace HomotopyEquiv

lemma homotopyEquivalences_hom (e : HomotopyEquiv K L) :
    homotopyEquivalences _ _ e.hom := ⟨e, rfl⟩

lemma homotopyEquivalences_inv (e : HomotopyEquiv K L) :
    homotopyEquivalences _ _ e.inv := e.symm.homotopyEquivalences_hom

/-- If `e` if a homotopy equivalence and `h` is a homotopy from `e.hom` to
a morphism `f`, then this is a homotopy equivalence whose `hom` field is `f`. -/
@[simps hom inv]
def copy (e : HomotopyEquiv K L) {f : K ⟶ L} (h : Homotopy e.hom f) :
    HomotopyEquiv K L where
  hom := f
  inv := e.inv
  homotopyHomInvId := (h.symm.compRight _).trans e.homotopyHomInvId
  homotopyInvHomId := (h.symm.compLeft _).trans e.homotopyInvHomId

end HomotopyEquiv

namespace HomologicalComplex

lemma homotopyEquivalences.of_isIso (f : K ⟶ L) [IsIso f] : homotopyEquivalences _ _ f :=
  ⟨.ofIso (asIso f), rfl⟩

lemma homotopyEquivalences.of_homotopy {f g : K ⟶ L} (h : homotopyEquivalences _ _ f)
    (hfg : Homotopy f g) :
    homotopyEquivalences _ _ g := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e.copy hfg, by simp⟩

instance : (homotopyEquivalences C c).IsMultiplicative where
  id_mem K := ⟨.refl _, rfl⟩
  comp_mem f g := by
    rintro ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f.trans g, rfl⟩

instance : (homotopyEquivalences C c).HasTwoOutOfThreeProperty where
  of_postcomp f _ := by
    rintro ⟨g, rfl⟩ ⟨e, he⟩
    refine (e.trans g.symm).homotopyEquivalences_hom.of_homotopy ?_
    dsimp [HomotopyEquiv.trans, HomotopyEquiv.symm]
    rw [he, Category.assoc]
    exact g.homotopyHomInvId.compLeftId f
  of_precomp _ g := by
    rintro ⟨f, rfl⟩ ⟨e, he⟩
    refine (f.symm.trans e).homotopyEquivalences_hom.of_homotopy ?_
    dsimp [HomotopyEquiv.trans, HomotopyEquiv.symm]
    rw [he, ← Category.assoc]
    exact f.homotopyInvHomId.compRightId g

instance : (homotopyEquivalences C c).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ _ _ ↦ .of_isIso _)

end HomologicalComplex
