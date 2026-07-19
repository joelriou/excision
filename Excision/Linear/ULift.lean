/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Cochains of a simplicial set with coefficients in an abelian group

-/

universe v u

@[expose] public section

namespace CategoryTheory.Linear

variable {R : Type u} [Semiring R] {C : Type*} [Category* C]
  [Preadditive C] [Linear R C]

instance ulift : Linear (ULift.{v} R) C where
  homModule _ _ := Module.compHom _ ULift.ringEquiv.toRingHom
  smul_comp := fun _ _ _ ⟨r⟩ f g ↦ Linear.smul_comp _ _ _ r f g
  comp_smul := fun _ _ _ f ⟨r⟩ g ↦ Linear.comp_smul _ _ _ f r g

@[simp]
lemma uliftUp_smul {X Y : C} (r : R) (f : X ⟶ Y) :
    ULift.up.{v} r • f = r • f := rfl

end CategoryTheory.Linear
