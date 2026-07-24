/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Excision.Limits.SigmaConst

/-!
# ...

-/

universe w

@[expose] public section

open CategoryTheory Limits

namespace SSet

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

set_option backward.defeqAttrib.useBackward true in
instance {X Y : SSet.{w}} (f : X ⟶ Y) [Mono f] (R : C) (n : ℕ) :
    Mono ((chainComplexMap f R).f n) := by
  dsimp [chainComplexMap, chainComplexFunctor, -sigmaConst_obj_map]
  infer_instance

instance {X Y : SSet.{w}} (f : X ⟶ Y) [Mono f] (R : C) :
    Mono (chainComplexMap f R) :=
  HomologicalComplex.mono_of_mono_f _ inferInstance

end SSet
