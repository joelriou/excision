/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# ...

-/

universe w

@[expose] public section

open CategoryTheory Limits

namespace SSet

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

instance {X Y : SSet.{w}} (f : X ⟶ Y) [Mono f] (R : C) :
    Mono (chainComplexMap f R) := sorry

end SSet
