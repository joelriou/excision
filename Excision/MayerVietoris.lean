/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Excision.SmallSimplices

/-!
# Mayer-Vietoris (WIP)

-/

universe w

@[expose] public section

open CategoryTheory Limits TopologicalSpace

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

namespace TopCat

variable {X : Type w} [TopologicalSpace X] {UV U V W : Opens X} (sq : Lattice.BicartSq UV U V W)

namespace toSSet

include sq in
lemma bicartSq : Lattice.BicartSq (subcomplexOfSet (X := .of X) UV)
    (subcomplexOfSet U) (subcomplexOfSet V)
    (subcomplexOfSet U ⊔ subcomplexOfSet V) where
  sup_eq := rfl
  inf_eq := by
    ext
    simp only [Subfunctor.min_obj, Set.mem_inter_iff, mem_subcomplexOfSet_iff.{w},
      ← sq.inf_eq, Opens.coe_inf, Set.subset_inter_iff]

end toSSet

end TopCat
