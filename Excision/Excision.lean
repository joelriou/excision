/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Excision.SmallSimplices

/-!
# Excision theorem

-/

universe w

@[expose] public section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Opposite

namespace TopCat

variable {X : TopCat.{w}} {ι : Type*} {A B : Set X}

variable (A B) in
/-- Given two subsets `A` and `B` of a topological space `X`, this is
the condition that the interiors of `A` and `B` cover `X`. -/
structure ExcisionCondition : Prop where
  union_interior : interior A ∪ interior B = Set.univ

variable (h : ExcisionCondition A B)

namespace ExcisionCondition

include h in
lemma smallSimplicesCondition : SmallSimplicesCondition (Bool.rec A B) where
  iUnion_interior := by rw [← h.union_interior]; aesop

end ExcisionCondition

end TopCat
