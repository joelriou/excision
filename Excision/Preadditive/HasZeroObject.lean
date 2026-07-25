/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# ...

-/

@[expose] public section

open CategoryTheory Limits

lemma CategoryTheory.Preadditive.hasZeroObject_of_hasCoproducts (C : Type*) [Category* C]
    [Preadditive C]
    [HasCoproduct (PEmpty.elim : PEmpty.{w + 1} → C)] :
    HasZeroObject C :=
  ⟨∐ (PEmpty.elim : PEmpty.{w + 1} → C), by
    rw [IsZero.iff_id_eq_zero]
    cat_disch⟩
