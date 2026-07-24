/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative

/-!
# ...

-/

universe w

@[expose] public section

open CategoryTheory Limits

namespace SSetPair

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]
  (X : SSetPair.{w})

noncomputable def kernelForkChainComplex (R : C) :
    KernelFork (X.chainComplexπ R) :=
  KernelFork.ofι _ (X.chainComplex_condition R)

def isLimitKernelForkChainComplex (R : C) :
    IsLimit (X.kernelForkChainComplex R) := sorry

end SSetPair
