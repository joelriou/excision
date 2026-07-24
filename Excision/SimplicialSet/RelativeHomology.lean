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

noncomputable def kernelForkChainComplexX (R : C) (n : ℕ) :
    KernelFork ((X.chainComplexπ R).f n) :=
  KernelFork.ofι _ (X.chainComplex_condition_f R n)

def isLimitKernelForkChainComplexX (R : C) (n : ℕ) :
    IsLimit (X.kernelForkChainComplexX R n) := by
  sorry

noncomputable def kernelForkChainComplex (R : C) :
    KernelFork (X.chainComplexπ R) :=
  KernelFork.ofι _ (X.chainComplex_condition R)

noncomputable def isLimitKernelForkChainComplex (R : C) :
    IsLimit (X.kernelForkChainComplex R) :=
  HomologicalComplex.isLimitOfEval _ _
    (fun n ↦ (KernelFork.isLimitMapConeEquiv _ _).2
      (X.isLimitKernelForkChainComplexX R n))

end SSetPair
