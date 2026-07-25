/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import Excision.Limits.SigmaConst
public import Excision.Preadditive.HasZeroObject

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

attribute [local instance] Preadditive.hasZeroObject_of_hasCoproducts in
@[no_expose]
noncomputable def isLimitKernelForkChainComplexX (R : C) (n : ℕ) :
    IsLimit (X.kernelForkChainComplexX R n) :=
  isLimitKernelForkOfIsColimitCokernelCoforkSigmaConst _ _ (injective_of_mono _)
    (X.isColimitCokernelCoforkChainComplexX R n)

noncomputable def kernelForkChainComplex (R : C) :
    KernelFork (X.chainComplexπ R) :=
  KernelFork.ofι _ (X.chainComplex_condition R)

@[no_expose]
noncomputable def isLimitKernelForkChainComplex (R : C) :
    IsLimit (X.kernelForkChainComplex R) :=
  HomologicalComplex.isLimitOfEval _ _
    (fun n ↦ (KernelFork.isLimitMapConeEquiv _ _).2
      (X.isLimitKernelForkChainComplexX R n))

end SSetPair
