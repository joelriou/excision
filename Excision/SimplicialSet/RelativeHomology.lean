/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import Excision.Limits.SigmaConst
public import Excision.Preadditive.HasZeroObject

/-!
# ...

-/

universe w

@[expose] public section

open CategoryTheory Limits Simplicial

namespace SSetPair

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

section

/-- The isomorphism of chain complexes that is induced by an isomorphism of
pairs of simplicial sets. -/
noncomputable abbrev chainComplexMapIso {X Y : SSetPair.{w}} (e : X ≅ Y) (R : C) :
    X.chainComplex R ≅ Y.chainComplex R where
  hom := chainComplexMap e.hom R
  inv := chainComplexMap e.inv R

end

section

variable (X : SSetPair.{w})

/-- If `X : SSetPair` and `n : ℕ`, this is the kernel fork with point `(X.left.chainComplex R).X n`
for the map `(X.chainComplexπ R).f n : (X.right.chainComplex R).X n ⟶ (X.chainComplex R).X n`. -/
noncomputable def kernelForkChainComplexX (R : C) (n : ℕ) :
    KernelFork ((X.chainComplexπ R).f n) :=
  KernelFork.ofι _ (X.chainComplex_condition_f R n)

variable (R : C) (n : ℕ)

attribute [local instance] Preadditive.hasZeroObject_of_hasCoproducts in
/-- If `X : SSetPair` and `n : ℕ`, the kernel of the morphism
`(X.chainComplexπ R).f n : (X.right.chainComplex R).X n ⟶ (X.chainComplex R).X n`
identifies to `(X.left.chainComplex R).X n`. -/
@[no_expose]
noncomputable def isLimitKernelForkChainComplexX (R : C) (n : ℕ) :
    IsLimit (X.kernelForkChainComplexX R n) :=
  isLimitKernelForkOfIsColimitCokernelCoforkSigmaConst _ _ (injective_of_mono _)
    (X.isColimitCokernelCoforkChainComplexX R n)

/-- If `X : SSetPair`, this is the kernel fork with point `X.left.chainComplex R`
for the map `X.chainComplexπ R : X.right.chainComplex R ⟶ X.chainComplex R`. -/
noncomputable def kernelForkChainComplex (R : C) :
    KernelFork (X.chainComplexπ R) :=
  KernelFork.ofι _ (X.chainComplex_condition R)

/-- If `X : SSetPair`, the kernel of `X.chainComplexπ R : X.right.chainComplex R ⟶ X.chainComplex R`
identifies to `X.left.chainComplex R`. -/
@[no_expose]
noncomputable def isLimitKernelForkChainComplex (R : C) :
    IsLimit (X.kernelForkChainComplex R) :=
  HomologicalComplex.isLimitOfEval _ _
    (fun n ↦ (KernelFork.isLimitMapConeEquiv _ _).2
      (X.isLimitKernelForkChainComplexX R n))

end

@[reassoc (attr := simp)]
lemma ιChainComplex_π_f_eq_zero
    (X : SSetPair.{w}) (R : C) {n : ℕ} (x : X.left _⦋n⦌) :
    dsimp% X.right.ιChainComplex (X.hom.app _ x) ≫ (X.chainComplexπ R).f n = 0 := by
  simpa only [comp_zero, SSet.ι_chainComplexMap_f_assoc] using
    X.left.ιChainComplex x ≫= X.chainComplex_condition_f R n

lemma ιChainComplex_π_f_eq_zero_of_mem_range
    (X : SSetPair.{w}) (R : C) {n : ℕ} (x : X.right _⦋n⦌) (hx : x ∈ Set.range (X.hom.app _)) :
    X.right.ιChainComplex x ≫ (X.chainComplexπ R).f n = 0 := by
  obtain ⟨x, rfl⟩ := hx
  rw [X.ιChainComplex_π_f_eq_zero]

lemma ιChainComplex_π_f_eq_zero_of_subcomplex {X : SSet.{w}} (A : X.Subcomplex) (R : C) {n : ℕ}
    (x : X _⦋n⦌) (hx : x ∈ A.obj _) :
    X.ιChainComplex x ≫ (A.pair.chainComplexπ R).f n = 0 :=
  A.pair.ιChainComplex_π_f_eq_zero_of_mem_range _ _ ⟨⟨x, hx⟩, rfl⟩

end SSetPair
