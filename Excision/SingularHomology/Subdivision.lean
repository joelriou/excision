/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Excision.ConvexSpace.AffineChains
public import Excision.ConvexSpace.Top
public import Excision.SingularHomology.NatTransOfFinsupp

/-!
# The subdivision endomorphism of the singular chain complex

-/

universe w

@[expose] public section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Convexity

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

namespace AlgebraicTopology

namespace singularChainComplexFunctor

/-- The natural transformations that are part of the homotopy between
the identity of the singular chain complex of a topological space and
the subdivision endomorphism. -/
noncomputable def hSd (R : C) (n : ℕ) :
    (singularChainComplexFunctor.{w} C).obj R ⋙ eval _ _ n ⟶
      (singularChainComplexFunctor C).obj R ⋙ eval _ _ (n + 1) :=
  haveI : HasCoproducts.{0} C := hasCoproducts_shrink
  natTransMk (SSet.ιChainComplex _ (ConvexSpace.AffineMap.id _) ≫
    ConvexSpace.toSSet.hSd (R := R) (Y := StdSimplex ℝ (Fin (n + 1))) n ≫
      (SSet.chainComplexMap (StdSimplex.toSSetNatTrans _) R).f (n + 1) ≫ by
        change ((TopCat.of (stdSimplex ℝ (Fin (n + 1)))).singularChainComplex R).X (n + 1) ⟶
          ((TopCat.of (ULift.{w} (stdSimplex ℝ (Fin (n + 1))))).singularChainComplex R).X (n + 1)
        -- this is a ulift iso for the singular chain complex
        sorry)

@[inherit_doc hSd]
noncomputable def hSd' (R : C) (n m : ℕ) :
    (singularChainComplexFunctor.{w} C).obj R ⋙ eval _ _ n ⟶
      (singularChainComplexFunctor.{w} C).obj R ⋙ eval _ _ m :=
  if h : n + 1 = m then hSd R n ≫ eqToHom (by simp [h]) else 0

@[simp]
lemma hSd'_eq (R : C) (n : ℕ) : hSd'.{w} R n (n + 1) = hSd R n := by simp [hSd']

lemma hSd'_zero (R : C) (n m : ℕ) (h : n + 1 ≠ m) : hSd' R n m = 0 := by grind [hSd']

end singularChainComplexFunctor

set_option backward.isDefEq.respectTransparency false in
open singularChainComplexFunctor in
/-- The subdivision operator on the singular chain complexes of
topological spaces as an endomorphism of the functor
`(singularChainComplexFunctor.{w} C).obj R : TopCat.{w} ⥤ ChainComplex C ℕ`. -/
noncomputable def singularChainComplexFunctorSd (R : C) :
    (singularChainComplexFunctor.{w} C).obj R ⟶
      (singularChainComplexFunctor.{w} C).obj R where
  app X := 𝟙 _ - Homotopy.nullHomotopicMap (fun n m ↦ (hSd' R n m).app X)
  naturality {X Y} f := by
    simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp, Category.id_comp,
      sub_right_inj]
    rw [Homotopy.nullHomotopicMap_comp, Homotopy.comp_nullHomotopicMap]
    congr
    ext n m
    exact (hSd' R n m).naturality f

end AlgebraicTopology

namespace TopCat

variable (X : TopCat.{w}) {R : C}

/-- The subdivision endomorphism of the singular chain complex of a topological space `X`
with coefficients in `R`. -/
noncomputable abbrev singularChainComplexSd :
    X.singularChainComplex R ⟶ X.singularChainComplex R :=
  (singularChainComplexFunctorSd R).app X

open singularChainComplexFunctor in
set_option backward.isDefEq.respectTransparency false in
/-- The homotopy from the identity to the subdivision endomorphism
`X.singularChainComplexSd` of the singular chain complex of a topological
space `X` with coefficients in `R`. -/
noncomputable def singularChainComplexHomotopyIdSd :
    _root_.Homotopy (𝟙 _) (X.singularChainComplexSd (R := R)) :=
  Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [singularChainComplexSd, singularChainComplexFunctorSd]))
      (Homotopy.nullHomotopy (fun n m ↦ (hSd' R n m).app X)
        (fun n m h ↦ by simp [hSd'_zero _ _ _ h])))

end TopCat
