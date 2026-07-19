/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Cochains of a simplicial set with coefficients in an abelian group

-/

universe u

@[expose] public section

open CategoryTheory Simplicial Limits

-- Also done by Andrew Yang
namespace AddCommGrpCat

variable (M : Type u) [AddCommGroup M] (ι : Type u)

noncomputable abbrev finsuppCofan :
    Cofan (fun (_ : ι) ↦ of M) :=
  Cofan.mk (of (ι →₀ M)) (fun i ↦ ofHom (Finsupp.singleAddHom i))

set_option backward.defeqAttrib.useBackward true in
noncomputable def isColimitFinsuppCofan :
    IsColimit (finsuppCofan M ι) :=
  Cofan.IsColimit.mk _
    (fun s ↦ ofHom (Y := s.pt)
      (Finsupp.liftAddHom (fun i ↦ (s.inj i).hom)))
    (by cat_disch)
    (fun s f hf ↦ by
      ext : 1
      exact Finsupp.addHom_ext (fun i m ↦ by simp [← hf]))

variable {M ι} in
noncomputable def sigmaConstAddEquiv :
    (sigmaConst.obj (AddCommGrpCat.of M)).obj ι ≃+ (ι →₀ M) :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitFinsuppCofan M ι)).addCommGroupIsoToAddEquiv

end AddCommGrpCat

namespace SSet

variable (X : SSet.{u}) (M : Type u) [AddCommGroup M] (n : ℕ)

noncomputable def chainComplexAddEquiv :
    (X.chainComplex (AddCommGrpCat.of M)).X n ≃+ (X _⦋n⦌ →₀ M) :=
  AddCommGrpCat.sigmaConstAddEquiv

end SSet
