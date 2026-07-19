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

variable {M : Type u} [AddCommGroup M] {ι : Type u}

variable (M ι) in
/-- The (colimit) cofan in the category `AddCommGrpCat` with
point `ι →₀ M` for the constant family `fun i ↦ of M`. -/
noncomputable abbrev finsuppCofan :
    Cofan (fun (_ : ι) ↦ of M) :=
  Cofan.mk (of (ι →₀ M)) (fun i ↦ ofHom (Finsupp.singleAddHom i))

variable (M ι) in
set_option backward.defeqAttrib.useBackward true in
/-- In the category `AddCommGrpCat`, the coproduct of the constant
family `fun (i : ι) ↦ of M` is `ι →₀ M`. -/
noncomputable def isColimitFinsuppCofan :
    IsColimit (finsuppCofan M ι) :=
  Cofan.IsColimit.mk _
    (fun s ↦ ofHom (Y := s.pt)
      (Finsupp.liftAddHom (fun i ↦ (s.inj i).hom)))
    (by cat_disch)
    (fun s f hf ↦ by
      ext : 1
      exact Finsupp.addHom_ext (fun i m ↦ by simp [← hf]))

/-- Given an abelian group `M` and a type `ι`, this is the additive
equivalence betwen `(sigmaConst.obj (AddCommGrpCat.of M)).obj ι`
and `ι →₀ M`. -/
noncomputable def sigmaConstAddEquiv :
    (sigmaConst.obj (AddCommGrpCat.of M)).obj ι ≃+ (ι →₀ M) :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitFinsuppCofan M ι)).addCommGroupIsoToAddEquiv

@[simp]
lemma sigmaConstAddEquiv_apply (i : ι) (m : M) :
    sigmaConstAddEquiv (Sigma.ι (f := fun (_ : ι) ↦ of M) i m) =
      Finsupp.single i m :=
  ConcreteCategory.congr_hom
    (IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
      (isColimitFinsuppCofan M ι) ⟨i⟩) _

@[simp]
lemma sigmaConstAddEquiv_symm_apply (i : ι) (m : M) :
    sigmaConstAddEquiv.symm (Finsupp.single i m) =
      Sigma.ι (f := fun (_ : ι) ↦ of M) i m :=
  ConcreteCategory.congr_hom
    (IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit _)
      (isColimitFinsuppCofan M ι) ⟨i⟩) _

end AddCommGrpCat

namespace SSet

variable (X : SSet.{u}) (M : Type u) [AddCommGroup M] (n : ℕ)

/-- `n`-cochains of a simplicial set `X` with values in an abelian group `M`
identify with `X _⦋n⦌ →₀ M`. -/
noncomputable def chainComplexAddEquiv :
    (X.chainComplex (AddCommGrpCat.of M)).X n ≃+ (X _⦋n⦌ →₀ M) :=
  AddCommGrpCat.sigmaConstAddEquiv

end SSet
