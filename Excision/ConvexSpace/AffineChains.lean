/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Excision.ConvexSpace.ToSSet

/-!
# ...

-/

@[expose] public section

open CategoryTheory Limits

namespace Convexity

variable {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{w} C]
  (Y : Type w) [ConvexSpace ℝ Y] (R : C)

namespace ConvexSpace.toSSet

/-- The data that is part of the homotopy between the identity and
the subdivision endomorphism `sd Y R` of the complex of affine
chains with coefficients in `R` in the convex space `Y`.
(We mostly follow the proof in Proposition 2.21 in Hatcher's book.
It seems that this can be zero for `n = 0` though, which is different
from the definition in the book.) -/
noncomputable def hSd : ∀ (n : ℕ),
    ((toSSet ℝ Y).chainComplex R).X n ⟶
      ((toSSet ℝ Y).chainComplex R).X (n + 1)
  | Nat.zero => 0
  | Nat.succ n =>
      Sigma.desc (fun s ↦
        (SSet.ιChainComplex _ s - SSet.ιChainComplex _ s ≫
          ((toSSet ℝ Y).chainComplex R).d (n + 1) n ≫ hSd n) ≫
            toSSet.cone s.isobarycenter _ (n + 1))

@[simp]
lemma hSd_zero : hSd Y R 0 = 0 := rfl

@[reassoc (attr := simp)]
lemma ι_hSd_succ {n : ℕ}
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 2))) Y) :
    SSet.ιChainComplex _ s ≫ hSd Y R (n + 1) =
      (SSet.ιChainComplex _ s - SSet.ιChainComplex _ s ≫
        ((toSSet ℝ Y).chainComplex R).d (n + 1) n ≫ hSd Y R n) ≫
          toSSet.cone s.isobarycenter _ (n + 1) :=
  Sigma.ι_desc ..

@[inherit_doc hSd]
noncomputable def hSd' (n m : ℕ) :
    ((toSSet ℝ Y).chainComplex R).X n ⟶ ((toSSet ℝ Y).chainComplex R).X m :=
  if h : n + 1 = m then hSd Y R n ≫ eqToHom (by simp [h]) else 0

@[simp]
lemma hSd'_eq (n : ℕ) : hSd' Y R n (n + 1) = hSd Y R n := by simp [hSd']

lemma hSd'_zero (n m : ℕ) (h : n + 1 ≠ m) : hSd' Y R n m = 0 := by grind [hSd']

/-- The subdivision operator on the complex of affine chains with coefficients
in `R` of a convex space `Y`. By definition, it is homotopic to the identity
(see `homotopyIdSd`). -/
noncomputable def sd :
    (toSSet ℝ Y).chainComplex R ⟶ (toSSet ℝ Y).chainComplex R :=
  𝟙 _ - Homotopy.nullHomotopicMap (hSd' Y R)

/-- The homotopy from the identity to the subdivision endomorphism `sd Y R`
of the complex of affine chains with coefficients in `R` in the convex space `Y`. -/
noncomputable def homotopyIdSd : Homotopy (𝟙 _) (sd Y R) :=
  Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [sd])) (.nullHomotopy (hSd' Y R) (hSd'_zero Y R)))

@[simp]
lemma sd_f_0 : (sd Y R).f 0 = 𝟙 _ := by
  simp [sd, Homotopy.nullHomotopicMap_f_of_not_rel_left (ComplexShape.down_mk 1 0 rfl) (by simp)]

lemma sd_f_succ (n : ℕ) :
    (sd Y R).f (n + 1) = 𝟙 _
      - ((toSSet ℝ Y).chainComplex R).d (n + 1) n ≫ hSd Y R n
      - hSd Y R (n + 1) ≫ ((toSSet ℝ Y).chainComplex R).d (n + 2) (n + 1) := by
  simp [sd, Homotopy.nullHomotopicMap_f (ComplexShape.down_mk (n + 2) (n + 1) rfl)
    (ComplexShape.down_mk (n + 1) n rfl), sub_sub]

@[reassoc]
lemma ι_sd_f_succ {n : ℕ} (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 2))) Y) :
    SSet.ιChainComplex _ s ≫ (sd Y R).f (n + 1) =
      SSet.ιChainComplex _ s ≫ ((toSSet ℝ Y).chainComplex R).d (n + 1) n ≫
        (sd Y R).f n ≫ toSSet.cone (R := ℝ) s.isobarycenter R n := by
  obtain _ | n := n
  · -- simp? [sd_f_succ, Fin.sum_univ_succ, toSSet_δ_zero.{w}]
    simp only [Nat.reduceAdd, sd_f_succ, hSd_zero, comp_zero, sub_zero, Preadditive.comp_sub,
      Category.comp_id, ι_hSd_succ_assoc, ι_cone_assoc, SSet.ιChainComplex_d, Int.reduceNeg,
      Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
      toSSet_δ_zero.{w}, one_smul, Fin.val_succ, zero_add, pow_one, Fin.succ_zero_eq_one, neg_smul,
      Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, even_two, Even.neg_pow, one_pow,
      Finset.sum_singleton, Fin.succ_one_eq_two, sub_add_cancel_left, neg_add_rev, neg_neg, sd_f_0,
      Category.id_comp, SSet.ιChainComplex_d_assoc, Finset.sum_neg_distrib, Preadditive.add_comp,
      ι_cone, Preadditive.neg_comp]
    generalize hγ : s.isobarycenter = γ
    obtain ⟨s, rfl⟩ := StdSimplex.affineMapMk_surjective s
    obtain ⟨s₀, s₁, rfl⟩ := Fin.exists_vecCons₂ s
    simp [toSSet_δ_zero_affineMapMk₂.{w}, toSSet_δ_one_affineMapMk₂.{w},
      toSSet_δ_two_affineMapMk₃.{w}, toSSet_δ_one_affineMapMk₃.{w}]
    abel
  · simp [sd_f_succ, ι_hSd_succ_assoc, cone_comp_d_eq_sub]

variable {n : ℕ}

@[reassoc]
lemma ι_sd_f_eq_sum {n : ℕ} (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) Y) :
    SSet.ιChainComplex _ s ≫ (sd Y R).f n =
      ∑ (σ : Equiv.Perm (Fin (n + 1))),
        σ.sign • (SSet.ιChainComplex _ (ConvexSpace.AffineMap.sd s σ)) := by
  induction n with
  | zero => simp
  | succ => sorry

end ConvexSpace.toSSet

end Convexity
