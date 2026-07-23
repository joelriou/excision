/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Excision.ConvexSpace.AffineChains
public import Excision.ConvexSpace.Top
public import Excision.SingularHomology.NatTrans
public import Excision.SingularHomology.ULift

/-!
# The subdivision endomorphism of the singular chain complex

-/

universe w

@[expose] public section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Convexity Simplicial

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
      (SSet.chainComplexMap (StdSimplex.toSSetNatTrans _) R).f (n + 1) ≫
        (TopCat.singularChainComplexULiftIso.{w} _ R).inv.f (n + 1))

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

namespace toSSet

variable {X}

/-- The subdivisions of a singular `n`-simplex of a topological space. It takes
a permutation of `Fin (n + 1)` as an input. -/
noncomputable def sd {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) (σ : Equiv.Perm (Fin (n + 1))) :
    (toSSet.obj X) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm
    ((TopCat.toSSetObjEquiv _ _ s).comp
      ((ConvexSpace.AffineMap.id (StdSimplex ℝ (Fin (n + 1)))).sd σ).toContinuousMap)

/-- The `k`-iterated subdivisions of a singular `n`-simplex of a topological space.
It takes a family of `k` permutations of `Fin (n + 1)` as an input. -/
@[no_expose]
noncomputable def sdIter
    {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) {k : ℕ} (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    (toSSet.obj X) _⦋n⦌ := by
  induction k generalizing s with
  | zero => exact s
  | succ k hk => exact sd (hk s (σ ∘ Fin.succ)) (σ 0)

@[simp]
lemma sdIter_zero
    {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) (σ : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    sdIter s σ = s := by
  rfl

lemma sdIter_succ
    {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) {k : ℕ} (σ : Fin (k + 1) → Equiv.Perm (Fin (n + 1))) :
    sdIter s σ = sd (sdIter s (σ ∘ Fin.succ)) (σ 0) := by
  rfl

@[simp]
lemma sdIter_one
    {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) (σ : Fin 1 → Equiv.Perm (Fin (n + 1))) :
    sdIter s σ = sd s (σ 0) := by
  rfl

end toSSet

/-- The `k`th iteration of the subdivision operator `TopCat.singularChainComplexSd`. -/
@[no_expose]
noncomputable def singularChainComplexSdIter (k : ℕ) :
    X.singularChainComplex R ⟶ X.singularChainComplex R :=
  letI x : End _ := singularChainComplexSd (R := R) X
  x ^ k

@[simp]
lemma singularChainComplexSdIter_zero :
    singularChainComplexSdIter (R := R) X 0 = 𝟙 _ := by
  simp [singularChainComplexSdIter]

@[simp high]
lemma singularChainComplexSdIter_one :
    singularChainComplexSdIter (R := R) X 1 = singularChainComplexSd X := by
  simp [singularChainComplexSdIter]

@[simp]
lemma singularChainComplexSdIter_add (k l : ℕ) :
    singularChainComplexSdIter (R := R) X (k + l) =
      singularChainComplexSdIter X k ≫ singularChainComplexSdIter X l := by
  simp [add_comm k l, singularChainComplexSdIter, pow_add]

@[simp]
lemma singularChainComplexSdIter_succ (k : ℕ) :
    singularChainComplexSdIter (R := R) X (k + 1) =
      singularChainComplexSdIter X k ≫ singularChainComplexSd X := by
  simp [singularChainComplexSdIter_add]

@[reassoc]
lemma ι_singularChainComplexSd_f {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) :
    ιSingularChainComplex _ s ≫ (singularChainComplexSd X (R := R)).f n =
      ∑ (σ : Equiv.Perm (Fin (n + 1))),
        σ.sign • ιSingularChainComplex _ (toSSet.sd s σ) := by
  sorry

@[reassoc]
lemma ι_singularChainComplexSdIter_f {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) (k : ℕ) :
    ιSingularChainComplex _ s ≫ (singularChainComplexSdIter X (R := R) k).f n =
      ∑ (σ : Fin k → Equiv.Perm (Fin (n + 1))),
        (∏ (i : Fin k), (σ i).sign) •
          ιSingularChainComplex _ (toSSet.sdIter s σ) := by
  induction k with
  | zero => simp
  | succ k hk =>
    let α : (Fin (k + 1) → Equiv.Perm (Fin (n + 1))) ≃
        (Fin k → Equiv.Perm (Fin (n + 1))) × Equiv.Perm (Fin (n + 1)) :=
      { toFun σ := ⟨σ ∘ Fin.succ, σ 0⟩
        invFun := fun ⟨σ, σ'⟩ ↦ Fin.cases σ' σ
        left_inv σ := by
          ext l : 1
          obtain rfl | ⟨l, rfl⟩ := l.eq_zero_or_eq_succ <;> rfl }
    simp only [singularChainComplexSdIter_succ, HomologicalComplex.comp_f, reassoc_of% hk,
      Preadditive.sum_comp, Linear.units_smul_comp, ι_singularChainComplexSd_f,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_bijective
      (g := fun ⟨σ, σ₀⟩ ↦ ((∏ i, Equiv.Perm.sign (σ i)) * Equiv.Perm.sign σ₀) •
        ιSingularChainComplex _ (toSSet.sd (toSSet.sdIter s σ) σ₀))
        (t := .univ) _ α.bijective (by simp) ?_,
      Finset.sum_finset_product .univ .univ (fun _ ↦ .univ) (by simp)]
    simp only [Finset.mem_univ, forall_const]
    intro σ
    congr
    rw [mul_comm]
    simp [α, Fin.prod_univ_succ]
    rfl

end TopCat
