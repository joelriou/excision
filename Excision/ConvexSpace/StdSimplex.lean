/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Excision.ConvexSpace.AffineMap
public import Excision.Fin.Vec

/-!
# API for the standard simplex

-/

@[expose] public section

namespace Convexity

namespace StdSimplex

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

instance {M : Type*} [IsEmpty M] : IsEmpty (StdSimplex R M) where
  false x := by
    have hx : x.weights = 0 := by ext m; exfalso; exact IsEmpty.false m
    simpa [hx] using x.total

lemma eq_single_of_subsingleton
    {M : Type*} [Subsingleton M] (x : StdSimplex R M) (m : M) :
    x = .single m := by
  ext i
  obtain rfl := Subsingleton.elim m i
  simp only [weights_single, Finsupp.single_eq_same, ← x.total]
  rw [Finsupp.sum_eq_single _ ?_ (by simp)]
  intro i
  obtain rfl := Subsingleton.elim m i
  simp

instance {M : Type*} [Subsingleton M] :
    Subsingleton (StdSimplex R M) where
  allEq x y := by
    by_cases h : IsEmpty M
    · exfalso
      exact IsEmpty.false x
    · simp only [not_isEmpty_iff] at h
      simp [eq_single_of_subsingleton _ (Classical.arbitrary _)]

@[simp]
lemma iConvexComb_single {M : Type*} (x : StdSimplex R M) :
    x.iConvexComb single = x := by
  aesop

@[ext]
lemma affineMap_ext {M : Type*} {Y : Type*} [ConvexSpace R Y]
    {f g : ConvexSpace.AffineMap R (StdSimplex R M) Y}
    (h : ∀ (i : M), f (.single i) = g (.single i)) : f = g := by
  ext x
  conv_lhs => rw [← iConvexComb_single x]
  conv_rhs => rw [← iConvexComb_single x]
  rw [f.isAffineMap.map_iConvexComb, g.isAffineMap.map_iConvexComb]
  aesop

/-- The (bundled) affine map `StdSimplex R M → StdSimplex R N` induced
by a map `f : M → N`. -/
@[simps, implicit_reducible]
noncomputable def affineMap {M N : Type*} (f : M → N) :
    ConvexSpace.AffineMap R (StdSimplex R M) (StdSimplex R N) where
  toFun := map f

@[simp]
lemma sConvexComb_map_iConvexComb {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y)
    (s : StdSimplex R (StdSimplex R M)) :
    sConvexComb (map (fun s ↦ iConvexComb s f) s) = iConvexComb (sConvexComb s) f :=
  calc
    _ = iConvexComb s fun s ↦ sConvexComb (map f s) := sConvexComb_map _ _
    _ = sConvexComb (map f (sConvexComb s)) := by
        rw [StdSimplex.map_sConvexComb, sConvexComb_sConvexComb, sConvexComb_map,
          iConvexComb_map]

/-- Constructor for (bundled) affine maps from a standard simplex to a convex space. -/
--@[simps, implicit_reducible]
@[simps -isSimp]
noncomputable def affineMapMk {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y) :
    ConvexSpace.AffineMap R (StdSimplex R M) Y where
  toFun s := iConvexComb s f
  isAffineMap_toFun.map_sConvexComb s := by simp

@[simp]
lemma affineMapMk_single {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y) (m : M) :
    affineMapMk (R := R) f (.single m) = f m := by
  simp [affineMapMk_toFun]

lemma affineMapMk_surjective {M : Type*} {Y : Type*} [ConvexSpace R Y]
    (s : ConvexSpace.AffineMap R (StdSimplex R M) Y) :
    ∃ (f : M → Y), affineMapMk f = s :=
  ⟨fun i ↦ s (single i), by ext; simp [affineMapMk_toFun]⟩

open BigOperators

/-- In the standard simplex with vertices `M`, this is the isobarycenter of
a nonempty finite subset `S` of `M`. -/
@[simps]
noncomputable def subIsobarycenter
    {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
    {M : Type*} (S : Finset M) (hS : S.Nonempty) : StdSimplex K M where
  weights := S.sum (fun m ↦ .single m S.card⁻¹)
  nonneg := Finset.sum_nonneg (by simp)
  total := by
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simpa using IsUnit.mul_inv_cancel (Ne.isUnit (by simpa [← Finset.nonempty_iff_ne_empty]))

@[simp]
lemma subIsobarycenter_single
    {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
    {M : Type*} (m : M) :
    subIsobarycenter (K := K) {m} (by simp) = .single m := by
  aesop

/-- The isobarycenter of the standard simplex. -/
noncomputable abbrev isobarycenter
    {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
    {M : Type*} [Nonempty M] [Fintype M] : StdSimplex K M :=
  subIsobarycenter .univ (by simp)

lemma isobarycenter_of_unique
    {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
    {M : Type*} [Unique M] :
    isobarycenter (K := K) (M := M) = .single default := by
  subsingleton

@[simp]
lemma isobarycenter_fin_one
    {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K] :
    isobarycenter (K := K) (M := Fin 1) = .single 0 :=
  isobarycenter_of_unique

end StdSimplex

namespace ConvexSpace.AffineMap

variable {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
  {Y : Type*} [ConvexSpace K Y]

section

variable {M : Type*} (f : ConvexSpace.AffineMap K (StdSimplex K M) Y)

/-- Given an affine map from the standard simplex with vertices `M` and
a nonempty finite subset `S` of `M`, this is the image of the isobarycenter
of the face of the standard simplex corresponding to `S`. -/
noncomputable def subIsobarycenter (S : Finset M) (hS : S.Nonempty) : Y :=
  f (.subIsobarycenter S hS)

@[simp]
lemma subIsobarycenter_single (m : M) :
    f.subIsobarycenter {m} (by simp) = f (.single m) := by
  simp [subIsobarycenter]

/-- The image of the isobarycenter of the standard simplex by an affine map. -/
noncomputable abbrev isobarycenter [Nonempty M] [Fintype M] : Y := f .isobarycenter

end

@[simp]
lemma isobarycenter_mk_one (f : ConvexSpace.AffineMap K (StdSimplex K (Fin 1)) Y) :
    f.isobarycenter = f (.single 0) := by
  simp [isobarycenter]

section

variable {n : ℕ}

/-- Given an affine map `f` from the standard simplex of dimension `n - 1`,
a permutation `σ` of `Fin n` and `i : Fin n`, this is the image by `f`
of the isobarycenter of the face of the standard simplex corresponding
to `{ x : Fin n | i ≤ σ⁻¹ x}` (i.e. `{σ i, σ (i + 1), ..., σ (n - 1)}`). -/
noncomputable def sdVertex
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) : Y :=
  f.subIsobarycenter { x : Fin n | i ≤ σ⁻¹ x} ⟨σ i, by simp⟩

@[simp]
lemma sdVertex_zero
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin (n + 1))) Y)
    (σ : Equiv.Perm (Fin (n + 1))) :
    f.sdVertex σ 0 = f.isobarycenter := by
  simp [sdVertex, subIsobarycenter]

@[simp]
lemma sdVertex_last
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin (n + 1))) Y)
    (σ : Equiv.Perm (Fin (n + 1))) :
    f.sdVertex σ (Fin.last n) = f (.single (σ (Fin.last n))) := by
  have : ({ x | σ.symm x = Fin.last n } : Finset _) = {σ (Fin.last n)} := by
    ext
    simp [Equiv.symm_apply_eq]
  simp [sdVertex, this]

@[simp]
lemma sdVertex_mk_one (y : Y) (σ : Equiv.Perm (Fin 1)) :
    (StdSimplex.affineMapMk (R := K) ![y]).sdVertex σ = ![y] := by
  ext
  simp [sdVertex]

/-- Given an affine map `f` from the standard simplex of dimension `n` to `Y` and
a permutation `σ` of `Fin n`, this is the subdivision of `f` corresponding to `σ`:
this is again an affine map from the standard simplex of dimension `n`, and the
images of the vertices are given by `f.sdVertex σ : Fin n → Y` -/
noncomputable abbrev sd
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y) (σ : Equiv.Perm (Fin n)) :
    ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y :=
  StdSimplex.affineMapMk (f.sdVertex σ)

@[simp]
lemma sd_eq_self
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin 1)) Y) (σ : Equiv.Perm (Fin 1)) :
    f.sd σ = f := by
  obtain ⟨f, rfl⟩ := StdSimplex.affineMapMk_surjective f
  obtain ⟨s, rfl⟩ := Fin.exists_vecCons₁ f
  simp [sd]

end

end ConvexSpace.AffineMap

end Convexity
