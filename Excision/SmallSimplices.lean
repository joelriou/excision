/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Excision.ConvexSpace.Diameter
public import Excision.SimplicialSet.Homology
public import Excision.SimplicialSet.RelativeHomology
public import Excision.SingularHomology.Subdivision
public import Excision.Topology.LebesgueNumber

/-!
# Small simplices lemma

-/

universe w

@[expose] public section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial

namespace TopCat

variable {X : TopCat.{w}} {ι : Type*} {U : ι → Set X}

namespace toSSet

variable (U) in
/-- Let `U : ι → Set X` be a family of subsets of a topological space `X : TopCat`.
This is the subcomplex of the singular simplicial set `toSSet.obj X` of `X`
consisting of simplices that are contained in some `U i`. -/
noncomputable def subcomplexOfSets : (toSSet.obj X).Subcomplex :=
  ⨆ (i : ι), SSet.Subcomplex.range (toSSet.map (ofHom (X := U i) ⟨Subtype.val, by fun_prop⟩))

lemma mem_subcomplexOfSets_iff {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    s ∈ (subcomplexOfSets U).obj _ ↔
      ∃ (i : ι), Set.range (toSSetObjEquiv _ _ s) ⊆ U i := by
  simp only [subcomplexOfSets, Subfunctor.iSup_obj, Subfunctor.range_obj, Set.mem_iUnion,
    Set.mem_range]
  refine exists_congr (fun i ↦ ⟨?_, fun h ↦ ?_⟩)
  · rintro ⟨s, rfl⟩
    obtain ⟨f, rfl⟩ := (toSSetObjEquiv _ _).symm.surjective s
    change Set.range (Subtype.val ∘ f) ⊆ U i
    rintro _ ⟨u, rfl⟩
    simp
  · obtain ⟨f, rfl⟩ := (toSSetObjEquiv _ _).symm.surjective s
    exact ⟨(toSSetObjEquiv _ _).symm ⟨fun x ↦ ⟨f x, h (by simp)⟩, by fun_prop⟩, rfl⟩

lemma sd_mem_subcomplexOfSets {n : ℕ} (s : toSSet.obj X _⦋n⦌)
    (hs : s ∈ (subcomplexOfSets U).obj _) (σ : Equiv.Perm (Fin (n + 1))) :
    sd s σ ∈ (subcomplexOfSets U).obj _ := by
  rw [mem_subcomplexOfSets_iff] at hs ⊢
  obtain ⟨i, hi⟩ := hs
  exact ⟨i, le_trans (range_toSSetObjEquiv_sd_subset _ _) hi⟩

end toSSet

variable (U) in
noncomputable abbrev sSetPairOfSets : SSetPair.{w} :=
  SSetPair.of (toSSet.subcomplexOfSets U).ι

variable (U) in
/-- Given a family `U : ι → Set X` of subsets of a topological spaces `X`,
this is the condition that the union of the interiors of the `U i` covers `X`. -/
structure SmallSimplicesCondition : Prop where
  iUnion_interior : ⋃ (i : ι), interior (U i) = Set.univ

namespace SmallSimplicesCondition

variable (hU : SmallSimplicesCondition U)

variable (U) in
/-- Let `U : ι → Set X` be a family of subsets of a topological sapce `X`.
Let `s` be a singular `n`-simplex of `X`. For any `k : ℕ`, this is
the condition that after subdividing `k` times `s`, we obtain
simplices that are contained in some of the `U i`. -/
def SdIterIsSmall {n : ℕ} (s : toSSet.obj X _⦋n⦌) (k : ℕ) : Prop :=
  ∀ (σ : Fin k → Equiv.Perm (Fin (n + 1))),
    toSSet.sdIter s σ ∈ (toSSet.subcomplexOfSets U).obj _

lemma SdIterIsSmall.succ {n : ℕ} {s : toSSet.obj X _⦋n⦌} {k : ℕ}
    (hs : SdIterIsSmall U s k) :
    SdIterIsSmall U s (k + 1) :=
  fun σ ↦ by
    rw [toSSet.sdIter_succ]
    exact toSSet.sd_mem_subcomplexOfSets _ (hs _) _

lemma SdIterIsSmall.δ {n : ℕ} {s : toSSet.obj X _⦋n + 1⦌} {k : ℕ}
    (hs : SdIterIsSmall U s k) (i : Fin (n + 2)) :
    SdIterIsSmall U ((toSSet.obj X).δ i s) k := by
  intro σ
  obtain ⟨σ', i', h⟩ := toSSet.exists_sdIter_δ_eq s i σ
  rw [h]
  exact (toSSet.subcomplexOfSets U).map _ (hs _)

lemma SdIterIsSmall.of_le {n : ℕ} {s : toSSet.obj X _⦋n⦌} {k k' : ℕ}
    (hs : SdIterIsSmall U s k) (h : k ≤ k') :
    SdIterIsSmall U s k' := by
  obtain ⟨i, h⟩ := Nat.le.dest h
  induction i generalizing k k' with
  | zero =>
    obtain rfl : k = k' := by lia
    exact hs
  | succ i hi =>
    obtain rfl : k + i + 1 = k' := by lia
    exact (hi hs (by lia) rfl).succ

lemma sdIterIsSmall_zero_iff {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    SdIterIsSmall U s 0 ↔ s ∈ (toSSet.subcomplexOfSets U).obj _ := by
  simp [SdIterIsSmall]

include hU in
attribute [local instance] Convexity.ConvexSpace.ofModule in
open Convexity in
lemma exists_sdIterIsSmall {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    ∃ (k : ℕ), SdIterIsSmall U s k := by
  obtain ⟨f, rfl⟩ := (toSSetObjEquiv _ _).symm.surjective s
  let V (i : ι) : Set (stdSimplex ℝ (Fin (n + 1))) := f ⁻¹' (interior (U i))
  obtain ⟨ε, hε₀, hε⟩ := CompactSpace.lebesgue_number_lemma V
    (fun i ↦ f.continuous.isOpen_preimage _ isOpen_interior)
    (by simp [V, ← Set.preimage_iUnion, hU.iUnion_interior])
  let s₀ := ConvexSpace.AffineMap.id (R := ℝ) (StdSimplex ℝ (Fin (n + 1)))
  suffices ∃ (k : ℕ), ∀ (σ : Fin k → Equiv.Perm (Fin (n + 1))),
    (StdSimplex.ι.comp (s₀.sdIter σ)).diam ≤ ε by
      obtain ⟨k, hk⟩ := this
      refine ⟨k, fun σ ↦ ?_⟩
      rw [toSSet.mem_subcomplexOfSets_iff]
      obtain ⟨i, hi⟩ := hε (Set.range (StdSimplex.equiv ∘ (s₀.sdIter σ)))
        (Set.range_nonempty _) (by simpa [Set.range_comp] using hk σ)
      refine ⟨i, ?_⟩
      rintro _ ⟨x, rfl⟩
      refine interior_subset ?_
      simpa only [Set.mem_preimage, V, toSSet.sdIter_toSSetObjEquiv_symm] using!
        hi (Set.mem_range_self (StdSimplex.equiv.symm x))
  let δ := (StdSimplex.ι.comp s₀).diam
  have hδ : 0 ≤ δ := (StdSimplex.ι.comp s₀).diam_nonneg
  obtain h | h := hδ.lt_or_eq'
  · have hε' : 0 < ε / δ := by positivity
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε' (y := (n / (n + 1) : ℝ)) (by
      rw [div_lt_one (by positivity)]
      simp)
    refine ⟨k, fun σ ↦ ?_⟩
    rw [ConvexSpace.AffineMap.comp_sdIter]
    refine ((StdSimplex.ι.comp s₀).diam_sdIter_le σ).trans
      (le_of_le_of_eq (mul_le_mul_of_nonneg_right hk.le (ConvexSpace.AffineMap.diam_nonneg _))
      (div_mul_cancel₀ ε h.ne'))
  · exact ⟨0, by simp [δ, h, hε₀.le]⟩

include hU in
lemma nonempty_ofPred_sdIterIsSmall {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    (Set.ofPred (SdIterIsSmall U s)).Nonempty :=
  hU.exists_sdIterIsSmall s

/-- Given a family `U : ι → Set X` of subsets of a topological space `X` which
satisfy the condition `SmallSimplicesCondition U`, and `s` a singular
`n`-simplex of `X`, this is the smallest `k : ℕ` such that
the condition `SdIterIsSmall U s k` is satisfied, i.e. that the
`k`th iterated subdivisions of `s` all belong to some of the `U i`. -/
noncomputable def m {n : ℕ} (s : toSSet.obj X _⦋n⦌) : ℕ :=
  Nat.lt_wfRel.wf.min _ (hU.nonempty_ofPred_sdIterIsSmall s)

lemma sdIterIsSmall_m {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    SdIterIsSmall U s (hU.m s) :=
  Nat.lt_wfRel.wf.min_mem _ (hU.nonempty_ofPred_sdIterIsSmall s)

lemma sdIterIsSmall_iff_m_le {n : ℕ} (s : toSSet.obj X _⦋n⦌) (k : ℕ) :
    SdIterIsSmall U s k ↔ hU.m s ≤ k :=
  ⟨fun h ↦ Nat.lt_wfRel.wf.min_le h, fun h ↦ (hU.sdIterIsSmall_m s).of_le h⟩

lemma m_eq_zero_iff {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    hU.m s = 0 ↔ s ∈ (toSSet.subcomplexOfSets U).obj _ := by
  rw [← sdIterIsSmall_zero_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ le_antisymm ?_ (by simp)⟩
  · simpa only [← h] using hU.sdIterIsSmall_m s
  · rwa [← sdIterIsSmall_iff_m_le]

lemma m_δ_le {n : ℕ} (s : toSSet.obj X _⦋n + 1⦌) (i : Fin (n + 2)) :
    hU.m ((toSSet.obj X).δ i s) ≤ hU.m s := by
  rw [← sdIterIsSmall_iff_m_le]
  exact (hU.sdIterIsSmall_m s).δ i

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

include hU

noncomputable def hρ (R : C) (n : ℕ) :
    (X.singularChainComplex R).X n ⟶ (X.singularChainComplex R).X (n + 1) :=
  Limits.Sigma.desc (fun x ↦
    ∑ (i : Fin (hU.m x)),
        TopCat.ιSingularChainComplex _ x ≫ (X.singularChainComplexSdIter i.val).f n ≫
          X.singularChainComplexHomotopyIdSd.hom _ _ )

@[reassoc]
lemma ι_hρ (R : C) {n : ℕ} (x : toSSet.obj X _⦋n⦌) :
    TopCat.ιSingularChainComplex _ x ≫ hU.hρ R n =
      ∑ (i : Fin (hU.m x)),
        TopCat.ιSingularChainComplex _ x ≫ (X.singularChainComplexSdIter i.val).f n ≫
          X.singularChainComplexHomotopyIdSd.hom _ _ :=
  Sigma.ι_desc ..

noncomputable def hρ' (R : C) (n m : ℕ) :
    (X.singularChainComplex R).X n ⟶ (X.singularChainComplex R).X m :=
  if h : n + 1 = m then hU.hρ R n ≫ eqToHom (by simp [h]) else 0

@[simp]
lemma hρ'_eq (R : C) (n : ℕ) : hU.hρ' R n (n + 1) = hU.hρ R n := by simp [hρ']

lemma hρ'_zero (R : C) (n m : ℕ) (h : n + 1 ≠ m) : hU.hρ' R n m = 0 := by grind [hρ']

noncomputable def ρ' (R : C) :
    X.singularChainComplex R ⟶ X.singularChainComplex R :=
  𝟙 _ - Homotopy.nullHomotopicMap (hU.hρ' R)

set_option backward.isDefEq.respectTransparency false in
noncomputable def homotopyρ'Id (R : C) :
    _root_.Homotopy (hU.ρ' R) (𝟙 _) :=
  (Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [ρ'])) (.nullHomotopy (hU.hρ' R) (hU.hρ'_zero R)))).symm

@[reassoc]
lemma ι_ρ'_f (R : C) {n : ℕ} (x : (toSSet.obj X) _⦋n⦌)
    (hx : x ∈ (toSSet.subcomplexOfSets U).obj _) :
    X.ιSingularChainComplex x ≫ (hU.ρ' R).f n = X.ιSingularChainComplex x := by
  dsimp [ρ']
  simp only [Preadditive.comp_sub, Category.comp_id, sub_eq_self]
  replace hx := (hU.m_eq_zero_iff x).2 hx
  obtain _ | n := n
  · rw [Homotopy.nullHomotopicMap_f_of_not_rel_left (k₁ := 1) (by simp) (by simp),
      hρ'_eq, ι_hρ_assoc, Finset.sum_eq_zero (fun ⟨i, hi⟩ ↦ by simp [hx] at hi),
      zero_comp]
  · rw [Homotopy.nullHomotopicMap_f (k₂ := n + 2) (k₀ := n) (by simp) (by simp),
      hρ'_eq, hρ'_eq, Preadditive.comp_add, ι_hρ_assoc,
      Finset.sum_eq_zero (fun ⟨i, hi⟩ ↦ by simp [hx] at hi),
      zero_comp, add_zero, ι_singularChainComplex_d_assoc, Preadditive.sum_comp,
      Finset.sum_eq_zero]
    intro i _
    rw [Linear.smul_comp, ι_hρ, Finset.sum_eq_zero, smul_zero]
    intro ⟨j, hj⟩
    have := lt_of_lt_of_le hj (hU.m_δ_le _ _)
    simp [hx] at this

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma chainComplexMap_ι_ρ' (R : C) :
    SSet.chainComplexMap
      (TopCat.toSSet.subcomplexOfSets U).ι R ≫ hU.ρ' R =
        SSet.chainComplexMap (toSSet.subcomplexOfSets U).ι R := by
  ext n ⟨x, hx⟩
  simpa using! hU.ι_ρ'_f R x hx

set_option backward.isDefEq.respectTransparency false in -- necessary for `reassoc`
@[reassoc (attr := simp)]
lemma ρ'_chainComplexπ (R : C) :
    hU.ρ' R ≫ (sSetPairOfSets U).chainComplexπ R = 0 := by
  sorry

@[no_expose]
noncomputable def ρ (R : C) :
    X.singularChainComplex R ⟶
      (toSSet.subcomplexOfSets U).toSSet.chainComplex R :=
  (KernelFork.IsLimit.lift'
    ((sSetPairOfSets U).isLimitKernelForkChainComplex R) _ (hU.ρ'_chainComplexπ R)).1

@[reassoc (attr := simp)]
lemma ρ'_ι (R : C) :
    hU.ρ R ≫ SSet.chainComplexMap
      (TopCat.toSSet.subcomplexOfSets U).ι R = hU.ρ' R :=
  (KernelFork.IsLimit.lift'
    ((sSetPairOfSets U).isLimitKernelForkChainComplex R) _ (hU.ρ'_chainComplexπ R)).2

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ι_ρ (R : C) :
    SSet.chainComplexMap
      (TopCat.toSSet.subcomplexOfSets U).ι R ≫ hU.ρ R = 𝟙 _ := by
  simp [← cancel_mono (SSet.chainComplexMap (TopCat.toSSet.subcomplexOfSets U).ι R)]

set_option backward.isDefEq.respectTransparency false in
noncomputable def homotopyEquiv (R : C) :
    HomotopyEquiv
      ((toSSet.subcomplexOfSets U).toSSet.chainComplex R)
      ((toSSet.obj X).chainComplex R) where
  hom := SSet.chainComplexMap (TopCat.toSSet.subcomplexOfSets U).ι R
  inv := hU.ρ R
  homotopyHomInvId := .ofEq (by simp)
  homotopyInvHomId := .trans (.ofEq (by simp)) (hU.homotopyρ'Id R)

lemma homotopyEquivalences (R : C) :
    homotopyEquivalences _ _
      (SSet.chainComplexMap (TopCat.toSSet.subcomplexOfSets U).ι R) :=
  ⟨hU.homotopyEquiv R, rfl⟩

end SmallSimplicesCondition

end TopCat
