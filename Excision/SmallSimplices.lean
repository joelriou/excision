/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Excision.ConvexSpace.Diameter
public import Excision.SingularHomology.Subdivision
public import Excision.Topology.LebesgueNumber

/-!
# Small simplices lemma

-/

universe w

@[expose] public section

open CategoryTheory Limits HomologicalComplex Simplicial

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
      have := hi (Set.mem_range_self (StdSimplex.equiv.symm x))
      simp only [Set.mem_preimage, V] at this
      refine interior_subset ?_
      convert this using 1
      sorry
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

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

include hU in
lemma homotopyEquivalences (R : C) :
    homotopyEquivalences _ _
      (SSet.chainComplexMap (TopCat.toSSet.subcomplexOfSets U).ι R) := by
  have := hU
  sorry

end SmallSimplicesCondition

end TopCat
