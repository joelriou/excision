/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Excision.ConvexSpace.StdSimplex
public import Excision.ConvexSpace.Top
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Module

/-!
# Diameter of the subdivision of affine

-/

@[expose] public section

lemma monotone_self_div_succ (a b : ℝ) (h : a ≤ b) (ha : 0 ≤ a := by positivity) :
    a / (a + 1) ≤ b / (b + 1) := by
  have (t : ℝ) (ht : t ≠ -1) : t / (t + 1) = 1 - 1 / (t + 1) := by
    grind
  rw [this a (by grind), this b (by grind), sub_le_sub_iff_left]
  exact one_div_le_one_div_of_le (by grind) (by simpa)

namespace Convexity

namespace ConvexSpace

namespace AffineMap

variable {n : ℕ} {X E : Type*} [ConvexSpace ℝ X] [NormedAddCommGroup E]
  [ConvexSpace ℝ E]

/-- The diameter of the range of an affine map to a normed real vector space. -/
noncomputable def diam (f : ConvexSpace.AffineMap ℝ X E) : ℝ :=
  Metric.diam (Set.range f)

lemma diam_nonneg (f : ConvexSpace.AffineMap ℝ X E) :
    0 ≤ f.diam :=
  Metric.diam_nonneg

variable [NormedSpace ℝ E] [IsModuleConvexSpace ℝ E]

lemma convex_range (f : ConvexSpace.AffineMap ℝ X E) :
    Convex ℝ (Set.range f) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ a b ha hb h
  exact ⟨convexCombPair a b ha hb h x y,
    by simp [f.isAffineMap.map_convexCombPair]⟩

variable (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) E)

lemma range_subset_iff_of_convex {F : Set E} (hF : Convex ℝ F) :
    Set.range s ⊆ F ↔ ∀ i, s (.single i) ∈ F := by
  refine ⟨fun h i ↦ h (by simp), fun h ↦ ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨p, rfl⟩ := StdSimplex.affineMapMk_surjective s
  rw [StdSimplex.affineMapMk_apply_eq_sum]
  refine hF.sum_mem (by simp) ?_ (by simpa using h)
  have := x.total
  rwa [Finsupp.sum_fintype _ _ (by simp)] at this

lemma range_eq_convexHull :
    Set.range s = _root_.convexHull ℝ (Set.range (s ∘ StdSimplex.single)) := by
  refine subset_antisymm ?_ ?_
  · rw [s.range_subset_iff_of_convex (convex_convexHull ..)]
    exact fun _ ↦ subset_convexHull _ _ (by simp)
  · rw [s.convex_range.convexHull_subset_iff]
    apply Set.range_comp_subset_range

lemma isBounded_range : Bornology.IsBounded (Set.range s) := by
  rw [range_eq_convexHull, isBounded_convexHull, ← boundedSpace_induced_iff]
  infer_instance

lemma exists_diam_eq :
    ∃ i j, s.diam = dist (s (.single i)) (s (.single j)) := by
  have : s.diam = Metric.diam (Set.range (s ∘ StdSimplex.single)) := by
    simp [diam, range_eq_convexHull]
  simp only [this]
  let φ (i j : Fin (n + 1)) : ℝ := dist (s (.single i)) (s (.single j))
  have := φ.uncurry
  let μ := (Finset.univ.image φ.uncurry).max' (by simp)
  have hμ : μ ∈ _ := (Finset.univ.image φ.uncurry).max'_mem (by simp)
  have hμ' (i j : Fin (n + 1)) : φ i j ≤ μ :=
    (Finset.univ.image φ.uncurry).le_max' _ (by simp)
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.exists,
    Function.uncurry_apply_pair] at hμ
  obtain ⟨i, j, h⟩ := hμ
  refine ⟨i, j, le_antisymm ?_ ?_⟩
  · refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    rintro _ ⟨i', rfl⟩ _ ⟨j', rfl⟩
    exact le_of_le_of_eq (hμ' i' j') h.symm
  · exact Metric.dist_le_diam_of_mem
      (Metric.isBounded_range_iff.2 ⟨μ, hμ'⟩) (by simp) (by simp)

lemma diam_comp_le {d : ℕ}
    (t : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (d + 1))) (StdSimplex ℝ (Fin (n + 1)))) :
    (s.comp t).diam ≤ s.diam :=
  Metric.diam_mono (Set.range_comp_subset_range t s) s.isBounded_range

lemma dist_barycenter_le (e : E) (he : e ∈ Set.range s) :
    dist s.isobarycenter e ≤ n / (n + 1) * s.diam := by
  sorry

lemma dist_subIsobarycenter_le
    (t : Finset (Fin (n + 1))) (ht : t.Nonempty) (y : StdSimplex ℝ (Fin (n + 1)))
    (hy : ∀ (i : Fin (n + 1)), i ∉ t → y.weights i = 0) :
    dist (s.subIsobarycenter t ht) (s y) ≤ n / (n + 1) * s.diam := by
  obtain ⟨d, hdn, ⟨e⟩⟩ : ∃ (d : ℕ) (_ : d ≤ n), Nonempty (t ≃ Fin (d + 1)) := by
    generalize hd : t.card = d
    obtain _ | d := d
    · grind
    · refine ⟨d, ?_, ?_⟩
      · simpa [hd] using Finset.card_le_card t.subset_univ
      · rw [← hd]
        exact ⟨Finset.equivFin _⟩
  let φ : Fin (d + 1) → Fin (n + 1) := Subtype.val ∘ e.symm
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have hφ' : Finset.image φ .univ = t := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, Function.comp_apply, true_and, φ]
    exact ⟨by grind, fun ha ↦ ⟨e ⟨a, ha⟩, by simp⟩⟩
  have := s.subIsobarycenter_comp_of_injective .univ (by simp) φ hφ
  simp only [hφ'] at this
  rw [← this]
  refine ((s.comp (StdSimplex.affineMap φ)).dist_barycenter_le (s y) ?_).trans
    (mul_le_mul (monotone_self_div_succ d n (by simpa)) (diam_comp_le _ _)
      (diam_nonneg _) (by positivity))
  obtain ⟨x, rfl⟩ := StdSimplex.mem_range_affineMap y φ (by grind)
  exact Set.mem_range_self x

section

lemma diam_sd_le
    (σ : Equiv.Perm (Fin (n + 1))) :
    (s.sd σ).diam ≤ n / (n + 1) * s.diam := by
  have : IsModuleConvexSpace ℝ E := inferInstance
  suffices ∀ (i j : Fin (n + 1)) (hij : i ≤ j),
      dist (s.sdVertex σ i) (s.sdVertex σ j) ≤ (n / (n + 1)) * s.diam by
    obtain ⟨i, j, h⟩ := (s.sd σ).exists_diam_eq
    simp only [h, StdSimplex.affineMapMk_single]
    obtain hij | hij := le_total i j
    · exact this _ _ hij
    · rw [dist_comm]
      exact this _ _ hij
  refine fun i j hij ↦ s.dist_subIsobarycenter_le _ _ _
    (fun k hk ↦ StdSimplex.subIsobarycenter_weights_apply_eq_zero _ _ _ ?_)
  simp only [Equiv.Perm.coe_inv, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk ⊢
  exact lt_of_lt_of_le hk hij

lemma diam_sdIter_le
    {k : ℕ} (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    (s.sdIter σ).diam ≤ (n / (n + 1)) ^ k * s.diam := by
  induction k with
  | zero => simp
  | succ k hk =>
    nth_rw 2 [add_comm k 1]
    rw [sdIter_succ, pow_add, pow_one, mul_assoc]
    exact (diam_sd_le _ _).trans (mul_le_mul_of_nonneg_left (hk _) (by positivity))

end

end AffineMap

end ConvexSpace

@[simp]
lemma StdSimplex.diam_equiv_image_range_affineMap
    {α β : Type*} [Fintype β] (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ α) (StdSimplex ℝ β)) :
    Metric.diam (StdSimplex.equiv '' (Set.range s)) = (StdSimplex.ι.comp s).diam := by
  rw [← isometry_subtype_coe.diam_image]
  dsimp [ConvexSpace.AffineMap.diam]
  rw [Set.range_comp, ← Set.image_comp]
  rfl

end Convexity
