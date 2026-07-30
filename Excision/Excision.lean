/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.TopPair
public import Excision.HomotopyCategory.HomotopyEquivalences
public import Excision.SmallSimplices

/-!
# Excision theorem

-/

universe w

@[expose] public section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Opposite Topology

/-- The topological pair `(B, A)` when `A ⊆ B`. -/
abbrev TopPair.ofSubsets {X : TopCat.{w}} {A B : Set X} (h : A ⊆ B) : TopPair.{w} :=
  TopPair.of (TopCat.ofHom (.inclusion h)) (IsEmbedding.inclusion h)

instance : TopPair.proj₁.{w}.Faithful where
  map_injective {X Y f g h} := by
    ext x
    · apply Y.prop.injective
      rw [dsimp% (ConcreteCategory.congr_hom f.w x),
        dsimp% (ConcreteCategory.congr_hom g.w x)]
      exact ConcreteCategory.congr_hom h (X.map x)
    · exact ConcreteCategory.congr_hom h x

lemma Topology.IsEmbedding.to_isHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsEmbedding f) (hf' : Function.Surjective f) :
    IsHomeomorph f := by
  rw [← Set.range_eq_univ] at hf'
  exact (Homeomorph.trans (hf.toHomeomorph.trans (Homeomorph.setCongr hf'))
    (Homeomorph.Set.univ Y)).isHomeomorph

lemma TopCat.isIso_of_isEmbedding {X Y : TopCat.{w}} (f : X ⟶ Y)
    (hf : IsEmbedding f) (hf' : Function.Surjective f) :
    IsIso f :=
  (TopCat.isoOfHomeo (hf.to_isHomeomorph hf').homeomorph).isIso_hom

lemma TopPair.isIso_of_isIso {X Y : TopPair.{w}} (f : X ⟶ Y)
    (h₁ : IsIso (Hom.fst f) := by infer_instance) (h₂ : IsIso (Hom.snd f) := by infer_instance) :
    IsIso f := by
  let φ : Y ⟶ X := TopPair.ofHom (inv (Hom.fst f)) (inv (Hom.snd f)) (by simpa using f.w.symm)
  exact ⟨φ, TopPair.proj₁.map_injective (IsIso.hom_inv_id _),
    TopPair.proj₁.map_injective (IsIso.inv_hom_id _)⟩

lemma TopPair.isEmbedding_snd_of_isEmbedding_fst
    {X Y : TopPair.{w}} {f : X ⟶ Y}
    (hf : IsEmbedding (Hom.fst f)) :
    IsEmbedding (Hom.snd f) := by
  rw [← IsEmbedding.of_comp_iff (g := Y.map) Y.prop]
  convert! hf.comp X.prop
  ext x
  exact ConcreteCategory.congr_hom f.w x

lemma TopPair.isIso_of_isEmbedding {X Y : TopPair.{w}} (f : X ⟶ Y)
    (hf : IsEmbedding (Hom.fst f))
    (h₁ : Function.Surjective (Hom.fst f))
    (h₂ : Function.Surjective (Hom.snd f)) :
    IsIso f :=
  TopPair.isIso_of_isIso _
    (TopCat.isIso_of_isEmbedding _ hf h₁)
    (TopCat.isIso_of_isEmbedding _ (isEmbedding_snd_of_isEmbedding_fst hf) h₂)

lemma TopCat.mono_toSSet_map {X Y : TopCat.{w}} (f : X ⟶ Y) (hf : Function.Injective f) :
    Mono (toSSet.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro ⟨⟨n⟩⟩
  rw [CategoryTheory.mono_iff_injective]
  intro x y h
  apply (toSSetObjEquiv _ _).injective
  ext t
  exact hf (DFunLike.congr_fun ((toSSetObjEquiv Y (op ⦋n⦌)).congr_arg h) t)

instance (P : TopPair.{w}) : Mono (TopCat.toSSet.map P.map) :=
  TopCat.mono_toSSet_map _ P.isEmbedding_map.injective

set_option backward.isDefEq.respectTransparency false in
/-- The functor `TopPair ⥤ SSetPair` that is induced by `TopCat.toSSet : TopCat ⥤ SSet`. -/
@[implicit_reducible, simps]
noncomputable def TopPair.toSSetPair : TopPair.{w} ⥤ SSetPair.{w} where
  obj P := .of (TopCat.toSSet.map P.map)
  map f :=
    MorphismProperty.Arrow.homMk (TopCat.toSSet.map f.left) (TopCat.toSSet.map f.right)
      (by simp [← Functor.map_comp])

namespace TopCat

variable {X : TopCat.{w}} {ι : Type*} {A B : Set X}

variable (A B) in
/-- Given two subsets `A` and `B` of a topological space `X`, this is
the condition that the interiors of `A` and `B` cover `X`. -/
structure ExcisionCondition : Prop where
  union_interior : interior A ∪ interior B = Set.univ

variable (h : ExcisionCondition A B)

namespace ExcisionCondition

include h in
lemma smallSimplicesCondition : SmallSimplicesCondition (Bool.rec A B) where
  iUnion_interior := by rw [← h.union_interior]; aesop

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C] {R : C}

/-- Assuming `A` and `B` are subsets of a topological space satisfying `ExcisionCondition A B`,
this is the morphism of topological pairs `(B, A ∩ B) ⟶ (X, A)`. -/
def topPairHom (_ : ExcisionCondition A B) :
    (TopPair.ofSubsets (Set.inter_subset_right : A ∩ B ⊆ B)) ⟶ TopPair.ofSubset A :=
  TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left)) rfl

-- TODO: The relative chain complex of `B` relative to `A ∩ B`
-- is homotopically equivalent to the chain complex of `X` relative to `A`

lemma homotopyEquivalences (R : C) :
    homotopyEquivalences _ _
      (SSetPair.chainComplexMap (TopPair.toSSetPair.map h.topPairHom) R) := by
  sorry

end ExcisionCondition

end TopCat

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

set_option backward.isDefEq.respectTransparency false in
lemma TopPair.homotopyEquivalences_of_excision {V X : TopPair} (g : V ⟶ X)
      (h₁ : IsEmbedding (Hom.fst g))
      (h₂ : Set.range (Hom.fst g ∘ V.map) = Set.range (Hom.fst g) ∩ Set.range X.map)
      (h₃ : closure (Set.range (Hom.fst g))ᶜ ⊆ interior (Set.range X.map)) (R : C) :
    homotopyEquivalences _ _ (SSetPair.chainComplexMap (TopPair.toSSetPair.map g) R) := by
  generalize hA : Set.range X.map = A
  generalize hB : Set.range (Hom.fst g) = B
  simp only [hA, hB] at h₂ h₃
  have h : TopCat.ExcisionCondition A B := ⟨by
    rwa [closure_compl, Set.compl_subset_iff_union, Set.union_comm] at h₃⟩
  obtain ⟨e₁, e₂, fac⟩ : ∃ (e₁ : _ ≅ _) (e₂ : _ ≅ _), e₁.hom ≫ h.topPairHom = g ≫ e₂.hom := by
    let f₁ : V ⟶ .ofSubsets (Set.inter_subset_right : A ∩ B ⊆ B) :=
      TopPair.ofHom (TopCat.ofHom ⟨fun v ↦ ⟨Hom.fst g v, by aesop⟩, by fun_prop⟩)
        (TopCat.ofHom ⟨fun v ↦ ⟨Hom.fst g (V.map v), by
          rw [Set.inter_comm, ← h₂]
          exact Set.mem_range_self v⟩, by fun_prop⟩) rfl
    let f₂ : X ⟶ .ofSubset A :=
      TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨fun x ↦ ⟨X.map x, by aesop⟩, by fun_prop⟩)
    have : IsIso f₁ := by
      apply TopPair.isIso_of_isEmbedding
      · rw [← IsEmbedding.of_comp_iff (hg := IsEmbedding.subtypeVal)]
        exact h₁
      · rintro ⟨x, hx⟩
        rw [← hB] at hx
        obtain ⟨y, rfl⟩ := hx
        exact ⟨y, rfl⟩
      · rintro ⟨x, hx⟩
        rw [Set.inter_comm, ← h₂] at hx
        obtain ⟨y, rfl⟩ := hx
        exact ⟨y, rfl⟩
    have : IsIso f₂ := by
      apply TopPair.isIso_of_isEmbedding
      · apply IsEmbedding.id
      · intro x
        exact ⟨x, rfl⟩
      · rintro ⟨x, hx⟩
        rw [← hA] at hx
        obtain ⟨y, rfl⟩ := hx
        exact ⟨y, rfl⟩
    exact ⟨asIso f₁, asIso f₂, proj₁.map_injective rfl⟩
  refine (MorphismProperty.arrow_mk_iso_iff _ ?_).2 (h.homotopyEquivalences R)
  refine
    Arrow.isoMk
      (SSetPair.chainComplexMapIso
        (MorphismProperty.Arrow.isoMk
          (TopCat.toSSet.mapIso (TopPair.proj₂.mapIso e₁))
          (TopCat.toSSet.mapIso (TopPair.proj₁.mapIso e₁)) ?_) R)
      (SSetPair.chainComplexMapIso
        (MorphismProperty.Arrow.isoMk
          (TopCat.toSSet.mapIso (TopPair.proj₂.mapIso e₂))
          (TopCat.toSSet.mapIso (TopPair.proj₁.mapIso e₂ :)) ?_) R) ?_
  · simp [← Functor.map_comp]
    rfl
  · simp [← Functor.map_comp]
    rfl
  · simp only [toSSetPair_obj, toSSetPair_map, Arrow.mk_left, Arrow.mk_right,
      MorphismProperty.Arrow.isoMk, MorphismProperty.Comma.isoMk,
      MorphismProperty.Comma.isoFromComma, MorphismProperty.Comma.homFromCommaOfIsIso,
      Functor.comp_obj, Arrow.mk_hom, ← Functor.map_comp]
    congr 1
    ext : 1
    · simp only [MorphismProperty.Comma.comp_hom, MorphismProperty.Comma.Hom.hom_mk,
        MorphismProperty.Arrow.homMk_hom, Comma.comp_left, Comma.isoMk_hom_left, Functor.mapIso_hom,
        Functor.comp_map, MorphismProperty.Comma.forget_map, Arrow.leftFunc_map, Arrow.homMk_left,
        ← Functor.map_comp]
      congr 1
      exact Functor.congr_map TopPair.proj₂ fac
    · simp only [MorphismProperty.Comma.comp_hom, MorphismProperty.Comma.Hom.hom_mk,
        MorphismProperty.Arrow.homMk_hom, Comma.comp_right, Comma.isoMk_hom_right,
        Functor.mapIso_hom, Functor.comp_map, MorphismProperty.Comma.forget_map,
        Arrow.rightFunc_map, Arrow.homMk_right, ← Functor.map_comp]
      congr 1
      exact Functor.congr_map TopPair.proj₁ fac
