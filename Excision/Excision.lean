/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.TopPair
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

/-lemma homotopyEquivalences (R : C) :
    homotopyEquivalences _ _
      (SSetPair.chainComplexMap (TopPair.toSSetPair.map h.topPairHom) R) := by
  sorry-/

end ExcisionCondition

end TopCat
