/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Excision.SimplicialSet.RelativeHomology
public import Excision.HomotopyCategory.ChainComplex
public import Excision.HomotopyCategory.HomotopyEquivalences
public import Excision.Limits.SigmaConst

/-!
# ...

-/

universe w

@[expose] public section

open CategoryTheory Limits Simplicial HomologicalComplex Opposite

namespace SSet.Subcomplex

variable {X : SSet.{w}} (A : X.Subcomplex)

@[simp] lemma pair_left : A.pair.left = A := rfl
@[simp] lemma pair_right : A.pair.right = X := rfl
@[simp] lemma pair_hom : A.pair.hom = A.ι := rfl

end SSet.Subcomplex

namespace SSetPair

section

variable {X Y : SSet.{w}} (i : X ⟶ Y) [Mono i]

@[simp] lemma of_left : (of i).left = X := rfl
@[simp] lemma of_right : (of i).right = Y := rfl
@[simp] lemma of_hom : (of i).hom = i := rfl

end

section

/-- Constructor for morphisms in `SSetPair`. -/
abbrev homMk {X Y : SSetPair.{w}} (f₁ : X.left ⟶ Y.left) (f₂ : X.right ⟶ Y.right)
    (w : f₁ ≫ Y.hom = X.hom ≫ f₂ := by cat_disch) :
    X ⟶ Y:=
  MorphismProperty.Arrow.homMk f₁ f₂ w

/-- Constructor for isomorphisms in `SSetPair`. -/
abbrev isoMk {X Y : SSetPair.{w}} (e₁ : X.left ≅ Y.left) (e₂ : X.right ≅ Y.right)
    (w : e₁.hom ≫ Y.hom = X.hom ≫ e₂.hom := by cat_disch) :
    X ≅ Y :=
  MorphismProperty.Arrow.isoMk e₁ e₂ w

end

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

section

variable (X : SSetPair.{w}) (R : C) (n : ℕ)

/-- If `X : SSetPair` and `n : ℕ`, this is a splitting of the short complex
relating the `n`-chains of `X.left`, `X.right` and `X`. -/
noncomputable def splittingChainComplexShortComplexEval :
    ((X.chainComplexShortComplex R).map (eval C _ n)).Splitting :=
  splittingSigmaConstCokernelShortComplex' _ _
    ((injective_of_mono _)) (X.isColimitCokernelCoforkChainComplexX R n)

end


section

variable {X : SSet.{w}} (A B : X.Subcomplex)

/-- The morphism from the pair `(B, A ⊓ B)` to `(X, A)` when `A` and `B` are
subcomplexes of a simplicial set `X`. -/
def homOfSubcomplexes :
    of (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) ⟶ A.pair :=
  SSetPair.homMk (SSet.Subcomplex.homOfLE (by simp)) B.ι (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- When `A` and `B` are subcomplexes of a simplicial set `X`, this is
a degreewise-split short complex which relates the chain complexes of
the pairs `(B, A ⊓ B)`, `(X, A)` and `(X, A ⊔ B)`. -/
noncomputable abbrev shortComplexHomOfSubcomplexes (R : C) :
    ShortComplex (ChainComplex C ℕ) where
  f := chainComplexMap (homOfSubcomplexes A B) R
  X₃ := (of (A ⊔ B).ι).chainComplex R
  g := chainComplexMap (SSetPair.homMk (SSet.Subcomplex.homOfLE (by simp)) (𝟙 X) (by simp)) R
  zero := by
    rw [← cancel_epi (chainComplexπ ..), ← Functor.map_comp,
      chainComplexπ_naturality, comp_zero]
    have h : A ⊓ B ≤ A ⊔ B := inf_left_le_sup_left
    calc
      _ = SSet.chainComplexMap (SSet.Subcomplex.homOfLE (by simp)) R ≫
          SSet.chainComplexMap (of (A ⊔ B).ι).hom R ≫ (of (A ⊔ B).ι).chainComplexπ R := by
        rw [← Functor.map_comp_assoc]
        rfl
      _ = _ := by
        simp [dsimp% (of (A ⊔ B).ι).chainComplex_condition R]

open Classical in
set_option backward.isDefEq.respectTransparency false in
/-- When `A` and `B` are subcomplexes of a simplicial set `X`, this is
the degreewise splitting of the short complex which relates the chain
complexes of the pairs `(B, A ⊓ B)`, `(X, A)` and `(X, A ⊔ B)`. -/
noncomputable def splittingShortComplexHomOfSubcomplexesEval (R : C) (n : ℕ) :
    ((shortComplexHomOfSubcomplexes A B R).map (eval _ _ n)).Splitting := by
  exact
    { r :=
        chainComplexXDesc
          (fun x ↦
            if hx : x ∈ B.obj _ then
              SSet.ιChainComplex _ (by exact ⟨x, hx⟩) ≫ (SSetPair.chainComplexπ _ _).f n
            else 0) (fun x ↦ by
              split_ifs with hx
              · exact (of (SSet.Subcomplex.homOfLE _)).ιChainComplex_π_f_eq_zero_of_mem_range
                  _ _ ⟨⟨x.val, ⟨x.prop, hx⟩⟩, rfl⟩
              · simp)
      s :=
        chainComplexXDesc
          (fun x ↦
            if hx : x ∈ B.obj _ then 0 else
              X.ιChainComplex x ≫ (A.pair.chainComplexπ R).f n)
          (fun ⟨x, hx⟩ ↦ by
            split_ifs with hx'
            · simp
            · apply ιChainComplex_π_f_eq_zero_of_subcomplex
              simp at hx
              tauto)
      f_r :=
        chainComplexX_hom_ext (fun x hx ↦ by
          dsimp
          simp only [ShortComplex.map_f, eval_map,
            chainComplexπ_f_naturality_assoc, SSet.ι_chainComplexMap_f_assoc,
            ι_chainComplexXDesc]
          erw [Category.comp_id]
          exact dif_pos x.prop)
      s_g :=
        chainComplexX_hom_ext (fun x hx ↦ by
          simp only [ShortComplex.map_g, eval_map,
            ι_chainComplexXDesc_assoc]
          erw [Category.comp_id]
          rw [dif_neg (fun h ↦ hx ⟨⟨x, Or.inr h⟩, rfl⟩)]
          simp [chainComplexπ_f_naturality])
      id :=
        chainComplexX_hom_ext (fun x hx ↦ by
          simp only [ShortComplex.map_f, ShortComplex.map_g, eval_map,
            Preadditive.comp_add, ι_chainComplexXDesc_assoc,
            ι_chainComplexMap_f_assoc]
          erw [ι_chainComplexXDesc]
          simp only [of_right, MorphismProperty.Arrow.homMk_hom, Arrow.homMk_right,
            NatTrans.id_app, id_apply, dite_eq_ite]
          erw [Category.comp_id]
          split_ifs with hx'
          · simp [chainComplexπ_f_naturality]
            rfl
          · simp) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma homotopyEquivalences_chainComplexMap_homOfSubcomplexes (R : C) :
    homotopyEquivalences _ _ (chainComplexMap (homOfSubcomplexes A B) R) ↔
      homotopyEquivalences _ _ (SSet.chainComplexMap (A ⊔ B).ι R) := by
  have : HasZeroObject C := Preadditive.hasZeroObject_of_hasCoproducts C
  have : HasFiniteCoproducts C := hasFiniteCoproducts_of_hasCoproducts C
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts
  rw [dsimp% ChainComplex.homotopyEquivalences_shortComplexF_iff_of_degreewiseSplit
    _ ((of (A ⊔ B).ι).splittingChainComplexShortComplexEval R),
    ChainComplex.homotopyEquivalences_shortComplexF_iff_of_degreewiseSplit
      _ (splittingShortComplexHomOfSubcomplexesEval A B R)]

end

lemma mono_left_of_mono_right {X Y : SSetPair.{w}}
    (f : X ⟶ Y) [Mono f.right] :
    Mono f.left :=
  mono_of_mono_fac f.w

lemma homotopyEquivalence_chainComplexMap_iff_of_mono {X Y : SSetPair.{w}}
    (f : X ⟶ Y) (R : C)
    (Z : Y.right.Subcomplex)
    (h₀ : Z = SSet.Subcomplex.range Y.hom ⊔ SSet.Subcomplex.range f.right)
    (h₁ : Mono f.right) (h₂ : SSet.Subcomplex.range (f.left ≫ Y.hom) =
      SSet.Subcomplex.range Y.hom ⊓ SSet.Subcomplex.range f.right) :
    homotopyEquivalences _ _ (chainComplexMap f R) ↔
      homotopyEquivalences _ _ (SSet.chainComplexMap Z.ι R) := by
  subst h₀
  rw [← homotopyEquivalences_chainComplexMap_homOfSubcomplexes]
  have := mono_left_of_mono_right f
  suffices Arrow.mk f ≅ Arrow.mk (homOfSubcomplexes (SSet.Subcomplex.range Y.hom)
      (SSet.Subcomplex.range f.right)) from
    MorphismProperty.arrow_mk_iso_iff _
      (((chainComplexFunctor C).obj R).mapArrow.mapIso this)
  refine Arrow.isoMk
    (SSetPair.isoMk
      (asIso (SSet.Subcomplex.toRange (f.left ≫ Y.hom)) ≪≫
      SSet.Subcomplex.eqToIso h₂) (asIso (SSet.Subcomplex.toRange (f.right)) :) ?_)
    (SSetPair.isoMk (asIso (SSet.Subcomplex.toRange Y.hom) :) (Iso.refl _))
  dsimp
  rw [← cancel_mono (SSet.Subcomplex.ι _)]
  simpa using f.w

end SSetPair
