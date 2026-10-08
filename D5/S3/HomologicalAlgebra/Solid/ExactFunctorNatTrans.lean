/- GID: D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Natural transformations of exact functors descend to unbounded derived categories. -/

/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

Source: Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean
https://github.com/leanprover-community/mathlib4/blob/5e0c4e5239cb0a2d86d68a884bf52cfd963fce22/Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean
Extracted proved NatTrans construction, its CommShift instance and complex
representative formula, for the native Mathlib db584cd6 pin. Original proof
bodies are preserved; no omitted premise or unproved supplier is introduced.
-/

import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Natural transformations between exact functors descend through the
unbounded quasi-isomorphism localization. The complex-representative formula
is the compatibility used by the solidification mate and cell-locality proofs. -/

universe w₁ w₂
open CategoryTheory Category Limits Localization
variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
namespace CategoryTheory

/- The zero-morphism formulation of Mathlib's composition comparison was
available at the official pin. At the native pin the existing name requires
additivity. This same degreewise natural isomorphism retains the original
zero-morphism interface without strengthening the adjunction theorem. -/
section DegreewiseComposition
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
@[simps!]
def Functor.mapHomologicalComplexCompIsoZero (e : F ⋙ G ≅ H)
    {ι : Type*} (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅ H.mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex e c
end DegreewiseComposition

/- The following proved degreewise natural-transformation compatibility is
extracted from Mathlib/Algebra/Homology/HomotopyCategory/Shift.lean at
5e0c4e5239cb0a2d86d68a884bf52cfd963fce22. -/
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
section DegreewiseTransformations
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
instance (τ : F ⟶ G) : NatTrans.CommShift (τ.mapHomologicalComplex (.up ℤ)) ℤ where
  shift_comm n := by
    ext K i
    simp
    change 𝟙 (F.obj (K.X (i + n))) ≫ τ.app (K.X (i + n)) =
      τ.app (K.X (i + n)) ≫ 𝟙 (G.obj (K.X (i + n)))
    simp only [Category.id_comp, Category.comp_id]
end DegreewiseTransformations

/- The following proved compatibility lemma is extracted from
Mathlib/CategoryTheory/Shift/Localization.lean at the same exact 5e0c4e
commit. Copyright (c) 2023 Joël Riou, Apache-2.0; Authors: Joël Riou. -/
section LocalizedTransformations
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  (A : Type*) [AddMonoid A] [HasShift C A]
namespace NatTrans.CommShift

open Localization

variable [HasShift D A] [L.CommShift A]

instance : NatTrans.CommShift (Lifting.iso L W L (𝟭 D)).hom A := by
  dsimp [Lifting.iso]
  infer_instance

instance liftNatTrans [HasShift E A]
    (F₁ F₂ : C ⥤ E) [F₁.CommShift A] [F₂.CommShift A]
    (F₁' F₂' : D ⥤ E) [F₁'.CommShift A] [F₂'.CommShift A]
    [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    [NatTrans.CommShift (Lifting.iso L W F₁ F₁').hom A]
    [NatTrans.CommShift (Lifting.iso L W F₂ F₂').hom A]
    (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ A] :
    NatTrans.CommShift (Localization.liftNatTrans L W F₁ F₂ F₁' F₂' τ) A where
  shift_comm m :=
    Localization.natTrans_ext L W (fun X ↦ by
      simp [← cancel_epi (F₁'.map ((L.commShiftIso m).hom.app X)),
        shift_app, Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app,
        ← Functor.map_comp_assoc])

end NatTrans.CommShift
end LocalizedTransformations
namespace NatTrans

variable {F : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {G : C₁ ⥤ C₂} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- A natural transformation between exact functors between abelian categories
induces a natural transformation between the corresponding induced functors
on the derived categories. -/
noncomputable def mapDerivedCategory (τ : F ⟶ G) : F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) _ _ _ _
      (Functor.whiskerRight (τ.mapHomologicalComplex _) DerivedCategory.Q)

instance (τ : F ⟶ G) : NatTrans.CommShift τ.mapDerivedCategory ℤ := by
  letI : NatTrans.CommShift (Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory).hom ℤ := by
    change NatTrans.CommShift F.mapDerivedCategoryFactors.hom ℤ
    infer_instance
  letI : NatTrans.CommShift (Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (.up ℤ))
      (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) G.mapDerivedCategory).hom ℤ := by
    change NatTrans.CommShift G.mapDerivedCategoryFactors.hom ℤ
    infer_instance
  exact NatTrans.CommShift.liftNatTrans ..

@[reassoc]
lemma mapDerivedCategory_app_Q_obj (τ : F ⟶ G) (X : CochainComplex C₁ ℤ) :
    τ.mapDerivedCategory.app (DerivedCategory.Q.obj X) =
    F.mapDerivedCategoryFactors.hom.app X ≫
      DerivedCategory.Q.map ((τ.mapHomologicalComplex (.up ℤ)).app X) ≫
        G.mapDerivedCategoryFactors.inv.app X :=
  liftNatTrans_app ..


end NatTrans

end CategoryTheory
