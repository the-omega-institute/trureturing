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
The imported Mathlib construction descends natural transformations through
quasi-isomorphism localization and supplies their shift compatibility and
complex-representative formula.
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

/- Degreewise composition comparison under preservation of zero morphisms. -/
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
instance instCommShiftHomologicalComplexIntUpMapHomologicalComplex_d5
    (τ : F ⟶ G) : NatTrans.CommShift (τ.mapHomologicalComplex (.up ℤ)) ℤ where
  shift_comm n := by
    ext K i
    simp
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

instance instHomFunctorIsoId_d5 :
    NatTrans.CommShift (Lifting.iso L W L (𝟭 D)).hom A := by
  dsimp [Lifting.iso]
  infer_instance


end NatTrans.CommShift
end LocalizedTransformations

/- The imported `NatTrans.mapDerivedCategory` uses `Localization.liftNatTrans`
on the degreewise transformation whiskered with `DerivedCategory.Q`.
`NatTrans.CommShift.liftNatTrans` supplies its shift compatibility, and
`NatTrans.mapDerivedCategory_app_Q_obj` gives its value on every complex. -/

end CategoryTheory
