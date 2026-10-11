/- GID: D5/S3/HomologicalAlgebra/Solid/OriginalDerived
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/OriginalDerived
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.RealizedAdjunction
import D5.S3.HomologicalAlgebra.Solid.AdjunctionKanExtension

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
Exact original derived-constructor declarations of LeanEval
`derived_solidification_free_CW_homology`, using the genuine unbounded
D(Solid) realization and accepted exact Kan proof. No derived-existence,
resolution, full-faithfulness or adjunction hypothesis is introduced.
The original ordinary declarations are imported unchanged from CWSolid.Early.
Challenge attribution: dagurtomas/LeanCondensed at
339ecc99fdc4bdb68ef248c16da0148dce61a639 (Apache-2.0).
-/

noncomputable section
open CategoryTheory
namespace LightCondensed.Solid

/-- **Hole 4.** The derived solidification functor. -/
def derivedSolidification : DLightCondAb ⥤ DSolid := realizedDerivedSolidification

/-- **Hole 5.** The comparison map from derived solidification to degreewise solidification. -/
def derivedSolidificationCounit :
    DerivedCategory.Q ⋙ derivedSolidification ⟶
      solidification.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  adjunctionDerivedCounit realizedDerivedSolidificationAdjunction

/-- **Hole 6.** Derived solidification, together with the comparison map of the previous hole, is
the total left derived functor of degreewise solidification followed by localization. -/
instance derivedSolidification_isLeftDerivedFunctor :
    derivedSolidification.IsLeftDerivedFunctor derivedSolidificationCounit
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ)) :=
  adjunction_isLeftDerivedFunctor realizedDerivedSolidificationAdjunction

/-- The inclusion of solid abelian groups, applied degreewise to cochain complexes. -/
abbrev inclusionComplexes :
    CochainComplex Solid ℤ ⥤ CochainComplex LightCondAb ℤ :=
  isSolid.ι.mapHomologicalComplex (ComplexShape.up ℤ)



/-- The derived inclusion is induced by applying the inclusion degreewise to complexes. -/
abbrev derivedInclusionFactors :
    DerivedCategory.Q ⋙ derivedInclusion ≅ inclusionComplexes ⋙ DerivedCategory.Q :=
  isSolid.ι.mapDerivedCategoryFactors

/-- The comparison map exhibiting `derivedInclusion` as a right derived functor of the degreewise
inclusion. -/
abbrev derivedInclusionComparison :
    inclusionComplexes ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ derivedInclusion :=
  derivedInclusionFactors.inv

/-- The exact derived inclusion is the right derived functor of the degreewise inclusion. -/
instance derivedInclusion_isRightDerivedFunctor :
    derivedInclusion.IsRightDerivedFunctor derivedInclusionComparison
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)) derivedInclusion
    derivedInclusionFactors

/-- **Hole 7.** The derived solidification adjunction: derived solidification is left adjoint to
the derived inclusion. -/
def derivedSolidificationAdjunction : derivedSolidification ⊣ derivedInclusion :=
  realizedDerivedSolidificationAdjunction












/-- Actual existence for all quasi-isomorphisms of arbitrary unbounded complexes. -/
instance solidification_hasLeftDerivedFunctor :
    (solidification.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ)) :=
  adjunction_hasLeftDerivedFunctor derivedSolidificationAdjunction

/-- The original counit has the literal right-Kan-extension universal property. -/
theorem derivedSolidification_isRightKanExtension :
    derivedSolidification.IsRightKanExtension derivedSolidificationCounit :=
  adjunction_isRightKanExtension derivedSolidificationAdjunction

end LightCondensed.Solid

#print axioms LightCondensed.Solid.solidification
#print axioms LightCondensed.Solid.solidification_additive
#print axioms LightCondensed.Solid.solidificationAdjunction
#print axioms LightCondensed.Solid.derivedSolidification
#print axioms LightCondensed.Solid.derivedSolidificationCounit
#print axioms LightCondensed.Solid.derivedSolidification_isLeftDerivedFunctor
#print axioms LightCondensed.Solid.derivedInclusion_isRightDerivedFunctor
#print axioms LightCondensed.Solid.derivedSolidificationAdjunction
#print axioms LightCondensed.Solid.solidification_hasLeftDerivedFunctor
#print axioms LightCondensed.Solid.derivedSolidification_isRightKanExtension
