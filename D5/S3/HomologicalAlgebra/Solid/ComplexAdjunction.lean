/- GID: D5/S3/HomologicalAlgebra/Solid/ComplexAdjunction
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/ComplexAdjunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.ExactFunctorNatTrans
import D5.S3.HomologicalAlgebra.Solid.Definitions

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace CWSolid

/-- An additive adjunction lifts degreewise to complexes of any shape. -/
def mapHomologicalComplexAdjunction
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    {F : C ⥤ D} {G : D ⥤ C} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (adj : F ⊣ G) {ι : Type*} (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c where
  unit := (Functor.mapHomologicalComplexIdIso C c).inv ≫
    adj.unit.mapHomologicalComplex c ≫
    (Functor.mapHomologicalComplexCompIsoZero (Iso.refl (F ⋙ G)) c).inv
  counit := (Functor.mapHomologicalComplexCompIsoZero (Iso.refl (G ⋙ F)) c).hom ≫
    adj.counit.mapHomologicalComplex c ≫
    (Functor.mapHomologicalComplexIdIso D c).hom
  left_triangle_components K := by
    ext i
    simpa [Functor.mapHomologicalComplexIdIso, Functor.mapHomologicalComplexCompIsoZero,
      NatIso.mapHomologicalComplex, HomologicalComplex.Hom.isoOfComponents,
      Functor.mapHomologicalComplex] using adj.left_triangle_components (K.X i)
  right_triangle_components K := by
    ext i
    simpa [Functor.mapHomologicalComplexIdIso, Functor.mapHomologicalComplexCompIsoZero,
      NatIso.mapHomologicalComplex, HomologicalComplex.Hom.isoOfComponents,
      Functor.mapHomologicalComplex] using adj.right_triangle_components (K.X i)

/-- Exact derived functors commute with homology in every integer degree. -/
def exactDerivedHomologyIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C) (n : ℤ) :
    F.obj ((DerivedCategory.homologyFunctor C n).obj X) ≅
      (DerivedCategory.homologyFunctor D n).obj (F.mapDerivedCategory.obj X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  exact F.mapIso ((DerivedCategory.homologyFunctor C n).mapIso e.symm) ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors C n).app K) ≪≫
    ((K.sc n).mapHomologyIso F).symm ≪≫
    ((DerivedCategory.homologyFunctorFactors D n).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm ≪≫
    (DerivedCategory.homologyFunctor D n).mapIso (F.mapDerivedCategoryFactors.app K).symm ≪≫
    (DerivedCategory.homologyFunctor D n).mapIso (F.mapDerivedCategory.mapIso e)

end CWSolid

namespace LightCondensed.Solid

/-- The exact derived inclusion remains a right-derived functor after any postcomposition.
This discharges the right-derived composite obligation in `Adjunction.derived`; it requires
no existence or adjunction assumption for derived solidification. -/
instance derivedInclusion_postcomp_isRightDerivedFunctor
    {E : Type*} [Category* E] (G : DLightCondAb ⥤ E) :
    (derivedInclusion ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight isSolid.ι.mapDerivedCategoryFactors.inv G ≫
        (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)) := by
  exact Functor.isRightDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)) (derivedInclusion ⋙ G)
    ((Functor.associator DerivedCategory.Q derivedInclusion G).symm ≪≫
      Functor.isoWhiskerRight isSolid.ι.mapDerivedCategoryFactors G)

end LightCondensed.Solid
