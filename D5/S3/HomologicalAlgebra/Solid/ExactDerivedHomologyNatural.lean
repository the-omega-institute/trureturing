/- GID: D5/S3/HomologicalAlgebra/Solid/ExactDerivedHomologyNatural
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/ExactDerivedHomologyNatural
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

noncomputable section
open CategoryTheory CategoryTheory.Category Limits
namespace CWSolid
set_option backward.isDefEq.respectTransparency false

section
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The existing exact homology comparison on complexes, naturally in the complex. -/
def exactComplexHomologyNatIso (n : ℤ) :
    HomologicalComplex.homologyFunctor C (.up ℤ) n ⋙ F ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor D (.up ℤ) n :=
  NatIso.ofComponents (fun K => ((K.sc n).mapHomologyIso F).symm) (fun f => by
    exact ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map f) F)

private def exactDerivedHomologyPreIso (n : ℤ) :
    DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C n ⋙ F) ≅
      DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n) F ≪≫
    exactComplexHomologyNatIso F n ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors D n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors.symm _ ≪≫
    Functor.associator _ _ _

/-- Naturality of exact derived homology, including every localized morphism. -/
def exactDerivedHomologyNatIso (n : ℤ) :
    DerivedCategory.homologyFunctor C n ⋙ F ≅
      F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n :=
  (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
    (HomologicalComplex.quasiIso C (.up ℤ)) D).preimageIso
      (exactDerivedHomologyPreIso F n)

@[reassoc]
lemma exactDerivedHomologyNatIso_hom_app_Q (n : ℤ) (K : CochainComplex C ℤ) :
    (exactDerivedHomologyNatIso F n).hom.app (DerivedCategory.Q.obj K) =
      F.map ((DerivedCategory.homologyFunctorFactors C n).hom.app K) ≫
        ((K.sc n).mapHomologyIso F).inv ≫
        (DerivedCategory.homologyFunctorFactors D n).inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (DerivedCategory.homologyFunctor D n).map (F.mapDerivedCategoryFactors.inv.app K) := by
  have h := (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
    (HomologicalComplex.quasiIso C (.up ℤ)) D).map_preimage
      (exactDerivedHomologyPreIso F n).hom
  simpa [exactDerivedHomologyNatIso, exactDerivedHomologyPreIso,
    exactComplexHomologyNatIso] using congr_app h K


end
end CWSolid
