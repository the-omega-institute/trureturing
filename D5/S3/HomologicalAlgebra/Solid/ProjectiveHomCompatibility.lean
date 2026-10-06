/- GID: D5/S3/HomologicalAlgebra/Solid/ProjectiveHomCompatibility
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/ProjectiveHomCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.ProjectiveSingleHom
import D5.S3.HomologicalAlgebra.Solid.ExactDerivedHomologyNatural

noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive Limits HomologicalComplex
namespace CWSolid
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section
variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

@[reassoc]
lemma derivedSingleHomologyMap_single_precomp {A B : C} (t : A ⟶ B) (n : ℤ)
    (Y : DerivedCategory C) (f : (DerivedCategory.singleFunctor C n).obj B ⟶ Y) :
    derivedSingleHomologyMap A n Y ((DerivedCategory.singleFunctor C n).map t ≫ f) =
      t ≫ derivedSingleHomologyMap B n Y f := by
  let e : DerivedCategory.singleFunctor C n ⋙ DerivedCategory.homologyFunctor C n ≅
      𝟭 C :=
    (Functor.associator (CochainComplex.singleFunctor C n) DerivedCategory.Q
      (DerivedCategory.homologyFunctor C n)) ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors C n) ≪≫
      homologyFunctorSingleIso C (.up ℤ) n
  have he (X : C) : e.inv.app X = (derivedSingleHomologyIso X n).inv := by
    simp [e, derivedSingleHomologyIso, homologyFunctorSingleIso]
  have ht := e.inv.naturality t
  simp only [Functor.id_map, Functor.comp_map, he] at ht
  dsimp [derivedSingleHomologyMap]
  rw [Functor.map_comp, ← Category.assoc, ← ht, Category.assoc]

end

section
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

@[reassoc]
lemma mapHomologyIso_homologyπ (S : ShortComplex C) :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [S.homologyData.left.mapHomologyIso_eq F,
    S.homologyData.left.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  simp only [ShortComplex.LeftHomologyData.map_π]
  rw [← F.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv, F.map_comp]

@[reassoc]
lemma exactComplexHomology_single (A : C) (n : ℤ) :
    ((exactComplexHomologyNatIso F n).hom.app
      ((CochainComplex.singleFunctor C n).obj A)) ≫
      homologyMap ((singleMapHomologicalComplex F (.up ℤ) n).hom.app A) n ≫
      (singleObjHomologySelfIso (.up ℤ) n (F.obj A)).hom =
    F.map (singleObjHomologySelfIso (.up ℤ) n A).hom := by
  with_unfolding_all
  let S := (HomologicalComplex.single C (.up ℤ) n).obj A
  let T := (F.mapHomologicalComplex (.up ℤ)).obj S
  let v := (singleMapHomologicalComplex F (.up ℤ) n).hom.app A
  change ((S.sc n).mapHomologyIso F).inv ≫ homologyMap v n ≫ _ = _
  rw [← cancel_epi ((S.sc n).mapHomologyIso F).hom, Iso.hom_inv_id_assoc]
  rw [← cancel_epi (T.homologyπ n), homologyπ_naturality_assoc]
  dsimp only [Functor.comp_obj]
  rw [homologyπ_singleObjHomologySelfIso_hom,
    singleObjCyclesSelfIso_hom, ← Category.assoc, cyclesMap_i]
  dsimp only [v]
  rw [singleMapHomologicalComplex_hom_app_self]
  simp only [Category.assoc, Iso.inv_hom_id, comp_id]
  change T.iCycles n ≫ F.map (singleObjXSelf (.up ℤ) n A).hom =
    ((S.sc n).map F).homologyπ ≫ ((S.sc n).mapHomologyIso F).hom ≫
      F.map (singleObjHomologySelfIso (.up ℤ) n A).hom
  rw [mapHomologyIso_homologyπ_assoc]
  have hπ : (S.sc n).homologyπ ≫ (singleObjHomologySelfIso (.up ℤ) n A).hom =
      S.iCycles n ≫ (singleObjXSelf (.up ℤ) n A).hom :=
    homologyπ_singleObjHomologySelfIso_hom (.up ℤ) n A
  rw [← F.map_comp, hπ, F.map_comp]
  have hi : ((S.sc n).mapCyclesIso F).hom ≫ F.map (S.iCycles n) = T.iCycles n :=
    ShortComplex.mapCyclesIso_hom_iCycles (S.sc n) F
  exact (congrArg (fun u => u ≫ F.map (singleObjXSelf (.up ℤ) n A).hom) hi.symm).trans
    (Category.assoc _ _ _)

@[reassoc]
lemma exactDerivedHomology_single (A : C) (n : ℤ) :
    (exactDerivedHomologyNatIso F n).hom.app
      ((DerivedCategory.singleFunctor C n).obj A) ≫
      (DerivedCategory.homologyFunctor D n).map
        ((F.mapDerivedCategorySingleFunctor n).hom.app A) ≫
      (derivedSingleHomologyIso (F.obj A) n).hom =
    F.map (derivedSingleHomologyIso A n).hom := by
  with_unfolding_all
  change (exactDerivedHomologyNatIso F n).hom.app
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C n).obj A)) ≫ _ = _
  rw [exactDerivedHomologyNatIso_hom_app_Q]
  have hsingle :
      ((sc ((HomologicalComplex.single C (.up ℤ) n).obj A) n).mapHomologyIso F).inv ≫
        homologyMap ((singleMapHomologicalComplex F (.up ℤ) n).hom.app A) n ≫
        (singleObjHomologySelfIso (.up ℤ) n (F.obj A)).hom =
      F.map (singleObjHomologySelfIso (.up ℤ) n A).hom :=
    exactComplexHomology_single F A n
  simp [Functor.mapDerivedCategorySingleFunctor, derivedSingleHomologyIso,
    DerivedCategory.singleFunctorIsoCompQ, Functor.map_comp,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    ← (DerivedCategory.homologyFunctorFactors D n).inv.naturality_assoc]
  erw [← (DerivedCategory.homologyFunctor D n).map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  simpa only [Functor.map_comp, Category.assoc] using congrArg (fun u =>
    F.map ((DerivedCategory.homologyFunctorFactors C n).hom.app
      ((HomologicalComplex.single C (.up ℤ) n).obj A)) ≫ u) hsingle

@[reassoc]
lemma derivedSingleHomologyMap_exact (A : C) (n : ℤ) (Y : DerivedCategory C)
    (f : (DerivedCategory.singleFunctor C n).obj A ⟶ Y) :
    derivedSingleHomologyMap (F.obj A) n (F.mapDerivedCategory.obj Y)
      ((F.mapDerivedCategorySingleFunctor n).inv.app A ≫ F.mapDerivedCategory.map f) =
    F.map (derivedSingleHomologyMap A n Y f) ≫
      (exactDerivedHomologyNatIso F n).hom.app Y := by
  have hs := exactDerivedHomology_single F A n
  have hi : (derivedSingleHomologyIso (F.obj A) n).inv ≫
      (DerivedCategory.homologyFunctor D n).map
        ((F.mapDerivedCategorySingleFunctor n).inv.app A) =
    F.map (derivedSingleHomologyIso A n).inv ≫
      (exactDerivedHomologyNatIso F n).hom.app
        ((DerivedCategory.singleFunctor C n).obj A) := by
    apply (cancel_epi (F.map (derivedSingleHomologyIso A n).hom)).1
    calc
      F.map (derivedSingleHomologyIso A n).hom ≫
          (derivedSingleHomologyIso (F.obj A) n).inv ≫
          (DerivedCategory.homologyFunctor D n).map
            ((F.mapDerivedCategorySingleFunctor n).inv.app A) =
        ((exactDerivedHomologyNatIso F n).hom.app
          ((DerivedCategory.singleFunctor C n).obj A) ≫
          (DerivedCategory.homologyFunctor D n).map
            ((F.mapDerivedCategorySingleFunctor n).hom.app A) ≫
          (derivedSingleHomologyIso (F.obj A) n).hom) ≫
          (derivedSingleHomologyIso (F.obj A) n).inv ≫
          (DerivedCategory.homologyFunctor D n).map
            ((F.mapDerivedCategorySingleFunctor n).inv.app A) := by rw [hs]
      _ = (exactDerivedHomologyNatIso F n).hom.app
          ((DerivedCategory.singleFunctor C n).obj A) := by
        simp [Category.assoc, ← Functor.map_comp]
      _ = F.map (derivedSingleHomologyIso A n).hom ≫
          F.map (derivedSingleHomologyIso A n).inv ≫
          (exactDerivedHomologyNatIso F n).hom.app
            ((DerivedCategory.singleFunctor C n).obj A) := by
        simp [← F.map_comp_assoc]
  dsimp [derivedSingleHomologyMap]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, hi, Category.assoc]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
    congrArg (fun u => F.map (derivedSingleHomologyIso A n).inv ≫ u)
      ((exactDerivedHomologyNatIso F n).hom.naturality f).symm


end
end CWSolid
