/- GID: D5/S3/HomologicalAlgebra/Solid/DerivedGeneratorComparison
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/DerivedGeneratorComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.MeasureOrdinaryReflection
import D5.S3.HomologicalAlgebra.Solid.Supplier.FreeAugmentation
import D5.S3.HomologicalAlgebra.Solid.Supplier.SingularProjective
import D5.S3.HomologicalAlgebra.Solid.ComplexAdjunction
import D5.S3.HomologicalAlgebra.Solid.ProjectiveHomCompatibility

/-!
Exact supplier isolation for the constructor closure. The frozen Localizing
module also imports a second copy of the already imported homotopy adjunction.
Only its actually needed projectivity declarations are extracted verbatim,
followed by the verbatim accepted ProjectiveGeneratorHom proof bodies.
Source/license: CWComparison.Localizing, copyright (c) 2026, Apache 2.0
(src/licenses/LICENSE.LeanCondensed), frozen simplex review; and immutable
accepted projective-checkpoint/CWSolid/ProjectiveGeneratorHom.lean, Apache 2.0.
Exact source identities and unchanged extraction bodies are recorded in
 tmp/projective-hom-isolation.json. The accepted original sources/oleans remain
unchanged. No declaration body or target interface is replaced by an assumption.
-/

noncomputable section
open CategoryTheory Limits LightCondensed MonoidalCategory MonoidalClosed Opposite
open LightProfinite OnePoint

namespace CWComparison

/-- Continuous maps into the topological point form the terminal light condensed set. -/
def pointCondTerminal : IsTerminal point.toLightCondSet := by
  letI : topCatToLightCondSet.IsRightAdjoint :=
    LightCondSet.topCatAdjunction.isRightAdjoint
  exact TopCat.isTerminalPUnit.isTerminalObj topCatToLightCondSet _

/-- The actual monoidal unit is discrete integers, with no change of solidness. -/
def tensorUnitIsoInt : 𝟙_ LightCondAb ≅
    (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) :=
  Functor.Monoidal.εIso (free ℤ) ≪≫
    (free ℤ).mapIso (pointCondTerminal.uniqueUpToIso
      SemiCartesianMonoidalCategory.isTerminalTensorUnit).symm ≪≫ freePointIsoInt

instance tensorUnit_projective : Projective (𝟙_ LightCondAb) :=
  Projective.of_iso tensorUnitIsoInt.symm (discrete_projective (ModuleCat.of ℤ ℤ))

/-- Internal projectivity implies actual projectivity here because the tensor unit
is projective. This uses the proved epimorphism preservation at the point. -/
theorem projective_of_internallyProjective (A : LightCondAb) [InternallyProjective A] :
    Projective A :=
  Projective.of_iso (ρ_ A) ((ihom.adjunction A).map_projective (𝟙_ LightCondAb) inferInstance)

/-- The protected localization source is a genuine projective object. -/
instance P_projective : Projective P := projective_of_internallyProjective P

/-- The free convergent-sequence object is genuinely projective as well. -/
instance freeSequence_projective : Projective ((free ℤ).obj (ℕ∪{∞}).toCondensed) :=
  projective_of_internallyProjective _

end CWComparison

noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive Limits HomologicalComplex

namespace CWSolid
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The natural extension agrees with the independently verified pointwise supplier. -/
lemma exactDerivedHomologyNatIso_app (n : ℤ) (Y : DerivedCategory C) :
    (exactDerivedHomologyNatIso F n).app Y = exactDerivedHomologyIso F Y n := by
  let K := DerivedCategory.Q.objPreimage Y
  let e : DerivedCategory.Q.obj K ≅ Y := DerivedCategory.Q.objObjPreimageIso Y
  apply Iso.ext
  change (exactDerivedHomologyNatIso F n).hom.app Y = _
  rw [← cancel_epi (F.map ((DerivedCategory.homologyFunctor C n).map e.hom))]
  have hn : F.map ((DerivedCategory.homologyFunctor C n).map e.hom) ≫
      (exactDerivedHomologyNatIso F n).hom.app Y =
    (exactDerivedHomologyNatIso F n).hom.app (DerivedCategory.Q.obj K) ≫
      (DerivedCategory.homologyFunctor D n).map (F.mapDerivedCategory.map e.hom) :=
    (exactDerivedHomologyNatIso F n).hom.naturality e.hom
  rw [hn]
  simp only [exactDerivedHomologyIso, K, e, exactDerivedHomologyNatIso_hom_app_Q,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.hom_inv_id]
  with_unfolding_all
    simp only [(DerivedCategory.homologyFunctor C n).map_id, Category.id_comp]

end

abbrev U : LightCondensed.Solid :=
  LightCondensed.Solid.solidification.obj LightCondensed.P

instance U_projective : Projective U :=
  LightCondensed.Solid.solidificationAdjunction.map_projective
    LightCondensed.P inferInstance

open LightCondensed LightCondensed.Solid

/-- The actual ambient projective P computes homology of every unbounded target. -/
def PDerivedHomEquiv (n : ℤ) (Y : DLightCondAb) :
    ((DerivedCategory.singleFunctor LightCondAb n).obj P ⟶ Y) ≃+
      (P ⟶ (DerivedCategory.homologyFunctor LightCondAb n).obj Y) :=
  projectiveSingleHomEquiv P n Y

@[reassoc]
theorem PDerivedHomEquiv_naturality (n : ℤ) {Y Z : DLightCondAb}
    (f : (DerivedCategory.singleFunctor LightCondAb n).obj P ⟶ Y) (g : Y ⟶ Z) :
    PDerivedHomEquiv n Z (f ≫ g) =
      PDerivedHomEquiv n Y f ≫ (DerivedCategory.homologyFunctor LightCondAb n).map g :=
  projectiveSingleHomEquiv_naturality P n f g

/-- The actual reflected projective U computes homology of every unbounded solid target. -/
def UDerivedHomEquiv (n : ℤ) (Y : DSolid) :
    ((DerivedCategory.singleFunctor Solid n).obj U ⟶ Y) ≃+
      (U ⟶ (DerivedCategory.homologyFunctor Solid n).obj Y) :=
  projectiveSingleHomEquiv U n Y

@[reassoc]
theorem UDerivedHomEquiv_naturality (n : ℤ) {Y Z : DSolid}
    (f : (DerivedCategory.singleFunctor Solid n).obj U ⟶ Y) (g : Y ⟶ Z) :
    UDerivedHomEquiv n Z (f ≫ g) =
      UDerivedHomEquiv n Y f ≫ (DerivedCategory.homologyFunctor Solid n).map g :=
  projectiveSingleHomEquiv_naturality U n f g

private def postcompHomAddEquiv {C : Type*} [Category* C] [Preadditive C]
    (A : C) {B D : C} (e : B ≅ D) : (A ⟶ B) ≃+ (A ⟶ D) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp [add_comp]

/-- Exact inclusion and the genuine ordinary adjunction give this Hom computation.
The target is any object of DSolid, without a derived-adjunction premise. -/
def inclusionPDerivedHomEquiv (n : ℤ) (Y : DSolid) :
    ((DerivedCategory.singleFunctor LightCondAb n).obj P ⟶ derivedInclusion.obj Y) ≃+
      (U ⟶ (DerivedCategory.homologyFunctor Solid n).obj Y) :=
  ((PDerivedHomEquiv n (derivedInclusion.obj Y)).trans
    (postcompHomAddEquiv P ((exactDerivedHomologyNatIso isSolid.ι n).app Y).symm)).trans
      (solidificationAdjunction.homAddEquiv P
        ((DerivedCategory.homologyFunctor Solid n).obj Y)).symm

lemma inclusionPDerivedHomEquiv_apply (n : ℤ) (Y : DSolid)
    (f : (DerivedCategory.singleFunctor LightCondAb n).obj P ⟶ derivedInclusion.obj Y) :
    inclusionPDerivedHomEquiv n Y f =
      (solidificationAdjunction.homEquiv P
        ((DerivedCategory.homologyFunctor Solid n).obj Y)).symm
        (PDerivedHomEquiv n (derivedInclusion.obj Y) f ≫
          (exactDerivedHomologyIso isSolid.ι Y n).inv) := by
  rw [← exactDerivedHomologyNatIso_app isSolid.ι n Y]
  rfl

@[reassoc]
theorem inclusionPDerivedHomEquiv_naturality (n : ℤ) {Y Z : DSolid}
    (f : (DerivedCategory.singleFunctor LightCondAb n).obj P ⟶ derivedInclusion.obj Y)
    (g : Y ⟶ Z) :
    inclusionPDerivedHomEquiv n Z (f ≫ derivedInclusion.map g) =
      inclusionPDerivedHomEquiv n Y f ≫ (DerivedCategory.homologyFunctor Solid n).map g := by
  change (solidificationAdjunction.homEquiv P _).symm
    (PDerivedHomEquiv n _ (f ≫ derivedInclusion.map g) ≫
      (exactDerivedHomologyNatIso isSolid.ι n).inv.app Z) =
    (solidificationAdjunction.homEquiv P _).symm
      (PDerivedHomEquiv n _ f ≫
        (exactDerivedHomologyNatIso isSolid.ι n).inv.app Y) ≫
      (DerivedCategory.homologyFunctor Solid n).map g
  have hn : (DerivedCategory.homologyFunctor LightCondAb n).map
      (derivedInclusion.map g) ≫ (exactDerivedHomologyNatIso isSolid.ι n).inv.app Z =
    (exactDerivedHomologyNatIso isSolid.ι n).inv.app Y ≫
      isSolid.ι.map ((DerivedCategory.homologyFunctor Solid n).map g) :=
    (exactDerivedHomologyNatIso isSolid.ι n).inv.naturality g
  rw [PDerivedHomEquiv_naturality, Category.assoc, hn]
  simpa only [← Category.assoc] using
    solidificationAdjunction.homEquiv_naturality_right_symm
      (PDerivedHomEquiv n _ f ≫ (exactDerivedHomologyNatIso isSolid.ι n).inv.app Y)
      ((DerivedCategory.homologyFunctor Solid n).map g)

/-- The actual canonical Hom comparison: the ordinary unit, the exact single comparison,
then the protected derived inclusion applied to the morphism. -/
def solidPHomComparison (n : ℤ) (Y : DSolid)
    (f : (DerivedCategory.singleFunctor Solid n).obj U ⟶ Y) :
    (DerivedCategory.singleFunctor LightCondAb n).obj P ⟶ derivedInclusion.obj Y :=
  (DerivedCategory.singleFunctor LightCondAb n).map (solidificationAdjunction.unit.app P) ≫
    (isSolid.ι.mapDerivedCategorySingleFunctor n).inv.app U ≫ derivedInclusion.map f

@[reassoc]
theorem solidPHomComparison_naturality (n : ℤ) {Y Z : DSolid}
    (f : (DerivedCategory.singleFunctor Solid n).obj U ⟶ Y) (g : Y ⟶ Z) :
    solidPHomComparison n Z (f ≫ g) = solidPHomComparison n Y f ≫ derivedInclusion.map g := by
  simp [solidPHomComparison]

/-- Compatibility with both Hom-to-homology computations and the ordinary adjunction. -/
theorem solidPHomComparison_homology (n : ℤ) (Y : DSolid)
    (f : (DerivedCategory.singleFunctor Solid n).obj U ⟶ Y) :
    inclusionPDerivedHomEquiv n Y (solidPHomComparison n Y f) = UDerivedHomEquiv n Y f := by
  change (solidificationAdjunction.homEquiv P _).symm
    (derivedSingleHomologyMap P n _ (solidPHomComparison n Y f) ≫
      (exactDerivedHomologyNatIso isSolid.ι n).inv.app Y) = _
  rw [solidPHomComparison, derivedSingleHomologyMap_single_precomp]
  change (solidificationAdjunction.homEquiv P _).symm
    ((solidificationAdjunction.unit.app P ≫
      derivedSingleHomologyMap (isSolid.ι.obj U) n (isSolid.ι.mapDerivedCategory.obj Y)
        ((isSolid.ι.mapDerivedCategorySingleFunctor n).inv.app U ≫
          isSolid.ι.mapDerivedCategory.map f)) ≫
      (exactDerivedHomologyNatIso isSolid.ι n).inv.app Y) = _
  rw [derivedSingleHomologyMap_exact isSolid.ι U n Y f]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  change (solidificationAdjunction.homEquiv P _).symm
    (solidificationAdjunction.unit.app P ≫ isSolid.ι.map (UDerivedHomEquiv n Y f)) = _
  rw [← Adjunction.homEquiv_unit, Equiv.symm_apply_apply]

/-- The canonical comparison is an equivalence of Hom groups for these actual sources.
This does not assert full faithfulness of derivedInclusion on other sources. -/
def solidPHomComparisonEquiv (n : ℤ) (Y : DSolid) :
    ((DerivedCategory.singleFunctor Solid n).obj U ⟶ Y) ≃+
      ((DerivedCategory.singleFunctor LightCondAb n).obj P ⟶ derivedInclusion.obj Y) :=
  (UDerivedHomEquiv n Y).trans (inclusionPDerivedHomEquiv n Y).symm

theorem solidPHomComparisonEquiv_apply (n : ℤ) (Y : DSolid)
    (f : (DerivedCategory.singleFunctor Solid n).obj U ⟶ Y) :
    solidPHomComparisonEquiv n Y f = solidPHomComparison n Y f := by
  apply (inclusionPDerivedHomEquiv n Y).injective
  simp [solidPHomComparisonEquiv, solidPHomComparison_homology]

@[reassoc]
theorem solidPHomComparisonEquiv_naturality (n : ℤ) {Y Z : DSolid}
    (f : (DerivedCategory.singleFunctor Solid n).obj U ⟶ Y) (g : Y ⟶ Z) :
    solidPHomComparisonEquiv n Z (f ≫ g) =
      solidPHomComparisonEquiv n Y f ≫ derivedInclusion.map g := by
  simp only [solidPHomComparisonEquiv_apply, solidPHomComparison_naturality]

end CWSolid


/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
The actual protected derived inclusion is fully faithful on every integer
shift of the concrete projective generator U = solidification(P), against
arbitrary unbounded solid targets. The ordinary unit is proved to be a
derived-local universal arrow, using the already compiled canonical measure
isomorphism. This joins the accepted measure and canonical projective-Hom
computations; it assumes neither global derived full faithfulness nor a
derived solidification adjunction. Research: Juan Esteban Rodríguez Camargo,
Notes on Solid Geometry, Theorem 3.3.1.
The projective-Hom supplier is copied unchanged from the immutable accepted
projective-checkpoint, with identities in tmp/projective-hom-reuse.json.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits LightCondensed

namespace LightCondensed.Solid

/-- The canonical P measure comparison is universal against every
unbounded derived-local target, rather than just solid stalks. -/
theorem PToIntegerMeasures_localDerivedPrecomp_bijective
    (Y : DLightCondAb) [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun g :
      (DerivedCategory.singleFunctor LightCondAb 0).obj integerMeasures ⟶ Y =>
      (DerivedCategory.singleFunctor LightCondAb 0).map PToIntegerMeasures ≫ g) := by
  haveI := localPToIntegerMeasures_isIso
  let X := (DerivedCategory.singleFunctor LightCondAb 0).obj P
  let Z : solidDerivedLocal.FullSubcategory := ⟨Y, (show IsIso (solidDerivedEndomorphism.app Y) from inferInstance)⟩
  let j := solidDerivedLocal.ι
  let e : (integerMeasuresDerivedLocal.obj ⟶ Y) ≃ (X ⟶ Y) :=
    (Functor.FullyFaithful.ofFullyFaithful j).homEquiv.symm.trans
      (((asIso localPToIntegerMeasures).symm.homCongr (Iso.refl Z)).trans
        (solidDerivedLocalReflectionAdjunction.homEquiv X Z))
  have heq : (fun g : integerMeasuresDerivedLocal.obj ⟶ Y =>
      (DerivedCategory.singleFunctor LightCondAb 0).map PToIntegerMeasures ≫ g) =
      (fun g => e g) := by
    funext g
    change _ = solidDerivedLocalReflectionAdjunction.unit.app X ≫
      j.map (localPToIntegerMeasures ≫ j.preimage
        (X := integerMeasuresDerivedLocal) (Y := Z) g ≫ 𝟙 Z)
    simp only [Functor.map_comp, Category.comp_id, ← Category.assoc]
    rw [localPToIntegerMeasures_unit, Functor.map_preimage]
  change Function.Bijective (fun g : integerMeasuresDerivedLocal.obj ⟶ Y =>
    (DerivedCategory.singleFunctor LightCondAb 0).map PToIntegerMeasures ≫ g)
  rw [heq]
  exact e.bijective

private theorem solidPUnit_zero_precomp_bijective
    (Y : DLightCondAb) [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun g :
      (DerivedCategory.singleFunctor LightCondAb 0).obj
        (isSolid.ι.obj (solidification.obj P)) ⟶ Y =>
      (DerivedCategory.singleFunctor LightCondAb 0).map
        (solidificationAdjunction.unit.app P) ≫ g) := by
  let F := DerivedCategory.singleFunctor LightCondAb 0
  let e := F.mapIso (isSolid.ι.mapIso solidPIntegerMeasuresIso)
  have he : F.map (solidificationAdjunction.unit.app P) ≫ e.hom =
      F.map PToIntegerMeasures := by
    simpa only [e, Functor.mapIso_hom, solidPIntegerMeasuresIso,
      asIso_hom, ← Functor.map_comp] using congrArg F.map solidPToIntegerMeasures_unit
  have h := PToIntegerMeasures_localDerivedPrecomp_bijective Y
  constructor
  · intro f g hfg
    apply (cancel_epi e.inv).1
    apply h.injective
    rw [← he]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hfg
  · intro f
    obtain ⟨g, hg⟩ := h.surjective f
    refine ⟨e.hom ≫ g, ?_⟩
    change F.map (solidificationAdjunction.unit.app P) ≫ (e.hom ≫ g) = f
    rw [← Category.assoc, he]
    exact hg

private theorem shifted_arrow_precomp_bijective
    {C : Type*} [Category* C] [HasShift C ℤ]
    {A B Y : C} (f : A ⟶ B) (n : ℤ)
    (hf : Function.Bijective (fun g : B ⟶ Y⟦-n⟧ => f ≫ g)) :
    Function.Bijective (fun g : B⟦n⟧ ⟶ Y => f⟦n⟧' ≫ g) := by
  let adj := (shiftEquiv C n).toAdjunction
  let eA := adj.homEquiv A Y
  let eB := adj.homEquiv B Y
  have he (g : B⟦n⟧ ⟶ Y) : eA (f⟦n⟧' ≫ g) = f ≫ eB g :=
    adj.homEquiv_naturality_left f g
  constructor
  · intro u v huv
    apply eB.injective
    apply hf.injective
    change f ≫ eB u = f ≫ eB v
    rw [← he, ← he]
    exact congrArg eA huv
  · intro u
    obtain ⟨v, hv⟩ := hf.surjective (eA u)
    refine ⟨eB.symm v, eA.injective ?_⟩
    change eA (f⟦n⟧' ≫ eB.symm v) = eA u
    rw [he, eB.apply_symm_apply]
    exact hv

/-- The exact ordinary unit is a derived universal arrow for P in EVERY
integer degree and against arbitrary unbounded derived-local targets. -/
theorem solidPUnit_localDerivedPrecomp_bijective (n : ℤ)
    (Y : DLightCondAb) [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun g :
      (DerivedCategory.singleFunctor LightCondAb n).obj
        (isSolid.ι.obj (solidification.obj P)) ⟶ Y =>
      (DerivedCategory.singleFunctor LightCondAb n).map
        (solidificationAdjunction.unit.app P) ≫ g) := by
  haveI : IsIso (solidDerivedEndomorphism.app (Y⟦n⟧)) := by
    haveI : IsIso ((MonoidalClosed.pre oneMinusShift).mapDerivedCategory.app Y) :=
      (inferInstance : IsIso (solidDerivedEndomorphism.app Y))
    unfold solidDerivedEndomorphism
    rw [NatTrans.app_shift _ n Y]
    infer_instance
  let F := DerivedCategory.singleFunctor LightCondAb 0
  let f : F.obj P ⟶ F.obj (isSolid.ι.obj (solidification.obj P)) :=
    F.map (solidificationAdjunction.unit.app P)
  have hzero : Function.Bijective (fun g :
      F.obj (isSolid.ι.obj (solidification.obj P)) ⟶ Y⟦-(-n)⟧ => f ≫ g) := by
    rw [neg_neg]
    exact solidPUnit_zero_precomp_bijective (Y⟦n⟧)
  have hf := shifted_arrow_precomp_bijective (Y := Y) f (-n) hzero
  let e := (DerivedCategory.singleFunctors LightCondAb).shiftIso (-n) n 0 (by simp)
  have he : f⟦-n⟧' ≫ e.hom.app (isSolid.ι.obj (solidification.obj P)) =
      e.hom.app P ≫ (DerivedCategory.singleFunctor LightCondAb n).map
        (solidificationAdjunction.unit.app P) :=
    e.hom.naturality (solidificationAdjunction.unit.app P)
  constructor
  · intro u v huv
    apply (cancel_epi (e.hom.app (isSolid.ι.obj (solidification.obj P)))).1
    apply hf.injective
    change f⟦-n⟧' ≫ (e.hom.app _ ≫ u) = f⟦-n⟧' ≫ (e.hom.app _ ≫ v)
    change (DerivedCategory.singleFunctor LightCondAb n).map
      (solidificationAdjunction.unit.app P) ≫ u =
        (DerivedCategory.singleFunctor LightCondAb n).map
          (solidificationAdjunction.unit.app P) ≫ v at huv
    calc
      f⟦-n⟧' ≫ (e.hom.app _ ≫ u) = e.hom.app P ≫
          ((DerivedCategory.singleFunctor LightCondAb n).map
            (solidificationAdjunction.unit.app P) ≫ u) := by
        rw [← Category.assoc, he, Category.assoc]
      _ = e.hom.app P ≫ ((DerivedCategory.singleFunctor LightCondAb n).map
          (solidificationAdjunction.unit.app P) ≫ v) := congrArg (e.hom.app P ≫ ·) huv
      _ = f⟦-n⟧' ≫ (e.hom.app _ ≫ v) := by
        symm
        rw [← Category.assoc, he, Category.assoc]
  · intro u
    obtain ⟨v, hv⟩ := hf.surjective (e.hom.app P ≫ u)
    refine ⟨e.inv.app _ ≫ v, ?_⟩
    apply (cancel_epi (e.hom.app P)).1
    rw [← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id_app_assoc]
    exact hv

/-- Full faithfulness of the protected derived inclusion on the actual
reflected generator, with every integer shift and arbitrary unbounded targets. -/
theorem derivedInclusion_solidP_map_bijective (n : ℤ) (Y : DSolid) :
    Function.Bijective (fun f :
      (DerivedCategory.singleFunctor Solid n).obj (solidification.obj P) ⟶ Y =>
      derivedInclusion.map f) := by
  haveI := solidDerivedEndomorphism_derivedInclusion_isIso Y
  let e := (isSolid.ι.mapDerivedCategorySingleFunctor n).app (solidification.obj P)
  have hp := solidPUnit_localDerivedPrecomp_bijective n (derivedInclusion.obj Y)
  have hpre : Function.Bijective (fun g :
      derivedInclusion.obj ((DerivedCategory.singleFunctor Solid n).obj
        (solidification.obj P)) ⟶ derivedInclusion.obj Y =>
      (DerivedCategory.singleFunctor LightCondAb n).map
        (solidificationAdjunction.unit.app P) ≫ e.inv ≫ g) := by
    have he : Function.Bijective (fun g :
        derivedInclusion.obj ((DerivedCategory.singleFunctor Solid n).obj
          (solidification.obj P)) ⟶ derivedInclusion.obj Y => e.inv ≫ g) := by
      simpa [Iso.homCongr] using
        (Iso.homCongr e (Iso.refl (derivedInclusion.obj Y))).bijective
    simpa only [Function.comp_def] using hp.comp he
  have hc : Function.Bijective (CWSolid.solidPHomComparison n Y) := by
    have he : (fun f => CWSolid.solidPHomComparisonEquiv n Y f) =
        CWSolid.solidPHomComparison n Y := by
      funext f
      exact CWSolid.solidPHomComparisonEquiv_apply n Y f
    rw [← he]
    exact (CWSolid.solidPHomComparisonEquiv n Y).bijective
  constructor
  · intro f g hfg
    apply hc.injective
    exact congrArg (fun u =>
      (DerivedCategory.singleFunctor LightCondAb n).map
        (solidificationAdjunction.unit.app P) ≫ e.inv ≫ u) hfg
  · intro f
    obtain ⟨g, hg⟩ := hc.surjective
      ((DerivedCategory.singleFunctor LightCondAb n).map
        (solidificationAdjunction.unit.app P) ≫ e.inv ≫ f)
    refine ⟨g, hpre.injective ?_⟩
    exact hg

end LightCondensed.Solid

#print axioms LightCondensed.Solid.PToIntegerMeasures_localDerivedPrecomp_bijective
#print axioms LightCondensed.Solid.solidPUnit_localDerivedPrecomp_bijective
#print axioms LightCondensed.Solid.derivedInclusion_solidP_map_bijective
#print axioms CWComparison.pointCondTerminal
#print axioms CWComparison.tensorUnitIsoInt
#print axioms CWComparison.tensorUnit_projective
#print axioms CWComparison.projective_of_internallyProjective
#print axioms CWComparison.P_projective
#print axioms CWComparison.freeSequence_projective
#print axioms CWSolid.exactDerivedHomologyNatIso_app
#print axioms CWSolid.U
#print axioms CWSolid.U_projective
#print axioms CWSolid.PDerivedHomEquiv
#print axioms CWSolid.PDerivedHomEquiv_naturality
#print axioms CWSolid.UDerivedHomEquiv
#print axioms CWSolid.UDerivedHomEquiv_naturality
#print axioms CWSolid.inclusionPDerivedHomEquiv
#print axioms CWSolid.inclusionPDerivedHomEquiv_apply
#print axioms CWSolid.inclusionPDerivedHomEquiv_naturality
#print axioms CWSolid.solidPHomComparison
#print axioms CWSolid.solidPHomComparison_naturality
#print axioms CWSolid.solidPHomComparison_homology
#print axioms CWSolid.solidPHomComparisonEquiv
#print axioms CWSolid.solidPHomComparisonEquiv_apply
#print axioms CWSolid.solidPHomComparisonEquiv_naturality
