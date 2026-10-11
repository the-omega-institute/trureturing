/- GID: D5/S3/HomologicalAlgebra/Solid/DerivedRealization
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/DerivedRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.DerivedHomFiltration
import D5.S3.HomologicalAlgebra.Solid.FreeGeneratorAugmentation
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
Realization in the protected D(Solid) of every object of the actual
derived-local category. The concrete free-generator kernel resolution,
finite layers, lower telescope and good upper telescope supply the
unbounded essential-image argument. Neither solid homology nor the
ordinary reflection is treated as a realization theorem.
Research: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry,
Theorem 3.3.1 and Lemma 3.3.2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits HomologicalComplex Pretriangulated LightCondensed
open scoped ZeroObject

namespace LightCondensed.Solid
open CWSolid

local instance : derivedInclusion.Full := derivedInclusionFullyFaithful.full
local instance : derivedInclusion.Faithful := derivedInclusionFullyFaithful.faithful
local instance : derivedInclusionToLocal.Full :=
  Functor.Full.of_comp_faithful_iso derivedInclusionToLocalCompIso
local instance : derivedInclusionToLocal.Faithful :=
  Functor.Faithful.of_comp_iso derivedInclusionToLocalCompIso
local instance : derivedInclusionToLocal.CommShift ℤ := by
  unfold derivedInclusionToLocal
  infer_instance
local instance : derivedInclusionToLocal.IsTriangulated := by
  unfold derivedInclusionToLocal
  infer_instance
local instance : solidDerivedLocalReflection.IsLeftAdjoint :=
  solidDerivedLocalReflectionAdjunction.isLeftAdjoint
local instance : solidDerivedLocalReflection.Additive :=
  solidDerivedLocalReflectionAdjunction.left_adjoint_additive
local instance : Reflective solidDerivedLocal.ι where
  L := solidDerivedLocalReflection
  adj := solidDerivedLocalReflectionAdjunction

local instance ambientComplexSmallCoproducts (I : Type) :
    HasColimitsOfShape (Discrete I) (CochainComplex LightCondAb ℤ) where
  has_colimit F := by
    haveI : HasColimitsOfShape (Discrete I) LightCondAb :=
      HasColimitsOfSize.has_colimits_of_shape (C := LightCondAb) (J := Discrete I)
    haveI (n : ℤ) : HasColimit (F ⋙ eval LightCondAb (.up ℤ) n) := inferInstance
    exact ⟨⟨⟨HomologicalComplex.coconeOfHasColimitEval F,
      HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩

/-- Actual coproducts of arbitrary derived objects are obtained from
complex representatives and the already proved coproduct witnesses. -/
instance derivedSolid_hasSmallCoproducts (I : Type) :
    HasColimitsOfShape (Discrete I) DSolid where
  has_colimit F := by
    let K i := DerivedCategory.Q.objPreimage (F.obj ⟨i⟩)
    let D := Discrete.functor (fun i => DerivedCategory.Q.obj (K i))
    haveI : HasColimit D := ⟨⟨⟨_, derivedCoproductIsColimit K⟩⟩⟩
    exact hasColimit_of_iso (Discrete.natIso (F := F) (G := D)
      (fun j => (DerivedCategory.Q.objObjPreimageIso (F.obj j)).symm))

instance derivedLightCondAb_hasSmallCoproducts (I : Type) :
    HasColimitsOfShape (Discrete I) DLightCondAb where
  has_colimit F := by
    let K i := DerivedCategory.Q.objPreimage (F.obj ⟨i⟩)
    let D := Discrete.functor (fun i => DerivedCategory.Q.obj (K i))
    haveI : HasColimit D := ⟨⟨⟨_, derivedCoproductIsColimit K⟩⟩⟩
    exact hasColimit_of_iso (Discrete.natIso (F := F) (G := D)
      (fun j => (DerivedCategory.Q.objObjPreimageIso (F.obj j)).symm))

instance derivedLocal_hasSmallCoproducts (I : Type) :
    HasColimitsOfShape (Discrete I) solidDerivedLocal.FullSubcategory :=
  hasColimitsOfShape_of_reflective solidDerivedLocal.ι

/-- The protected inclusion preserves these actual arbitrary derived
coproducts, by transport from its verified complex-coproduct comparison. -/
instance derivedInclusion_preservesSmallCoproducts (I : Type) :
    PreservesColimitsOfShape (Discrete I) derivedInclusion where
  preservesColimit {F} := by
    let K i := DerivedCategory.Q.objPreimage (F.obj ⟨i⟩)
    haveI := derivedInclusion_preservesComplexCoproduct K
    exact preservesColimit_of_iso_diagram derivedInclusion
      (Discrete.natIso
        (F := Discrete.functor (fun i => DerivedCategory.Q.obj (K i))) (G := F)
        (fun j => DerivedCategory.Q.objObjPreimageIso (F.obj j)))

instance derivedInclusionToLocal_preservesSmallCoproducts (I : Type) :
    PreservesColimitsOfShape (Discrete I) derivedInclusionToLocal := by
  haveI : PreservesColimitsOfShape (Discrete I)
      (derivedInclusionToLocal ⋙ solidDerivedLocal.ι) :=
    preservesColimitsOfShape_of_natIso derivedInclusionToLocalCompIso.symm
  exact preservesColimitsOfShape_of_reflects_of_preserves
    derivedInclusionToLocal solidDerivedLocal.ι

/-- Realization is the actual essential image, pulled back along the
genuine unbounded local reflector. -/
private def realized : ObjectProperty DLightCondAb :=
  derivedInclusionToLocal.essImage.inverseImage solidDerivedLocalReflection

private instance realized_closedUnderIsomorphisms :
    realized.IsClosedUnderIsomorphisms := by
  change (derivedInclusionToLocal.essImage.inverseImage
    solidDerivedLocalReflection).IsClosedUnderIsomorphisms
  infer_instance

private instance realized_isTriangulated : realized.IsTriangulated := by
  change (derivedInclusionToLocal.essImage.inverseImage
    solidDerivedLocalReflection).IsTriangulated
  infer_instance

-- Keep the cellular construction out of implicit triangle-object inference.
attribute [irreducible] realized

private theorem realized_complex_coproduct {I : Type}
    (K : I → CochainComplex LightCondAb ℤ)
    (hK : ∀ i, realized (DerivedCategory.Q.obj (K i))) :
    realized (DerivedCategory.Q.obj (∐ K)) := by
  unfold realized
  let c := Cofan.mk (DerivedCategory.Q.obj (∐ K))
    (fun i => DerivedCategory.Q.map (Sigma.ι K i))
  exact derivedInclusionToLocal.essImage.prop_of_isColimit
    (isColimitOfPreserves solidDerivedLocalReflection (derivedCoproductIsColimit K))
    (fun i => by
      change derivedInclusionToLocal.essImage
        (solidDerivedLocalReflection.obj (DerivedCategory.Q.obj (K i.as)))
      simpa only [realized, ObjectProperty.inverseImage] using hK i.as)

private theorem realized_mappingCone {K L : CochainComplex LightCondAb ℤ}
    (f : K ⟶ L) (hK : realized (DerivedCategory.Q.obj K))
    (hL : realized (DerivedCategory.Q.obj L)) :
    realized (DerivedCategory.Q.obj (CochainComplex.mappingCone f)) :=
  realized.ext_of_isTriangulatedClosed₃ _
    (DerivedCategory.mappingCone_triangle_distinguished f) hK hL

private theorem realized_sequence_colimit (F : ℕ ⥤ CochainComplex LightCondAb ℤ)
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ n, realized (DerivedCategory.Q.obj (F.obj n))) :
    realized (DerivedCategory.Q.obj c.pt) := by
  have hsum := realized_complex_coproduct (fun n => F.obj n) hF
  have htel := realized_mappingCone (complexSequenceDifferential F) hsum hsum
  haveI := complexSequenceTelescopeToCocone_quasiIso F c hc
  exact realized.prop_of_iso
    (asIso (DerivedCategory.Q.map (complexSequenceTelescopeToCocone F c))) htel

private theorem realized_free_stalk_zero (s : SmallModel.{0} LightProfinite) :
    realized ((DerivedCategory.singleFunctor LightCondAb 0).obj (freeGeneratorSource s)) := by
  unfold realized
  let S := (equivSmallModel LightProfinite).inverse.obj s
  refine ⟨(DerivedCategory.singleFunctor Solid 0).obj
    (solidification.obj (freeGeneratorSource s)), ⟨?_⟩⟩
  exact solidDerivedLocal.isoMk (localFreeStalkOrdinaryRealizationIso S).symm

private theorem ambientSingle_preservesCoproduct {I : Type}
    (A : I → LightCondAb) (n : ℤ) :
    PreservesColimit (Discrete.functor A) (DerivedCategory.singleFunctor LightCondAb n) := by
  let S := CochainComplex.singleFunctor LightCondAb n
  let K i := S.obj (A i)
  haveI : PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := LightCondAb)) :=
    lightCondensedDerivedQ_preservesCoproduct K
  haveI : PreservesColimit (Discrete.functor A ⋙ S) (DerivedCategory.Q (C := LightCondAb)) :=
    preservesColimit_of_iso_diagram _
      (Discrete.natIso (F := Discrete.functor K) (G := Discrete.functor A ⋙ S)
        (fun j => Iso.refl (S.obj (A j.as))))
  haveI : PreservesColimit (Discrete.functor A) S := by
    dsimp [S, CochainComplex.singleFunctor, CochainComplex.singleFunctors]
    infer_instance
  change PreservesColimit (Discrete.functor A) (S ⋙ DerivedCategory.Q)
  infer_instance

private theorem realized_freeCopower_stalk_zero (X : LightCondAb) :
    realized ((DerivedCategory.singleFunctor LightCondAb 0).obj (freeGeneratorCopower X)) := by
  unfold realized
  let A : FreeGeneratorIndex X → LightCondAb := fun a => freeGeneratorSource a.1
  let S := DerivedCategory.singleFunctor LightCondAb 0
  haveI := ambientSingle_preservesCoproduct A 0
  change derivedInclusionToLocal.essImage (solidDerivedLocalReflection.obj (S.obj (∐ A)))
  exact derivedInclusionToLocal.essImage.prop_of_isColimit
    (isColimitOfPreserves (S ⋙ solidDerivedLocalReflection) (coproductIsCoproduct A))
    (fun j => by
      simpa only [realized, ObjectProperty.inverseImage, Functor.comp_obj,
        Discrete.functor_obj_eq_as, S, A] using realized_free_stalk_zero j.as.1)

private theorem realized_freeCopower_stalk (X : LightCondAb) (i : ℤ) :
    realized ((DerivedCategory.singleFunctor LightCondAb i).obj (freeGeneratorCopower X)) := by
  exact realized.prop_of_iso
    (((DerivedCategory.singleFunctors LightCondAb).shiftIso (-i) i 0 (by simp)).app _)
    (realized.le_shift (-i) _ (realized_freeCopower_stalk_zero X))

private theorem realized_lower_finite (K : CochainComplex LightCondAb ℤ)
    [K.IsStrictlyLE 0]
    (hK : ∀ i, realized ((DerivedCategory.singleFunctor LightCondAb i).obj (K.X i)))
    (m : ℕ) : realized (DerivedCategory.Q.obj (lowerTruncation K m)) := by
  induction m with
  | zero =>
    haveI : (lowerTruncation K 0).IsStrictlyGE 0 := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      simp only [lowerTruncation, Nat.cast_zero, neg_zero,
        if_neg (show ¬ (0 : ℤ) ≤ i by omega)]
      exact Limits.isZero_zero LightCondAb
    haveI : (lowerTruncation K 0).IsStrictlyLE 0 := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      simpa [lowerTruncation, show (0 : ℤ) ≤ i by omega] using
        K.isZero_of_isStrictlyLE 0 i hi
    obtain ⟨M, ⟨e⟩⟩ := CochainComplex.exists_iso_single (lowerTruncation K 0) 0
    let e₀ := (HomologicalComplex.eval LightCondAb (.up ℤ) 0).mapIso
      (X := lowerTruncation K 0) e ≪≫
      singleObjXSelf (.up ℤ) 0 M
    have h₀ : realized ((DerivedCategory.singleFunctor LightCondAb 0).obj
        ((lowerTruncation K 0).X 0)) := by simpa [lowerTruncation] using hK 0
    have hM := realized.prop_of_iso ((DerivedCategory.singleFunctor LightCondAb 0).mapIso e₀) h₀
    exact realized.prop_of_iso (DerivedCategory.Q.mapIso e).symm hM
  | succ m ih =>
    exact realized.ext_of_isTriangulatedClosed₂ _
      (DerivedCategory.triangleOfSES_distinguished (lowerTruncationLayerSequence_shortExact K m))
      ih (hK (-((m + 1 : ℕ) : ℤ)))

private theorem realized_nonpositive (K : CochainComplex LightCondAb ℤ)
    [K.IsStrictlyLE 0]
    (hK : ∀ i, realized ((DerivedCategory.singleFunctor LightCondAb i).obj (K.X i))) :
    realized (DerivedCategory.Q.obj K) :=
  realized_sequence_colimit (lowerTruncationDiagram K) (lowerTruncationCocone K)
    (lowerTruncationCocone_isColimit K) (realized_lower_finite K hK)

private theorem realized_stalk_zero (X : LightCondAb) :
    realized ((DerivedCategory.singleFunctor LightCondAb 0).obj X) := by
  let K := freeGeneratorCochainResolution X
  haveI : K.IsStrictlyLE 0 := freeGeneratorCochainResolution_strictlyLE X
  have hK (i : ℤ) : realized ((DerivedCategory.singleFunctor LightCondAb i).obj (K.X i)) := by
    by_cases hi : i ≤ 0
    · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hi
      obtain ⟨Y, ⟨e⟩⟩ := freeGeneratorCochainResolution_negative_term X n
      exact realized.prop_of_iso
        ((DerivedCategory.singleFunctor LightCondAb (-(n : ℤ))).mapIso e).symm
        (realized_freeCopower_stalk Y (-(n : ℤ)))
    · exact realized.prop_of_isZero
        ((DerivedCategory.singleFunctor LightCondAb i).map_isZero
          (K.isZero_of_isStrictlyLE 0 i (by omega)))
  have h := realized_nonpositive K hK
  haveI := freeGeneratorCochainResolutionπ_quasiIso X
  exact realized.prop_of_iso
    (asIso (DerivedCategory.Q.map (freeGeneratorCochainResolutionπ X))) h

private theorem realized_stalk (X : LightCondAb) (i : ℤ) :
    realized ((DerivedCategory.singleFunctor LightCondAb i).obj X) :=
  realized.prop_of_iso
    (((DerivedCategory.singleFunctors LightCondAb).shiftIso (-i) i 0 (by simp)).app X)
    (realized.le_shift (-i) _ (realized_stalk_zero X))

private theorem realized_boundedAbove (K : CochainComplex LightCondAb ℤ) (b : ℤ)
    [K.IsStrictlyLE b] : realized (DerivedCategory.Q.obj K) := by
  haveI : (K⟦b⟧).IsStrictlyLE 0 := CochainComplex.isStrictlyLE_shift K b b 0 (by simp)
  have h := realized_nonpositive (K⟦b⟧) (fun i => realized_stalk _ i)
  have hs := realized.prop_of_iso ((DerivedCategory.Q.commShiftIso b).app K) h
  exact realized.prop_of_iso ((shiftEquiv DLightCondAb b).unitIso.app (DerivedCategory.Q.obj K)).symm
    (realized.le_shift (-b) _ hs)

/-- Every arbitrary unbounded ambient complex has its actual derived-local
reflection in the essential image of the protected derived inclusion. -/
theorem derivedLocalReflection_realized_complex (K : CochainComplex LightCondAb ℤ) :
    derivedInclusionToLocal.essImage (solidDerivedLocalReflection.obj (DerivedCategory.Q.obj K)) := by
  simpa only [realized, ObjectProperty.inverseImage, upperTruncationCocone] using
    realized_sequence_colimit (upperTruncationDiagram K) (upperTruncationCocone K)
    (upperTruncationCocone_isColimit K)
    (fun m => realized_boundedAbove (K.truncLE (m : ℤ)) (m : ℤ))

/-- The actual unbounded realization theorem, with no generation,
full-faithfulness or realization premise. -/
instance derivedInclusionToLocal_essSurj : derivedInclusionToLocal.EssSurj where
  mem_essImage Y := by
    have hQ : realized (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage Y.obj)) := by
      simpa only [realized, ObjectProperty.inverseImage] using
        derivedLocalReflection_realized_complex (DerivedCategory.Q.objPreimage Y.obj)
    have h : realized Y.obj := realized.prop_of_iso
      (DerivedCategory.Q.objObjPreimageIso Y.obj) hQ
    unfold realized at h
    exact derivedInclusionToLocal.essImage.prop_of_iso
      (asIso (solidDerivedLocalReflectionAdjunction.counit.app Y)) h

/-- The genuine equivalence preserves the exact protected inclusion. -/
def derivedSolidLocalEquivalence : DSolid ≌ solidDerivedLocal.FullSubcategory :=
  letI : derivedInclusionToLocal.IsEquivalence := {}
  derivedInclusionToLocal.asEquivalence

end LightCondensed.Solid

#print axioms LightCondensed.Solid.derivedSolid_hasSmallCoproducts
#print axioms LightCondensed.Solid.derivedLightCondAb_hasSmallCoproducts
#print axioms LightCondensed.Solid.derivedLocal_hasSmallCoproducts
#print axioms LightCondensed.Solid.derivedInclusion_preservesSmallCoproducts
#print axioms LightCondensed.Solid.derivedInclusionToLocal_preservesSmallCoproducts
#print axioms LightCondensed.Solid.derivedLocalReflection_realized_complex
#print axioms LightCondensed.Solid.derivedInclusionToLocal_essSurj
#print axioms LightCondensed.Solid.derivedSolidLocalEquivalence
