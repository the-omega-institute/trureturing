/- GID: D5/S3/HomologicalAlgebra/Solid/GeneratorConstruction
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/GeneratorConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.DerivedLocalReflection
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Adjunction
import D5.S3.HomologicalAlgebra.Solid.DerivedCoproduct
import Mathlib.CategoryTheory.Limits.FullSubcategory
import D5.S3.HomologicalAlgebra.Solid.FiniteApproximationSquare
import D5.S3.HomologicalAlgebra.Solid.MeasureComparisonConstruction
import Mathlib.CategoryTheory.Retract
import D5.S3.HomologicalAlgebra.Solid.FiniteFreeSolid
import D5.S3.HomologicalAlgebra.Solid.MeasureOrdinaryReflection
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import D5.S3.HomologicalAlgebra.Solid.FreeDetect
import D5.S3.HomologicalAlgebra.Solid.UnboundedTruncationColimit
import D5.S3.HomologicalAlgebra.Solid.SequentialPresentation
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-!
The actual ordinary P reflection is imported; new concrete finite-approximation retract,
degree-zero DSolid realization of every reflected free profinite generator,
the actual ordinary generator solidification(P), the exact local reflector,
protected derived coproduct preservation, and the concrete unbounded lower-truncation telescope.
Only new owned construction bodies are assembled to share one import pass.
Passed dependencies are imported unchanged. New proofs: Apache-2.0.
Research: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry,
Theorem 3.3.1 and Lemma 3.3.2. No arbitrary unbounded realization or original
HasLeftDerivedFunctor/derived adjunction is assumed.
-/

/- Owned source component: DerivedLocalTriangulation.lean. -/

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
The actual local reflector is an exact functor on the unbounded derived
category. This gives the shift and triangle structure needed to extend the
concrete generator realization by cones and telescopes. The local category
is still distinct from DSolid; no realization equivalence is assumed.
Research attribution: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry,
Proposition 3.2.5 and Theorem 3.3.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits MonoidalClosed Pretriangulated
open scoped ZeroObject

namespace LightCondensed.Solid

instance solidDerivedLocal_closedUnderIsomorphisms :
    solidDerivedLocal.IsClosedUnderIsomorphisms where
  of_iso e h := (NatTrans.isIso_app_iff_of_iso solidDerivedEndomorphism e).1 h

instance solidDerivedLocal_containsZero : solidDerivedLocal.ContainsZero where
  exists_zero := by
    let h := (ihom P).mapDerivedCategory.map_isZero (isZero_zero DLightCondAb)
    exact ⟨0, isZero_zero _, h.isIso h (solidDerivedEndomorphism.app 0)⟩

instance solidDerivedLocal_stableUnderShift : solidDerivedLocal.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    intro X hX
    haveI : IsIso ((MonoidalClosed.pre oneMinusShift).mapDerivedCategory.app X) := hX
    change IsIso ((MonoidalClosed.pre oneMinusShift).mapDerivedCategory.app (X⟦n⟧))
    rw [NatTrans.app_shift _ n X]
    infer_instance⟩

/-- The actual defining transformation gives a morphism of distinguished
triangles; its compatibility with shifts is inherited from exact derivation. -/
def solidDerivedEndomorphismTriangle (T : Triangle DLightCondAb) :
    (ihom P).mapDerivedCategory.mapTriangle.obj T ⟶
      (ihom P).mapDerivedCategory.mapTriangle.obj T where
  hom₁ := solidDerivedEndomorphism.app T.obj₁
  hom₂ := solidDerivedEndomorphism.app T.obj₂
  hom₃ := solidDerivedEndomorphism.app T.obj₃
  comm₁ := solidDerivedEndomorphism.naturality T.mor₁
  comm₂ := solidDerivedEndomorphism.naturality T.mor₂
  comm₃ := by
    dsimp only [Functor.mapTriangle, Triangle.mk]
    simp only [Category.assoc]
    change (ihom P).mapDerivedCategory.map T.mor₃ ≫
        ((ihom P).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫
          (solidDerivedEndomorphism.app T.obj₁)⟦(1 : ℤ)⟧' =
      solidDerivedEndomorphism.app T.obj₃ ≫
        (ihom P).mapDerivedCategory.map T.mor₃ ≫
          ((ihom P).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app T.obj₁
    unfold solidDerivedEndomorphism
    rw [NatTrans.shift_app_comm
      (MonoidalClosed.pre oneMinusShift).mapDerivedCategory (1 : ℤ) T.obj₁]
    rw [← Category.assoc,
      ((MonoidalClosed.pre oneMinusShift).mapDerivedCategory).naturality T.mor₃,
      Category.assoc]

instance solidDerivedLocal_closedUnderCones : solidDerivedLocal.IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (by
    intro T hT h₁ h₂
    exact isIso₃_of_isIso₁₂ (solidDerivedEndomorphismTriangle T)
      ((ihom P).mapDerivedCategory.map_distinguished T hT)
      ((ihom P).mapDerivedCategory.map_distinguished T hT) h₁ h₂)

instance solidDerivedLocal_closedUnderExtensions :
    solidDerivedLocal.IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance solidDerivedLocal_isTriangulated : solidDerivedLocal.IsTriangulated where

/-- The shift on the genuine reflector is constructed from its proved
adjunction to the exact full local inclusion. -/
instance solidDerivedLocalReflection_commShift :
    solidDerivedLocalReflection.CommShift ℤ :=
  solidDerivedLocalReflectionAdjunction.leftAdjointCommShift ℤ

instance solidDerivedLocalReflectionAdjunction_commShift :
    solidDerivedLocalReflectionAdjunction.CommShift ℤ :=
  solidDerivedLocalReflectionAdjunction.commShift_of_rightAdjoint ℤ

/-- Exactness of this specific unbounded reflector, with its actual shift
structure. It uses no protected derived-solidification adjunction. -/
instance solidDerivedLocalReflection_isTriangulated :
    solidDerivedLocalReflection.IsTriangulated :=
  solidDerivedLocalReflectionAdjunction.isTriangulated_leftAdjoint

instance solidDerivedLocalReflectionAdjunction_isTriangulated :
    solidDerivedLocalReflectionAdjunction.IsTriangulated :=
  Adjunction.IsTriangulated.mk'' _

end LightCondensed.Solid


/- Owned source component: SolidDerivedColimits.lean. -/

/-!
Copyright (c) 2026. Released under Apache 2.0.
Actual exact small colimits in the protected solid category and the actual
coproduct comparison for its unbounded derived inclusion. These are used
in the unbounded generator realization; no derived full faithfulness,
realization or left-derived adjunction is assumed.
The ordinary colimit closure is reused from the accepted official-pin port
of dagurtomas/LeanCondensed@339ecc99fdc4bdb68ef248c16da0148dce61a639.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits HomologicalComplex

namespace LightCondensed.Solid

instance solid_hasSmallColimitsOfShape (J : Type) [SmallCategory J] :
    HasColimitsOfShape J Solid := by infer_instance

instance solidInclusion_preservesSmallColimitsOfShape (J : Type) [SmallCategory J] :
    PreservesColimitsOfShape J isSolid.ι := by infer_instance

/-- Exactness of these colimits is pulled back through the actual exact
fully faithful inclusion, rather than assumed for the solid category. -/
instance solid_hasExactSmallColimitsOfShape (J : Type) [SmallCategory J]
    [HasExactColimitsOfShape J LightCondAb] : HasExactColimitsOfShape J Solid :=
  HasExactColimitsOfShape.domain_of_functor J isSolid.ι

theorem solidDerivedQ_preservesCoproduct {I : Type}
    (K : I → CochainComplex Solid ℤ) :
    PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := Solid)) := by
  haveI : IsGrothendieckAbelian.{0} LightCondAb := inferInstance
  haveI : AB4OfSize.{0} LightCondAb := IsGrothendieckAbelian.ab4OfSize LightCondAb
  exact CWSolid.derivedQ_preservesCoproduct K

/-- The protected derived inclusion preserves the coproduct of every
small family of arbitrary unbounded solid complexes. -/
theorem derivedInclusion_preservesComplexCoproduct {I : Type}
    (K : I → CochainComplex Solid ℤ) :
    PreservesColimit (Discrete.functor (fun i => DerivedCategory.Q.obj (K i)))
      derivedInclusion := by
  let A := isSolid.ι.mapHomologicalComplex (.up ℤ)
  let QA := DerivedCategory.Q (C := LightCondAb)
  let QB := DerivedCategory.Q (C := Solid)
  haveI : PreservesColimit (Discrete.functor K) QB := solidDerivedQ_preservesCoproduct K
  haveI : PreservesColimit (Discrete.functor K ⋙ A) QA := by
    let K' i := A.obj (K i)
    haveI : PreservesColimit (Discrete.functor K') QA :=
      lightCondensedDerivedQ_preservesCoproduct K'
    exact preservesColimit_of_iso_diagram QA
      (Discrete.natIso (F := Discrete.functor K') (G := Discrete.functor K ⋙ A)
        (fun j => Iso.refl (A.obj (K j.as))))
  haveI : PreservesColimit (Discrete.functor K) (A ⋙ QA) := by infer_instance
  haveI : PreservesColimit (Discrete.functor K) (QB ⋙ derivedInclusion) :=
    preservesColimit_of_natIso (Discrete.functor K) isSolid.ι.mapDerivedCategoryFactors.symm
  haveI : PreservesColimit (Discrete.functor K ⋙ QB) derivedInclusion :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves QB (coproductIsCoproduct K))
      (isColimitOfPreserves (QB ⋙ derivedInclusion) (coproductIsCoproduct K))
  exact preservesColimit_of_iso_diagram derivedInclusion
    (Discrete.natIso (F := Discrete.functor K ⋙ QB)
      (G := Discrete.functor (fun i => QB.obj (K i)))
      (fun j => Iso.refl (QB.obj (K j.as))))

end LightCondensed.Solid


/- Owned source component: FiniteApproximationRetract.lean. -/

/-!
A genuine retract of the reflected free object into the reflected sum of
P and its finite initial quotient. The finite term is retained, so this
construction also respects finite spaces. No DSolid realization is inferred
merely from locality. New proofs, Apache-2.0; Rodríguez Camargo,
Notes on Solid Geometry, Lemma 3.3.2, with the initial contribution explicit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits LightProfinite OnePoint LightCondensed MonoidalCategory

namespace CWSolid
attribute [local instance] FintypeCat.botTopology FintypeCat.discreteTopology

/-- The actual continuous chosen section of the finite initial quotient. -/
def finiteApproximationInitialSection (S : LightProfinite) : S.component 0 ⟶ S := by
  haveI : DiscreteTopology (S.component 0) := by
    change DiscreteTopology (S.fintypeDiagram.obj ⟨0⟩)
    infer_instance
  exact ConcreteCategory.ofHom
    ⟨(compatibleFiniteSection S 0).val, continuous_of_discreteTopology⟩

@[reassoc] theorem finiteApproximationInitialSection_factor (S : LightProfinite) :
    S.proj 0 ≫ finiteApproximationInitialSection S = finiteApproximation S 0 := by
  ext s
  rfl

end CWSolid

namespace LightCondensed.Solid

local instance : solidDerivedLocalReflection.Additive :=
  solidDerivedLocalReflectionAdjunction.left_adjoint_additive
local notation "F" => localMeasureStalk
local instance (B : LightCondAb) :
    IsIso ((F).map (oneMinusShift ▷ B)) := localMeasureDifference_isIso B

/-- Zeroth row, inverse defining difference, and the concrete coefficient map. -/
def localFiniteApproximationSection (S : LightProfinite) :
    (F).obj (freeOn S) ⟶ (F).obj P :=
  (F).map (finiteApproximationRowSection S 0) ≫
    inv ((F).map (oneMinusShift ▷ freeOn S)) ≫
      (F).map (finiteApproximationCoefficient S)

/-- The actual split identity includes the finite initial remainder. -/
theorem localFiniteApproximationSection_comp (S : LightProfinite) (s₀ : S) :
    localFiniteApproximationSection S ≫ (F).map (finiteApproximationPMap S s₀) =
      𝟙 ((F).obj (freeOn S)) -
        (F).map ((free ℤ).map (lightProfiniteToLightCondSet.map
          (CWSolid.finiteApproximation S 0))) := by
  haveI := localMeasureDifference_isIso (freeOn S)
  dsimp only [localFiniteApproximationSection]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← finiteApproximationRemainder_square,
    Functor.map_comp, IsIso.inv_hom_id_assoc, ← Functor.map_comp,
    finiteApproximationRowSection_remainder]
  simp only [Nat.zero_sub, Functor.map_sub, CategoryTheory.Functor.map_id]

set_option maxHeartbeats 1000000 in
/-- An actual retract, with no infinite enumeration or claimed P=free(S). -/
def localFiniteApproximationRetract (S : LightProfinite) (s₀ : S) :
    Retract ((F).obj (freeOn S)) ((F).obj (P ⊞ freeOn (S.component 0))) where
  i := localFiniteApproximationSection S ≫ (F).map biprod.inl +
    (F).map ((free ℤ).map (lightProfiniteToLightCondSet.map (S.proj 0))) ≫
      (F).map biprod.inr
  r := (F).map biprod.fst ≫ (F).map (finiteApproximationPMap S s₀) +
    (F).map biprod.snd ≫
      (F).map ((free ℤ).map (lightProfiniteToLightCondSet.map
        (CWSolid.finiteApproximationInitialSection S)))
  retract := by
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      ← Functor.map_comp_assoc, biprod.inl_fst, biprod.inl_snd,
      biprod.inr_fst, biprod.inr_snd, CategoryTheory.Functor.map_id,
      Functor.map_zero, Category.id_comp, zero_comp, comp_zero,
      add_zero, zero_add]
    rw [localFiniteApproximationSection_comp]
    rw [← Functor.map_comp]
    change _ - (F).map ((lightProfiniteToLightCondSet ⋙ free ℤ).map
        (CWSolid.finiteApproximation S 0)) +
      (F).map ((lightProfiniteToLightCondSet ⋙ free ℤ).map (S.proj 0) ≫
        (lightProfiniteToLightCondSet ⋙ free ℤ).map
          (CWSolid.finiteApproximationInitialSection S)) = _
    rw [← Functor.map_comp, CWSolid.finiteApproximationInitialSection_factor]
    simp only [sub_add_cancel]

end LightCondensed.Solid

/- Owned source component: GeneratorRealization.lean. -/

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
Actual degree-zero realization of every reflected free light-profinite
generator, using the proved canonical P-measure computation and the
finite-initial-term retract. Research attribution: Juan Esteban Rodríguez
Camargo, Notes on Solid Geometry, Theorem 3.3.1 and Lemma 3.3.2.
This does not assert unbounded realization of arbitrary local objects.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits LightCondensed

namespace LightCondensed.Solid

local instance : solidDerivedLocalReflection.Additive :=
  solidDerivedLocalReflectionAdjunction.left_adjoint_additive

/-- Reflection of a genuinely solid stalk is the original stalk. -/
def localSolidStalkIso (B : Solid) :
    (localMeasureStalk.obj (isSolid.ι.obj B)).obj ≅
      (DerivedCategory.singleFunctor LightCondAb 0).obj (isSolid.ι.obj B) :=
  solidDerivedLocal.ι.mapIso
    (asIso (solidDerivedLocalReflectionAdjunction.counit.app (solidMeasureTargetLocal B)))

/-- The actual P computation has no homology away from degree zero. -/
theorem localPStalk_homology_zero (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor LightCondAb n).obj
      (localMeasureStalk.obj P).obj) := by
  let e := solidDerivedLocal.ι.mapIso localIntegerMeasureIso
  apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor LightCondAb n).mapIso e)
  change IsZero ((DerivedCategory.homologyFunctor LightCondAb n).obj
    ((DerivedCategory.singleFunctor LightCondAb 0).obj integerMeasures))
  by_cases h : n < 0
  · exact DerivedCategory.isZero_of_isGE _ 0 n h
  · exact DerivedCategory.isZero_of_isLE _ 0 n (by omega)

/-- The finite initial term is already solid, including the empty case. -/
theorem localInitialFreeStalk_homology_zero (S : LightProfinite)
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor LightCondAb n).obj
      (localMeasureStalk.obj (freeOn (S.component 0))).obj) := by
  let B : Solid := ⟨freeOn (S.component 0), isSolid_free_initialComponent S⟩
  apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor LightCondAb n).mapIso
    (localSolidStalkIso B))
  by_cases h : n < 0
  · exact DerivedCategory.isZero_of_isGE _ 0 n h
  · exact DerivedCategory.isZero_of_isLE _ 0 n (by omega)

/-- The reflected sum in the concrete retract is concentrated in degree zero. -/
theorem localFreeRetractTarget_homology_zero (S : LightProfinite)
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor LightCondAb n).obj
      (localMeasureStalk.obj (P ⊞ freeOn (S.component 0))).obj) := by
  let H := localMeasureStalk ⋙ solidDerivedLocal.ι ⋙
    DerivedCategory.homologyFunctor LightCondAb n
  have hP : IsZero (H.obj P) := localPStalk_homology_zero n hn
  have hA : IsZero (H.obj (freeOn (S.component 0))) :=
    localInitialFreeStalk_homology_zero S n hn
  apply (IsZero.iff_id_eq_zero _).2
  change 𝟙 (H.obj (P ⊞ freeOn (S.component 0))) = 0
  rw [← H.map_id, ← biprod.total, Functor.map_add, Functor.map_comp,
    Functor.map_comp, hP.eq_zero_of_tgt (H.map biprod.fst),
    hA.eq_zero_of_tgt (H.map biprod.snd)]
  simp

/-- Every light-profinite free generator reflects to a degree-zero object.
The empty branch uses its actual finite free object; no chosen point or
infinite enumeration is used there. -/
theorem localFreeStalk_homology_zero (S : LightProfinite)
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor LightCondAb n).obj
      (localMeasureStalk.obj (freeOn S)).obj) := by
  classical
  by_cases hS : Nonempty S
  · let r := (localFiniteApproximationRetract S hS.some).map
      (solidDerivedLocal.ι ⋙ DerivedCategory.homologyFunctor LightCondAb n)
    have hz := localFreeRetractTarget_homology_zero S n hn
    apply (IsZero.iff_id_eq_zero _).2
    change 𝟙 ((solidDerivedLocal.ι ⋙ DerivedCategory.homologyFunctor LightCondAb n).obj
      (localMeasureStalk.obj (freeOn S))) = 0
    rw [← r.retract, hz.eq_zero_of_tgt r.i, zero_comp]
  · letI : IsEmpty S := not_nonempty_iff.mp hS
    let B : Solid := ⟨freeOn S, isSolid_free_finite S⟩
    apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor LightCondAb n).mapIso
      (localSolidStalkIso B))
    by_cases h : n < 0
    · exact DerivedCategory.isZero_of_isGE _ 0 n h
    · exact DerivedCategory.isZero_of_isLE _ 0 n (by omega)

theorem localFreeStalk_isGE (S : LightProfinite) :
    (localMeasureStalk.obj (freeOn S)).obj.IsGE 0 := by
  rw [DerivedCategory.isGE_iff]
  intro n hn
  exact localFreeStalk_homology_zero S n (by omega)

theorem localFreeStalk_isLE (S : LightProfinite) :
    (localMeasureStalk.obj (freeOn S)).obj.IsLE 0 := by
  rw [DerivedCategory.isLE_iff]
  intro n hn
  exact localFreeStalk_homology_zero S n (by omega)

/-- The reflected generator is its actual zeroth homology stalk. -/
def localFreeStalkHeartIso (S : LightProfinite) :
    (localMeasureStalk.obj (freeOn S)).obj ≅
      (DerivedCategory.singleFunctor LightCondAb 0).obj
        ((DerivedCategory.homologyFunctor LightCondAb 0).obj
          (localMeasureStalk.obj (freeOn S)).obj) := by
  let X := (localMeasureStalk.obj (freeOn S)).obj
  letI := localFreeStalk_isGE S
  letI := localFreeStalk_isLE S
  let h := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X 0
  let M := h.choose
  let e := h.choose_spec.some
  let eM := (DerivedCategory.homologyFunctor LightCondAb 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso LightCondAb 0).app M
  exact e ≪≫ (DerivedCategory.singleFunctor LightCondAb 0).mapIso eM.symm

/-- Locality really supplies a protected solid homology object, after
transport from the actual complex representative in the localization. -/
theorem localFreeStalkHeart_solid (S : LightProfinite) :
    isSolid ((DerivedCategory.homologyFunctor LightCondAb 0).obj
      (localMeasureStalk.obj (freeOn S)).obj) := by
  let X := (localMeasureStalk.obj (freeOn S)).obj
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hX : IsIso (solidDerivedEndomorphism.app X) :=
    (localMeasureStalk.obj (freeOn S)).property
  have hK : IsIso (solidDerivedEndomorphism.app (DerivedCategory.Q.obj K)) :=
    (NatTrans.isIso_app_iff_of_iso solidDerivedEndomorphism e).2 hX
  have hs := (isIso_solidDerivedEndomorphism_Q_iff K).1 hK 0
  let eh : K.homology 0 ≅ (DerivedCategory.homologyFunctor LightCondAb 0).obj X :=
    ((DerivedCategory.homologyFunctorFactors LightCondAb 0).app K).symm ≪≫
      (DerivedCategory.homologyFunctor LightCondAb 0).mapIso e
  exact isSolid.prop_of_iso eh hs

def localFreeStalkSolidObject (S : LightProfinite) : Solid :=
  ⟨(DerivedCategory.homologyFunctor LightCondAb 0).obj
    (localMeasureStalk.obj (freeOn S)).obj, localFreeStalkHeart_solid S⟩

/-- An actual object of the protected D(Solid) realizes each reflected
free generator. No realization of an arbitrary unbounded object is inferred. -/
def localFreeStalkRealizationIso (S : LightProfinite) :
    (localMeasureStalk.obj (freeOn S)).obj ≅
      derivedInclusion.obj ((DerivedCategory.singleFunctor Solid 0).obj
        (localFreeStalkSolidObject S)) :=
  localFreeStalkHeartIso S ≪≫
    ((isSolid.ι.mapDerivedCategorySingleFunctor 0).app
      (localFreeStalkSolidObject S)).symm

/-- The comparison is induced by the actual derived-local unit. -/
def freeToLocalFreeHeart (S : LightProfinite) :
    freeOn S ⟶ isSolid.ι.obj (localFreeStalkSolidObject S) :=
  (DerivedCategory.singleFunctor LightCondAb 0).preimage
    (solidDerivedLocalReflectionAdjunction.unit.app
      ((DerivedCategory.singleFunctor LightCondAb 0).obj (freeOn S)) ≫
        (localFreeStalkHeartIso S).hom)

theorem freeToLocalFreeHeart_derivedPrecomp_bijective
    (S : LightProfinite) (B : Solid) :
    Function.Bijective (fun g :
      (DerivedCategory.singleFunctor LightCondAb 0).obj
        (isSolid.ι.obj (localFreeStalkSolidObject S)) ⟶
      (DerivedCategory.singleFunctor LightCondAb 0).obj (isSolid.ι.obj B) =>
      (DerivedCategory.singleFunctor LightCondAb 0).map (freeToLocalFreeHeart S) ≫ g) := by
  let X := (DerivedCategory.singleFunctor LightCondAb 0).obj (freeOn S)
  let Y := solidMeasureTargetLocal B
  let E := solidMeasureTargetLocal (localFreeStalkSolidObject S)
  let j := solidDerivedLocal.ι
  let eH : localMeasureStalk.obj (freeOn S) ≅ E :=
    solidDerivedLocal.isoMk (localFreeStalkHeartIso S)
  let e : (E.obj ⟶ Y.obj) ≃ (X ⟶ Y.obj) :=
    (Functor.FullyFaithful.ofFullyFaithful j).homEquiv.symm.trans
      ((eH.symm.homCongr (Iso.refl Y)).trans
        (solidDerivedLocalReflectionAdjunction.homEquiv X Y))
  have heq : (fun g : E.obj ⟶ Y.obj =>
      (DerivedCategory.singleFunctor LightCondAb 0).map (freeToLocalFreeHeart S) ≫ g) =
      (fun g => e g) := by
    funext g
    change _ = solidDerivedLocalReflectionAdjunction.unit.app X ≫
      j.map (eH.hom ≫ j.preimage (X := E) (Y := Y) g ≫ 𝟙 Y)
    simp only [freeToLocalFreeHeart, Functor.map_preimage, Functor.map_comp,
      Category.comp_id, Functor.map_preimage, ← Category.assoc]
    rfl
  change Function.Bijective (fun g : E.obj ⟶ Y.obj =>
    (DerivedCategory.singleFunctor LightCondAb 0).map (freeToLocalFreeHeart S) ≫ g)
  rw [heq]
  exact e.bijective

/-- This ordinary universal property is proved from the concrete heart
calculation; no derived adjunction with DSolid is assumed. -/
theorem freeToLocalFreeHeart_precomp_bijective (S : LightProfinite) (B : Solid) :
    Function.Bijective (fun g :
      isSolid.ι.obj (localFreeStalkSolidObject S) ⟶ isSolid.ι.obj B =>
      freeToLocalFreeHeart S ≫ g) := by
  let F := DerivedCategory.singleFunctor LightCondAb 0
  have h := freeToLocalFreeHeart_derivedPrecomp_bijective S B
  constructor
  · intro f g hfg
    apply F.map_injective
    apply h.injective
    change F.map (freeToLocalFreeHeart S) ≫ F.map f =
      F.map (freeToLocalFreeHeart S) ≫ F.map g
    simpa only [Functor.map_comp] using congrArg F.map hfg
  · intro f
    obtain ⟨g, hg⟩ := h.surjective (F.map f)
    refine ⟨F.preimage g, F.map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage]
    exact hg

def solidFreeToLocalFreeHeart (S : LightProfinite) :
    solidification.obj (freeOn S) ⟶ localFreeStalkSolidObject S :=
  (solidificationAdjunction.homEquiv (freeOn S) (localFreeStalkSolidObject S)).symm
    (freeToLocalFreeHeart S)

theorem solidFreeToLocalFreeHeart_unit (S : LightProfinite) :
    solidificationAdjunction.unit.app (freeOn S) ≫
      isSolid.ι.map (solidFreeToLocalFreeHeart S) = freeToLocalFreeHeart S :=
  (solidificationAdjunction.homEquiv (freeOn S)
    (localFreeStalkSolidObject S)).apply_symm_apply _

theorem solidFreeToLocalFreeHeart_isIso (S : LightProfinite) :
    IsIso (solidFreeToLocalFreeHeart S) := by
  apply isIso_of_coyoneda_map_bijective
  intro B
  let e := solidificationAdjunction.homEquiv (freeOn S) B
  let eH := (Functor.FullyFaithful.ofFullyFaithful isSolid.ι).homEquiv
    (X := localFreeStalkSolidObject S) (Y := B)
  have heq : (fun g : localFreeStalkSolidObject S ⟶ B =>
      solidFreeToLocalFreeHeart S ≫ g) =
      (fun g => e.symm (freeToLocalFreeHeart S ≫ eH g)) := by
    funext g
    apply e.injective
    rw [Equiv.apply_symm_apply]
    exact (solidificationAdjunction.homEquiv_naturality_right
      (solidFreeToLocalFreeHeart S) g).trans
        (congrArg (· ≫ isSolid.ι.map g)
          ((solidificationAdjunction.homEquiv (freeOn S)
            (localFreeStalkSolidObject S)).apply_symm_apply (freeToLocalFreeHeart S)))
  change Function.Bijective (fun g : localFreeStalkSolidObject S ⟶ B =>
    solidFreeToLocalFreeHeart S ≫ g)
  rw [heq]
  exact e.symm.bijective.comp ((freeToLocalFreeHeart_precomp_bijective S B).comp eH.bijective)

def solidFreeLocalHeartIso (S : LightProfinite) :
    solidification.obj (freeOn S) ≅ localFreeStalkSolidObject S := by
  haveI := solidFreeToLocalFreeHeart_isIso S
  exact asIso (solidFreeToLocalFreeHeart S)

/-- The generator realization uses the exact original ordinary reflector. -/
def localFreeStalkOrdinaryRealizationIso (S : LightProfinite) :
    (localMeasureStalk.obj (freeOn S)).obj ≅
      derivedInclusion.obj ((DerivedCategory.singleFunctor Solid 0).obj
        (solidification.obj (freeOn S))) :=
  localFreeStalkRealizationIso S ≪≫
    derivedInclusion.mapIso ((DerivedCategory.singleFunctor Solid 0).mapIso
      (solidFreeLocalHeartIso S).symm)

end LightCondensed.Solid


/- Owned source component: SolidGenerator.lean. -/

/-!
Copyright (c) 2026. Released under Apache 2.0.
The concrete protected solidification of P detects zero solid objects.
The proof uses the actual integer-measure computation, finite free coproducts
and the finite-initial-term local retract. Research attribution: Juan Esteban
Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1.
No derived adjunction, global EnoughProjectives or unbounded realization is
assumed. This is the actual ordinary generator calculation used by that route.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits LightCondensed LightProfinite

namespace LightCondensed.Solid
open IntProof

local instance : solidDerivedLocalReflection.Additive :=
  solidDerivedLocalReflectionAdjunction.left_adjoint_additive
local instance : solidification.Additive := solidificationAdjunction.left_adjoint_additive
attribute [local instance] FintypeCat.botTopology FintypeCat.discreteTopology

/-- The finite-presentability calculation uses the literal protected
cokernel P and the already-proved filtered-colimit computation for free
test objects. -/
theorem P_hom_preservesSmallFilteredColimits :
    PreservesFilteredColimitsOfSize.{0, 0} (coyoneda.obj (Opposite.op P)) := by
  haveI : PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (Opposite.op
        ((free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed))) :=
    LightSolidFilteredScaffold.preservesFilteredColimits_hom_free_lightProfinite _
  haveI : PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (Opposite.op ((free ℤ).obj (ℕ∪{∞}).toCondensed))) :=
    LightSolidFilteredScaffold.preservesFilteredColimits_hom_free_lightProfinite _
  exact LightSolidFilteredScaffold.preservesFilteredColimits_hom_cokernel_of_preserves_hom P_map

/-- The actual ordinary adjunction supplies this natural Hom comparison. -/
def solidGeneratorHomIso :
    coyoneda.obj (Opposite.op (solidification.obj P)) ≅
      isSolid.ι ⋙ coyoneda.obj (Opposite.op P) :=
  NatIso.ofComponents
    (fun X => Equiv.toIso (solidificationAdjunction.homEquiv P X)) (by
      intro X Y f
      ext g
      exact solidificationAdjunction.homEquiv_naturality_right g f)

/-- The specific protected reflected generator is finitely presentable
in Solid. No smallness or projectivity is silently assumed. -/
theorem solidP_hom_preservesSmallFilteredColimits :
    PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (Opposite.op (solidification.obj P))) := by
  haveI := P_hom_preservesSmallFilteredColimits
  refine ⟨fun J _ _ => ?_⟩
  haveI : PreservesColimitsOfShape J (coyoneda.obj (Opposite.op P)) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
  haveI : PreservesColimitsOfShape J isSolid.ι := by infer_instance
  exact preservesColimitsOfShape_of_natIso solidGeneratorHomIso.symm

def integerMeasuresZeroSection : Zdisc ⟶ integerMeasures :=
  Pi.lift (fun n : ℕ => if n = 0 then 𝟙 Zdisc else 0)

theorem integerMeasuresZeroSection_comp :
    integerMeasuresZeroSection ≫ Pi.π (fun _ : ℕ => Zdisc) 0 = 𝟙 Zdisc := by
  simp [integerMeasuresZeroSection]

private theorem localStalkHom_zero (A : LightCondAb) (B : Solid)
    (h : ∀ f : A ⟶ isSolid.ι.obj B, f = 0)
    (f : localMeasureStalk.obj A ⟶ solidMeasureTargetLocal B) : f = 0 := by
  let F := DerivedCategory.singleFunctor LightCondAb 0
  let e : (localMeasureStalk.obj A ⟶ solidMeasureTargetLocal B) ≃
      (F.obj A ⟶ F.obj (isSolid.ι.obj B)) :=
    solidDerivedLocalReflectionAdjunction.homEquiv (F.obj A) (solidMeasureTargetLocal B)
  apply e.injective
  calc
    e f = F.map (F.preimage (e f)) := (F.map_preimage (e f)).symm
    _ = F.map 0 := congrArg F.map (h (F.preimage (e f)))
    _ = 0 := F.map_zero _ _
    _ = e 0 := (solidDerivedLocalReflectionAdjunction.homAddEquiv_zero
      (F.obj A) (solidMeasureTargetLocal B)).symm

private theorem hom_finiteFree_zero (S : LightProfinite)
    [Finite S] [DiscreteTopology S] (X : Solid)
    (hZ : ∀ f : Zdisc ⟶ isSolid.ι.obj X, f = 0)
    (f : freeOn S ⟶ isSolid.ι.obj X) : f = 0 := by
  let F := lightProfiniteToLightCondSet ⋙ free ℤ
  let e := F.mapIso (finiteProfinitePointsIso S)
  have hpoint (g : freeOn (LightProfinite.of PUnit.{1}) ⟶ isSolid.ι.obj X) : g = 0 := by
    rw [← Category.id_comp g, ← freeProfinitePointIsoInt.hom_inv_id, Category.assoc,
      hZ (freeProfinitePointIsoInt.inv ≫ g), comp_zero]
  apply (cancel_epi e.hom).1
  rw [comp_zero]
  let hc := isColimitOfPreserves F (CompHausLike.finiteCoproduct.isColimit
    (fun _ : S => LightProfinite.of PUnit.{1}))
  apply hc.hom_ext
  rintro ⟨s⟩
  change F.map (CompHausLike.finiteCoproduct.ι
    (fun _ : S => LightProfinite.of PUnit.{1}) s) ≫ e.hom ≫ f = 0
  exact hpoint _

/-- The actual protected object solidification(P), rather than an assumed
generator, detects every zero solid object. -/
theorem solidP_detects_isZero (X : Solid)
    (h : ∀ f : solidification.obj P ⟶ X, f = 0) : IsZero X := by
  classical
  have hP (f : P ⟶ isSolid.ι.obj X) : f = 0 := by
    let e := solidificationAdjunction.homEquiv P X
    calc
      f = e (e.symm f) := (e.apply_symm_apply f).symm
      _ = e 0 := congrArg e (h (e.symm f))
      _ = 0 := solidificationAdjunction.homAddEquiv_zero P X
  have hM (f : integerMeasures ⟶ isSolid.ι.obj X) : f = 0 := by
    let g : integerMeasuresSolid ⟶ X := isSolid.ι.preimage f
    haveI := solidPToIntegerMeasures_isIso
    have hg : g = 0 := by
      apply (cancel_epi solidPToIntegerMeasures).1
      simpa using h (solidPToIntegerMeasures ≫ g)
    calc
      f = isSolid.ι.map g := (isSolid.ι.map_preimage (X := integerMeasuresSolid) (Y := X) f).symm
      _ = 0 := by rw [hg, Functor.map_zero]
  have hZ (f : Zdisc ⟶ isSolid.ι.obj X) : f = 0 := by
    rw [← Category.id_comp f, ← integerMeasuresZeroSection_comp, Category.assoc,
      hM (Pi.π (fun _ : ℕ => Zdisc) 0 ≫ f), comp_zero]
  have hfree (S : LightProfinite) (g : freeOn S ⟶ isSolid.ι.obj X) : g = 0 := by
    by_cases hS : Nonempty S
    · let F := DerivedCategory.singleFunctor LightCondAb 0
      let Y := solidMeasureTargetLocal X
      let e := solidDerivedLocalReflectionAdjunction.homEquiv (F.obj (freeOn S)) Y
      let f := e.symm (F.map g)
      let r := localFiniteApproximationRetract S hS.some
      have hfinite (a : freeOn (S.component 0) ⟶ isSolid.ι.obj X) : a = 0 := by
        haveI : Finite (S.component 0) :=
          inferInstanceAs (Finite (S.fintypeDiagram.obj ⟨0⟩))
        haveI : DiscreteTopology (S.component 0) := by
          change DiscreteTopology (S.fintypeDiagram.obj ⟨0⟩)
          infer_instance
        exact hom_finiteFree_zero (S.component 0) X hZ a
      have hsum (a : P ⊞ freeOn (S.component 0) ⟶ isSolid.ι.obj X) : a = 0 := by
        apply biprod.hom_ext'
        · simpa using hP (biprod.inl ≫ a)
        · simpa using hfinite (biprod.inr ≫ a)
      have hr : r.r ≫ f = 0 :=
        localStalkHom_zero (P ⊞ freeOn (S.component 0)) X hsum _
      have hf : f = 0 := by
        simpa only [Category.assoc, hr, comp_zero, Category.id_comp] using
          (congrArg (fun u => u ≫ f) r.retract).symm
      apply F.map_injective
      calc
        F.map g = e f := (e.apply_symm_apply (F.map g)).symm
        _ = e 0 := by rw [hf]
        _ = 0 := solidDerivedLocalReflectionAdjunction.homAddEquiv_zero _ _
        _ = F.map 0 := (F.map_zero _ _).symm
    · letI : IsEmpty S := not_nonempty_iff.mp hS
      exact hom_finiteFree_zero S X hZ g
  apply (IsZero.iff_id_eq_zero X).2
  apply isSolid.ι.map_injective
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  apply hom_eq_zero_of_free
  intro S g
  simpa using hfree S g

end LightCondensed.Solid


/- Owned source component: UnboundedTruncationTelescope.lean. -/

/-!
Copyright (c) 2026. Released under Apache 2.0.
Actual mapping-cone presentation of every unbounded light condensed
complex by its bounded-below brutal truncations. The colimit and monicity
arguments reuse the accepted sequence-presentation proof, now for the
explicit lower-truncation diagram. No realization or derived adjunction
is assumed. Research: Rodríguez Camargo, Notes on Solid Geometry,
Theorem 3.3.1, unbounded extension.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits HomologicalComplex

namespace LightCondensed.Solid
open CWSolid

local instance lowerTruncationCoproducts :
    HasColimitsOfShape (Discrete ℕ) (CochainComplex LightCondAb ℤ) := by infer_instance

def lowerTruncationTelescopeDifferential (K : CochainComplex LightCondAb ℤ) :
    (∐ lowerTruncation K) ⟶ ∐ lowerTruncation K :=
  𝟙 _ - Limits.Sigma.desc (fun n => lowerTruncationMap K n (n + 1) (Nat.le_succ n) ≫
    Sigma.ι (lowerTruncation K) (n + 1))

def lowerTruncationSumToInput (K : CochainComplex LightCondAb ℤ) :
    (∐ lowerTruncation K) ⟶ K :=
  Limits.Sigma.desc (lowerTruncationι K)

private theorem lowerTruncationTelescopeDifferential_comp (K : CochainComplex LightCondAb ℤ) :
    lowerTruncationTelescopeDifferential K ≫ lowerTruncationSumToInput K = 0 := by
  apply Sigma.hom_ext
  intro n
  simp [lowerTruncationTelescopeDifferential, lowerTruncationSumToInput,
    Preadditive.comp_sub, Preadditive.sub_comp, lowerTruncationMap_ι]

def lowerTruncationTelescopeSequence (K : CochainComplex LightCondAb ℤ) :
    ShortComplex (CochainComplex LightCondAb ℤ) :=
  ShortComplex.mk (lowerTruncationTelescopeDifferential K) (lowerTruncationSumToInput K)
    (lowerTruncationTelescopeDifferential_comp K)

/-- The last object is the unrestricted original K, not an assumed
realization or only a bounded truncation. -/
def lowerTruncationTelescopeSequence_isCokernel (K : CochainComplex LightCondAb ℤ) :
    IsColimit (CokernelCofork.ofπ (lowerTruncationTelescopeSequence K).g
      (lowerTruncationTelescopeSequence K).zero) := by
  let S := lowerTruncationTelescopeSequence K
  let hc := lowerTruncationCocone_isColimit K
  have descExists {Y : CochainComplex LightCondAb ℤ}
      (g : S.X₂ ⟶ Y) (hg : S.f ≫ g = 0) : ∃ u : K ⟶ Y, S.g ≫ u = g := by
    have hn (n : ℕ) : lowerTruncationMap K n (n + 1) (Nat.le_succ n) ≫
        (Sigma.ι (lowerTruncation K) (n + 1) ≫ g) =
          Sigma.ι (lowerTruncation K) n ≫ g := by
      have h := congrArg (Sigma.ι (lowerTruncation K) n ≫ ·) hg
      simp only [S, lowerTruncationTelescopeSequence, lowerTruncationTelescopeDifferential,
        Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp,
        Sigma.ι_desc_assoc, comp_zero] at h
      exact (sub_eq_zero.mp h).symm
    let c : Cocone (lowerTruncationDiagram K) :=
      { pt := Y
        ι := NatTrans.ofSequence (fun n => Sigma.ι (lowerTruncation K) n ≫ g)
          (fun n => by simpa [lowerTruncationDiagram] using hn n) }
    refine ⟨hc.desc c, ?_⟩
    apply Sigma.hom_ext
    intro n
    change Sigma.ι (lowerTruncation K) n ≫ lowerTruncationSumToInput K ≫ hc.desc c = _
    simp only [lowerTruncationSumToInput, Sigma.ι_desc_assoc]
    exact hc.fac c n
  refine CokernelCofork.IsColimit.ofπ S.g S.zero
    (fun g hg => (descExists g hg).choose)
    (fun g hg => (descExists g hg).choose_spec) ?_
  intro Y g hg u hu
  apply hc.hom_ext
  intro n
  have h := congrArg (Sigma.ι (lowerTruncation K) n ≫ ·)
    (hu.trans (descExists g hg).choose_spec.symm)
  simpa only [S, lowerTruncationTelescopeSequence, lowerTruncationSumToInput,
    Sigma.ι_desc_assoc, lowerTruncationCocone] using h

theorem lowerTruncationTelescopeDifferential_f_mono
    (K : CochainComplex LightCondAb ℤ) (m : ℤ) :
    Mono ((lowerTruncationTelescopeDifferential K).f m) := by
  haveI : IsGrothendieckAbelian.{0} LightCondAb := inferInstance
  haveI : AB5OfSize.{0, 0} LightCondAb := inferInstance
  let G := eval LightCondAb (.up ℤ) m
  let A : ℕ → LightCondAb := fun n => G.obj (lowerTruncation K n)
  let a : ∀ n, A n ⟶ A (n + 1) :=
    fun n => G.map (lowerTruncationMap K n (n + 1) (Nat.le_succ n))
  let e := PreservesCoproduct.iso G (lowerTruncation K)
  let d := 𝟙 (∐ A) - Limits.Sigma.desc (fun n => a n ≫ Sigma.ι A (n + 1))
  have hleg (n : ℕ) : G.map (Sigma.ι (lowerTruncation K) n) ≫ e.hom = Sigma.ι A n := by
    simpa [e, A, ← PreservesCoproduct.inv_hom] using
      (map_ι_comp_inv_sigmaComparison (G := G) (f := lowerTruncation K) n)
  have hlegInv (n : ℕ) : Sigma.ι A n ≫ e.inv = G.map (Sigma.ι (lowerTruncation K) n) := by
    rw [← hleg, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hd : e.inv ≫ G.map (lowerTruncationTelescopeDifferential K) ≫ e.hom = d := by
    apply Sigma.hom_ext
    intro n
    change Sigma.ι A n ≫ e.inv ≫ G.map (lowerTruncationTelescopeDifferential K) ≫ e.hom =
      Sigma.ι A n ≫ d
    rw [← Category.assoc, hlegInv, ← G.map_comp_assoc]
    have hn : Sigma.ι (lowerTruncation K) n ≫ lowerTruncationTelescopeDifferential K =
        Sigma.ι (lowerTruncation K) n - lowerTruncationMap K n (n + 1) (Nat.le_succ n) ≫
          Sigma.ι (lowerTruncation K) (n + 1) := by
      simp [lowerTruncationTelescopeDifferential, Preadditive.comp_sub]
    rw [hn, G.map_sub, Preadditive.sub_comp, G.map_comp, Category.assoc, hleg, hleg]
    dsimp only [d]
    rw [Preadditive.comp_sub, Category.comp_id, Sigma.ι_desc]
  have he : G.map (lowerTruncationTelescopeDifferential K) = e.hom ≫ d ≫ e.inv := by
    rw [← hd]
    simp
  haveI : Mono d := CWSolid.oneMinusSequence_mono A a
  change Mono (G.map (lowerTruncationTelescopeDifferential K))
  rw [he]
  infer_instance

theorem lowerTruncationTelescopeSequence_shortExact (K : CochainComplex LightCondAb ℤ) :
    (lowerTruncationTelescopeSequence K).ShortExact := by
  haveI : Mono (lowerTruncationTelescopeSequence K).f :=
    HomologicalComplex.mono_of_mono_f _ (lowerTruncationTelescopeDifferential_f_mono K)
  haveI : Epi (lowerTruncationTelescopeSequence K).g :=
    epi_of_isColimit_cofork (lowerTruncationTelescopeSequence_isCokernel K)
  exact { exact := ((lowerTruncationTelescopeSequence K).exact_of_g_is_cokernel
    (lowerTruncationTelescopeSequence_isCokernel K)) }

def lowerTruncationTelescope (K : CochainComplex LightCondAb ℤ) :
    CochainComplex LightCondAb ℤ := CochainComplex.mappingCone (lowerTruncationTelescopeDifferential K)

def lowerTruncationTelescopeToInput (K : CochainComplex LightCondAb ℤ) :
    lowerTruncationTelescope K ⟶ K :=
  CochainComplex.mappingCone.descShortComplex (lowerTruncationTelescopeSequence K)

/-- A proved quasi-isomorphism for every unbounded input. It provides the
actual lower-truncation telescope used in the realization argument. -/
theorem lowerTruncationTelescopeToInput_quasiIso (K : CochainComplex LightCondAb ℤ) :
    QuasiIso (lowerTruncationTelescopeToInput K) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex
    (lowerTruncationTelescopeSequence_shortExact K)

end LightCondensed.Solid


/- Every named public construction root is audited here. -/
#print axioms LightCondensed.Solid.solidDerivedLocal_closedUnderIsomorphisms
#print axioms LightCondensed.Solid.solidDerivedLocal_containsZero
#print axioms LightCondensed.Solid.solidDerivedLocal_stableUnderShift
#print axioms LightCondensed.Solid.solidDerivedEndomorphismTriangle
#print axioms LightCondensed.Solid.solidDerivedLocal_closedUnderCones
#print axioms LightCondensed.Solid.solidDerivedLocal_closedUnderExtensions
#print axioms LightCondensed.Solid.solidDerivedLocal_isTriangulated
#print axioms LightCondensed.Solid.solidDerivedLocalReflection_commShift
#print axioms LightCondensed.Solid.solidDerivedLocalReflectionAdjunction_commShift
#print axioms LightCondensed.Solid.solidDerivedLocalReflection_isTriangulated
#print axioms LightCondensed.Solid.solidDerivedLocalReflectionAdjunction_isTriangulated
#print axioms LightCondensed.Solid.solid_hasSmallColimitsOfShape
#print axioms LightCondensed.Solid.solidInclusion_preservesSmallColimitsOfShape
#print axioms LightCondensed.Solid.solid_hasExactSmallColimitsOfShape
#print axioms LightCondensed.Solid.solidDerivedQ_preservesCoproduct
#print axioms LightCondensed.Solid.derivedInclusion_preservesComplexCoproduct
#print axioms CWSolid.finiteApproximationInitialSection
#print axioms CWSolid.finiteApproximationInitialSection_factor
#print axioms LightCondensed.Solid.localFiniteApproximationSection
#print axioms LightCondensed.Solid.localFiniteApproximationSection_comp
#print axioms LightCondensed.Solid.localFiniteApproximationRetract
#print axioms LightCondensed.Solid.localSolidStalkIso
#print axioms LightCondensed.Solid.localPStalk_homology_zero
#print axioms LightCondensed.Solid.localInitialFreeStalk_homology_zero
#print axioms LightCondensed.Solid.localFreeRetractTarget_homology_zero
#print axioms LightCondensed.Solid.localFreeStalk_homology_zero
#print axioms LightCondensed.Solid.localFreeStalk_isGE
#print axioms LightCondensed.Solid.localFreeStalk_isLE
#print axioms LightCondensed.Solid.localFreeStalkHeartIso
#print axioms LightCondensed.Solid.localFreeStalkHeart_solid
#print axioms LightCondensed.Solid.localFreeStalkSolidObject
#print axioms LightCondensed.Solid.localFreeStalkRealizationIso
#print axioms LightCondensed.Solid.freeToLocalFreeHeart
#print axioms LightCondensed.Solid.freeToLocalFreeHeart_derivedPrecomp_bijective
#print axioms LightCondensed.Solid.freeToLocalFreeHeart_precomp_bijective
#print axioms LightCondensed.Solid.solidFreeToLocalFreeHeart
#print axioms LightCondensed.Solid.solidFreeToLocalFreeHeart_unit
#print axioms LightCondensed.Solid.solidFreeToLocalFreeHeart_isIso
#print axioms LightCondensed.Solid.solidFreeLocalHeartIso
#print axioms LightCondensed.Solid.localFreeStalkOrdinaryRealizationIso
#print axioms LightCondensed.Solid.P_hom_preservesSmallFilteredColimits
#print axioms LightCondensed.Solid.solidGeneratorHomIso
#print axioms LightCondensed.Solid.solidP_hom_preservesSmallFilteredColimits
#print axioms LightCondensed.Solid.integerMeasuresZeroSection
#print axioms LightCondensed.Solid.integerMeasuresZeroSection_comp
#print axioms LightCondensed.Solid.solidP_detects_isZero
#print axioms LightCondensed.Solid.lowerTruncationTelescopeDifferential
#print axioms LightCondensed.Solid.lowerTruncationSumToInput
#print axioms LightCondensed.Solid.lowerTruncationTelescopeSequence
#print axioms LightCondensed.Solid.lowerTruncationTelescopeSequence_isCokernel
#print axioms LightCondensed.Solid.lowerTruncationTelescopeDifferential_f_mono
#print axioms LightCondensed.Solid.lowerTruncationTelescopeSequence_shortExact
#print axioms LightCondensed.Solid.lowerTruncationTelescope
#print axioms LightCondensed.Solid.lowerTruncationTelescopeToInput
#print axioms LightCondensed.Solid.lowerTruncationTelescopeToInput_quasiIso
