/- GID: D5/S3/HomologicalAlgebra/Solid/MeasureFactorization
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/MeasureFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.BoundedMeasures

/-! Actual derived factorization of every uniformly bounded integer family
through the constructed local reflection of the protected P. The tensor square
is proved in BoundedMeasures; no D(Solid) realization is assumed. New proofs,
Apache-2.0, following Rodriguez Camargo's concrete measure argument. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint MonoidalCategory MonoidalClosed
open scoped BigOperators

namespace LightCondensed.Solid
open IntProof

/-- All the coordinates of an integer family, as an actual condensed morphism. -/
def familyToIntegerMeasures (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ) :
    freeOn S ⟶ integerMeasures :=
  Pi.lift (fun j => (freeHomIntAddEquiv S).symm (c j))

/-- Include the test space in the zeroth finite slice of the convergent sequence. -/
def measureZeroSlice (S : LightProfinite) : S ⟶ NinfTensor S :=
  ConcreteCategory.ofHom ⟨fun s => (((0 : ℕ) : ℕ∪{∞}), s),
    continuous_const.prodMk continuous_id⟩

/-- The actual zeroth-coordinate section of the tail construction. -/
def measureTailSection (S : LightProfinite) : freeOn S ⟶ P ⊗ freeOn S :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map (measureZeroSlice S) ≫
    (freeTensorIsoInt (ℕ∪{∞}) S).inv ≫ (P_proj ▷ freeOn S)

theorem measureTailSection_tailMap (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) :
    measureTailSection S ≫ measureTailMap S c = familyToIntegerMeasures S c := by
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, measureTailMap, familyToIntegerMeasures, Pi.lift_π]
  apply (freeHomDiscreteEquiv ℤ S (ModuleCat.of ℤ ℤ)).injective
  ext s
  dsimp only [measureTailSection]
  change freeHomDiscreteEquiv ℤ S (ModuleCat.of ℤ ℤ)
    ((free ℤ).map (lightProfiniteToLightCondSet.map (measureZeroSlice S)) ≫
      ((freeTensorIsoInt (ℕ∪{∞}) S).inv ≫
        (P_proj ▷ freeOn S) ≫ measureTailCoordinate S c j)) s = _
  rw [freeHomDiscreteEquiv_map]
  change numeratorHomEquiv S ((P_proj ▷ freeOn S) ≫ measureTailCoordinate S c j)
    (((0 : ℕ) : ℕ∪{∞}), s) = _
  rw [← pTensorHomSubtypeEquiv_apply_coe,
    ← nullSeqPointsEquiv_apply, show nullSeqPointsEquiv S (measureTailCoordinate S c j) =
      (c j).map (measureTailSeq j) from (nullSeqPointsEquiv S).apply_symm_apply _]
  have hc : freeHomDiscreteEquiv ℤ S (ModuleCat.of ℤ ℤ)
      ((freeHomIntAddEquiv S).symm (c j)) = c j := (freeHomIntAddEquiv S).apply_symm_apply _
  rw [hc]
  simp [LocallyConstant.map]

/-- Lift the bounded coefficient map past the defining map in the actual
unbounded derived category. The existence follows from the proved all-roof
orthogonality into the actual local-reflection object. -/
def boundedTensorLocalLift (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ)
    (F : Finset ℤ) :
    (DerivedCategory.singleFunctor LightCondAb 0).obj (P ⊗ freeOn S) ⟶
      (solidDerivedLocalReflection.obj
        ((DerivedCategory.singleFunctor LightCondAb 0).obj P)).obj := by
  let Y := solidDerivedLocalReflection.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj P)
  haveI : IsIso (solidDerivedEndomorphism.app Y.obj) := Y.property
  exact ((solidTensorSingle_precomp_bijective (freeOn S) 0 Y.obj).surjective
    ((DerivedCategory.singleFunctor LightCondAb 0).map (boundedCoefficientMap S c F) ≫
      solidDerivedLocalReflectionAdjunction.unit.app
        ((DerivedCategory.singleFunctor LightCondAb 0).obj P))).choose

theorem boundedTensorLocalLift_spec (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) :
    (DerivedCategory.singleFunctor LightCondAb 0).map (oneMinusShift ▷ freeOn S) ≫
      boundedTensorLocalLift S c F =
        (DerivedCategory.singleFunctor LightCondAb 0).map (boundedCoefficientMap S c F) ≫
          solidDerivedLocalReflectionAdjunction.unit.app
            ((DerivedCategory.singleFunctor LightCondAb 0).obj P) := by
  let Y := solidDerivedLocalReflection.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj P)
  haveI : IsIso (solidDerivedEndomorphism.app Y.obj) := Y.property
  exact ((solidTensorSingle_precomp_bijective (freeOn S) 0 Y.obj).surjective
    ((DerivedCategory.singleFunctor LightCondAb 0).map (boundedCoefficientMap S c F) ≫
      solidDerivedLocalReflectionAdjunction.unit.app
        ((DerivedCategory.singleFunctor LightCondAb 0).obj P))).choose_spec

/-- The actual derived lift of a bounded family through the local reflection of P. -/
def boundedFamilyLocalLift (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ)
    (F : Finset ℤ) :
    (DerivedCategory.singleFunctor LightCondAb 0).obj (freeOn S) ⟶
      (solidDerivedLocalReflection.obj
        ((DerivedCategory.singleFunctor LightCondAb 0).obj P)).obj :=
  (DerivedCategory.singleFunctor LightCondAb 0).map (measureTailSection S) ≫
    boundedTensorLocalLift S c F

theorem localPToIntegerMeasures_unit :
    solidDerivedLocalReflectionAdjunction.unit.app
        ((DerivedCategory.singleFunctor LightCondAb 0).obj P) ≫
      solidDerivedLocal.ι.map localPToIntegerMeasures =
        (DerivedCategory.singleFunctor LightCondAb 0).map PToIntegerMeasures := by
  exact solidDerivedLocalReflectionAdjunction.homEquiv _ _ |>.apply_symm_apply _

/-- Every uniformly bounded integer family factors through the actual local
reflection of P, with the canonical measure comparison. This is a proved
concrete comparison, valid for all light profinite S, not a realization assumption. -/
theorem boundedFamilyLocalLift_comparison (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ n s, c n s ∈ F) :
    boundedFamilyLocalLift S c F ≫ solidDerivedLocal.ι.map localPToIntegerMeasures =
      (DerivedCategory.singleFunctor LightCondAb 0).map (familyToIntegerMeasures S c) := by
  haveI : IsIso (solidDerivedEndomorphism.app integerMeasuresDerivedLocal.obj) :=
    integerMeasuresDerivedLocal.property
  have h : boundedTensorLocalLift S c F ≫ solidDerivedLocal.ι.map localPToIntegerMeasures =
      (DerivedCategory.singleFunctor LightCondAb 0).map (measureTailMap S c) := by
    apply (solidTensorSingle_precomp_bijective (freeOn S) 0
      integerMeasuresDerivedLocal.obj).injective
    change (DerivedCategory.singleFunctor LightCondAb 0).map
        (oneMinusShift ▷ freeOn S) ≫
        (boundedTensorLocalLift S c F ≫ solidDerivedLocal.ι.map localPToIntegerMeasures) = _
    rw [← Category.assoc, boundedTensorLocalLift_spec, Category.assoc,
      localPToIntegerMeasures_unit, ← Functor.map_comp,
      ← boundedMeasureTensorSquare S c F hF, Functor.map_comp]
    rfl
  rw [boundedFamilyLocalLift, Category.assoc, h, ← Functor.map_comp,
    measureTailSection_tailMap]

end LightCondensed.Solid
