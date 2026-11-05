import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.HyperbolicHausdorffDimension
import Reg.Support.DependentFamily

/-! Natural-dimensional Hausdorff density as a dependent family of measures. -/

open _root_.D5.S3.Geometry.HyperbolicUpperHalfSpace
open _root_.D5.S3.Geometry.HyperbolicNormalizedDensity (coordinatesEquiv)
open _root_.D5.S3.Geometry.HyperbolicHausdorffDimension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace Reg.D5.S3.Geometry.HyperbolicHausdorffDimension

private local instance : MeasurableSpace (UpperHalfSpace ℂ) := borel _
private local instance : BorelSpace (UpperHalfSpace ℂ) := ⟨rfl⟩
private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure (UpperHalfSpace ℂ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => (rawNativeMeasureDim d).map coordinatesEquiv)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : ℕ, R.readout () () d =
    (rawCoordinateMeasureDim d).withDensity (heightDensityDim d)

private def nativePoint : HyperbolicThreeSpace :=
  ⟨⟨WithLp.toLp 2 ((0 : ℂ), (1 : ℝ)), by norm_num⟩⟩

private theorem coordinate_singleton_preimage :
    coordinatesEquiv ⁻¹' ({coordinatesEquiv nativePoint} : Set (UpperHalfSpace ℂ)) =
      {nativePoint} := by
  ext y
  change coordinatesEquiv y = coordinatesEquiv nativePoint ↔ y = nativePoint
  exact coordinatesEquiv.injective.eq_iff

private theorem zero_dimension_singleton :
    ((rawNativeMeasureDim 0).map coordinatesEquiv)
      {coordinatesEquiv nativePoint} = 1 := by
  rw [coordinatesEquiv.map_apply, coordinate_singleton_preimage]
  simp [rawNativeMeasureDim]

private theorem one_dimension_singleton :
    ((rawNativeMeasureDim 1).map coordinatesEquiv)
      {coordinatesEquiv nativePoint} = 0 := by
  rw [coordinatesEquiv.map_apply, coordinate_singleton_preimage]
  letI := Measure.nullSingletonClass_hausdorff HyperbolicThreeSpace
    (by norm_num : (0 : ℝ) < 1)
  have hs : (Measure.hausdorffMeasure (1 : ℝ) : Measure HyperbolicThreeSpace)
      {nativePoint} = 0 := measure_singleton nativePoint
  simpa only [rawNativeMeasureDim, Nat.cast_one] using hs

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0
  change (0 : Measure (UpperHalfSpace ℂ)) =
    (rawCoordinateMeasureDim 0).withDensity (heightDensityDim 0) at he
  rw [← raw_native_density_nat 0] at he
  have hx := congrArg
    (fun μ : Measure (UpperHalfSpace ℂ) => μ {coordinatesEquiv nativePoint}) he
  norm_num [zero_dimension_singleton] at hx

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.Geometry.HyperbolicHausdorffDimension.raw_native_density_nat)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨raw_native_density_nat, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have hx := congrArg
      (fun μ : Measure (UpperHalfSpace ℂ) => μ {coordinatesEquiv nativePoint}) h
    change ((rawNativeMeasureDim 0).map coordinatesEquiv) {coordinatesEquiv nativePoint} =
      ((rawNativeMeasureDim 1).map coordinatesEquiv) {coordinatesEquiv nativePoint} at hx
    rw [zero_dimension_singleton, one_dimension_singleton] at hx
    exact one_ne_zero hx

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.HyperbolicHausdorffDimension.raw_native_density_nat)
    (type_of% (realize signature
      (fun _ _ d => (rawNativeMeasureDim d).map coordinatesEquiv) (fun e => nomatch e)))
    Unit Unit := {
  unitName :=
    `D5.S3.Geometry.HyperbolicHausdorffDimension.raw_native_density_nat.native_measure_unit,
  realizationName := `Reg.D5.S3.Geometry.HyperbolicHausdorffDimension.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ _ d => (rawNativeMeasureDim d).map coordinatesEquiv) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.HyperbolicHausdorffDimension,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
end Reg.D5.S3.Geometry.HyperbolicHausdorffDimension
