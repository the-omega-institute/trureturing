import D5.S3.Combinatorics.Partitions.NiuQ15
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source registrations for the cardinality, count ratio and limiting law. -/

open LeanInformationAudit Filter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.NiuTableauCount
open NiuQ15 NiuQ15.Analytic
open scoped Topology

namespace Reg.D5.S3.Combinatorics.Partitions.NiuQ15

abbrev shapeSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ RowShape (fun _ => ℚ)

def shiftedReadout : Realization shapeSignature :=
  realize shapeSignature (fun _ _ shape => shiftedCount shape.rows) (fun e => nomatch e)

def zeroShapeReadout : Realization shapeSignature :=
  realize shapeSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev shapeArena : Arena where
  signature := shapeSignature
  Law r := ∀ {k : ℕ}, 2 ≤ k → ∀ shape : RowShape k,
    (Fintype.card (StandardTableau shape) : ℚ) = r.readout () k shape

private theorem zeroShapeReadout_fails : ¬ shapeArena.Law zeroShapeReadout := by
  intro h
  let shape := rectangle 1 0
  have hz : size shape = 0 := by simp [shape, size_rectangle]
  have hc := h (k := 2) (by decide) shape
  change (Fintype.card (StandardTableau shape) : ℚ) = 0 at hc
  rw [card_standardTableau_of_size_zero shape hz, Nat.cast_one] at hc
  exact one_ne_zero hc

private theorem shiftedReadout_depends : ObservationalDependence shapeSignature shiftedReadout := by
  intro i
  refine ⟨2, rectangle 1 0, rotatedShape 1 2 1, ?_⟩
  change shiftedCount (rectangle 1 0).rows ≠ shiftedCount (rotatedShape 1 2 1).rows
  decide +kernel

def shapeFamily : Registration shapeArena (type_of% @card_standardTableau_eq_shiftedCount) where
  actual := shiftedReadout
  bridge := Iff.rfl
  variation := ⟨@card_standardTableau_eq_shiftedCount, zeroShapeReadout, zeroShapeReadout_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    shapeArena.Law shiftedReadout zeroShapeReadout zeroShapeReadout_fails
  dependence := shiftedReadout_depends

def shapeRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@card_standardTableau_eq_shiftedCount) (type_of% shiftedReadout) Unit Unit where
  unitName := `NiuQ15.card_standardTableau_eq_shiftedCount.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.NiuQ15.shapeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨shapeArena⟩
  objectArena := .source ⟨shapeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shapeArena ⟨shapeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize shapeSignature (fun _ _ shape => shiftedCount shape.rows)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.NiuQ15
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev ratioSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def coefficientReadout : Realization ratioSignature :=
  realize ratioSignature (fun _ k r => tailCoefficient (k + 2) r) (fun e => nomatch e)

def zeroCoefficientReadout : Realization ratioSignature :=
  realize ratioSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev ratioArena : Arena where
  signature := ratioSignature
  Law f := ∀ k n r, 0 < n → r ≤ n →
    Fintype.card (StandardTableau (rotatedShape (k + 1) n r)) * ((k + 2) * n).descFactorial r =
      Fintype.card (StandardTableau (rectangle (k + 1) n)) * f.readout () k r * n.descFactorial r

private theorem zeroCoefficientReadout_fails : ¬ ratioArena.Law zeroCoefficientReadout := by
  intro h
  have hrect : rotatedShape 1 1 0 = rectangle 1 1 := by simp [rotatedShape, rectangle]
  have hc := h 0 1 0 (by decide) (by decide)
  change Fintype.card (StandardTableau (rotatedShape 1 1 0)) * 1 = _ * 0 * 1 at hc
  rw [hrect, Nat.mul_one, Nat.mul_zero, Nat.zero_mul] at hc
  exact (rectangle_card_pos 1 1).ne' hc

private theorem coefficientReadout_depends :
    ObservationalDependence ratioSignature coefficientReadout := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change tailCoefficient 2 0 ≠ tailCoefficient 2 1
  decide

def ratioFamily : Registration ratioArena (type_of% exactRectangleTailCount) where
  actual := coefficientReadout
  bridge := Iff.rfl
  variation := ⟨exactRectangleTailCount, zeroCoefficientReadout, zeroCoefficientReadout_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    ratioArena.Law coefficientReadout zeroCoefficientReadout zeroCoefficientReadout_fails
  dependence := coefficientReadout_depends

def ratioRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      exactRectangleTailCount (type_of% coefficientReadout) Unit Unit where
  unitName := `NiuQ15.exactRectangleTailCount.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.NiuQ15.ratioFamily
  realizationSource := none
  generated := false
  arena := .source ⟨ratioArena⟩
  objectArena := .source ⟨ratioArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ratioArena ⟨ratioFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ratioSignature (fun _ k r => tailCoefficient (k + 2) r)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.NiuQ15
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev paritySignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → ℝ)

noncomputable def parityReadout : Realization paritySignature :=
  realize paritySignature (fun _ _ => rectangleOddEntryProbability) (fun e => nomatch e)

def zeroParityReadout : Realization paritySignature :=
  realize paritySignature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev limitArena : Arena where
  signature := paritySignature
  Law f := ∀ k : ℕ,
    (∀ r, Tendsto (fun n => rectangleTailProbability k n r) atTop (𝓝 (limitTail (k + 2) r))) ∧
    (∀ r, Tendsto (fun n => rectanglePointProbability k n r) atTop (𝓝 (limitMass (k + 2) r))) ∧
    HasSum (limitMass (k + 2)) 1 ∧
    Tendsto (f.readout () () k) atTop (𝓝 ((((k : ℝ) + 2) / ((k : ℝ) + 3)) ^ (k + 2)))

private theorem zeroParityReadout_fails : ¬ limitArena.Law zeroParityReadout := by
  intro h
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have he := tendsto_nhds_unique (h 0).2.2.2 hzero
  norm_num at he

private theorem parityReadout_depends : ObservationalDependence paritySignature parityReadout := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change rectangleOddEntryProbability 0 ≠ rectangleOddEntryProbability 1
  intro heq
  have hleft := (rectangleQuestion15 0).2.2.2
  have hright := (rectangleQuestion15 1).2.2.2
  rw [← heq] at hright
  have he := tendsto_nhds_unique hleft hright
  norm_num at he

noncomputable def limitFamily : Registration limitArena (type_of% rectangleQuestion15) where
  actual := parityReadout
  bridge := Iff.rfl
  variation := ⟨rectangleQuestion15, zeroParityReadout, zeroParityReadout_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    limitArena.Law parityReadout zeroParityReadout zeroParityReadout_fails
  dependence := parityReadout_depends

noncomputable def limitRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      rectangleQuestion15 (type_of% parityReadout) Unit Unit where
  unitName := `NiuQ15.rectangleQuestion15.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.NiuQ15.limitFamily
  realizationSource := none
  generated := false
  arena := .source ⟨limitArena⟩
  objectArena := .source ⟨limitArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source limitArena ⟨limitFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize paritySignature (fun _ _ => rectangleOddEntryProbability)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.NiuQ15
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Partitions.NiuQ15
