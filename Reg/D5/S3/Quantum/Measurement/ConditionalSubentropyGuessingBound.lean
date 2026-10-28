import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound
import Reg.Support.DependentFamily

/-! Source-bound audits of simplex volume and its null sum boundary. -/

namespace Reg.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound

open _root_.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe equality of extended nonnegative real volumes. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hbad : (1 : ℝ≥0∞) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero hbad

namespace SimplexVolume

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ,
    r.readout () () (volume (simplexCoords (n + 1))) (n.factorial : ℝ≥0∞)⁻¹

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 (simplex_volume 0)

def source_registration : Registration arena (type_of% @simplex_volume) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨simplex_volume, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@simplex_volume) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.SimplexVolume.unit
  realizationName :=
    .str `Reg.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.SimplexVolume
      "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SimplexVolume

namespace SimplexSumBoundaryNull

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (t : ℝ), 0 < t →
    r.readout () () (volume {u : Fin n → ℝ | ∑ i, u i = t}) 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 zero_lt_one (simplex_sum_boundary_null 1 1 zero_lt_one)

def source_registration : Registration arena (type_of% @simplex_sum_boundary_null) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨simplex_sum_boundary_null, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@simplex_sum_boundary_null) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.SimplexSumBoundaryNull.unit
  realizationName :=
    .str `Reg.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.SimplexSumBoundaryNull
      "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SimplexSumBoundaryNull

end
end Reg.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound
