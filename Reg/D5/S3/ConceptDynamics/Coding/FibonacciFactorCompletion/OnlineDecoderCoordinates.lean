import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
open _root_.D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open _root_.D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates

noncomputable section

abbrev coordinateSignature : Signature where
  Params := Σ _ : ℕ → CLabel, ℕ → ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def coordinateActual : Realization coordinateSignature :=
  realize coordinateSignature (fun _ params p => params.2 p) (fun e => nomatch e)

def coordinateRejected : Realization coordinateSignature :=
  realize coordinateSignature (fun _ params p => params.2 p + 1) (fun e => nomatch e)

abbrev coordinateArena : Arena where
  signature := coordinateSignature
  Law R := ∀ (a : ℕ → CLabel) (x : ℕ → ℝ), OperationOmega a x →
    ∃ d : LegalDigits,
      (∀ p, window d p = labelWindow (a p)) ∧
      (∀ p, R.readout () ⟨a, x⟩ p = kappa (bitShift d (3 * p)))

theorem coordinate_rejected_law : ¬ coordinateArena.Law coordinateRejected := by
  intro h
  have hzero : OperationOmega
      (_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.address [])
      (_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.coordinate []) :=
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.literal_address_path
      .G0 .G0 [] rfl
  obtain ⟨d, hw, hc⟩ := h _ _ hzero
  have hwindow : ∀ p, window d p = nullLabel := by
    intro p
    simpa [_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.address,
      labelWindow] using hw p
  have hk : kappa d = 0 := by simp [kappa, hwindow, offset, nullLabel]
  have hvalue := hc 0
  simp [coordinateRejected, realize, bitShift,
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.coordinate,
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.compose] at hvalue
  exact one_ne_zero (hvalue.trans hk)

def coordinateRegistration : Registration coordinateArena
    (∀ (a : ℕ → CLabel) (x : ℕ → ℝ), OperationOmega a x →
      ∃ d : LegalDigits, (∀ p, window d p = labelWindow (a p)) ∧
        (∀ p, x p = kappa (bitShift d (3 * p)))) where
  actual := coordinateActual
  bridge := Iff.rfl
  variation := ⟨operation_coordinate_bridge, coordinateRejected, coordinate_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coordinateRejected, ?_, rfl, coordinate_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.address [.L2],
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.coordinate [.L2]⟩,
      0, 1, ?_⟩
    norm_num [coordinateActual, realize,
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.coordinate,
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.compose,
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.branch,
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.shift]

def operation_coordinate_bridge_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.operation_coordinate_bridge)
      (type_of% (realize.{0,0,0,0,0} coordinateSignature
        (fun _ params p => params.2 p) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.operation_coordinate_bridge_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.coordinateRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨coordinateArena⟩
  objectArena := .source ⟨coordinateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coordinateArena ⟨coordinateRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} coordinateSignature
    (fun _ params p => params.2 p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
