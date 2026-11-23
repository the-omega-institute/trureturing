import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum

/-! Source-bound readouts of the stationary parameter and the joint trace distance. -/

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Recovery.LocalCompression.QutritPure
open _root_.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset
open _root_.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum

namespace Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum

abbrev StationarySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def stationaryParameter : Realization StationarySignature :=
  realize StationarySignature (fun _ _ => stationaryLambda) (fun e => nomatch e)

private def zeroParameter : Realization StationarySignature :=
  realize StationarySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev stationaryArena : Arena where
  signature := StationarySignature
  Law R := ∃ b : ℝ, 0.80680296 < b ∧ b < 0.80680298 ∧
    1 < R.readout () () b ∧ characteristic (R.readout () () b) b = 0 ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ b → characteristic (R.readout () () b) x < 0

private theorem zeroParameter_fails : ¬ stationaryArena.Law zeroParameter := by
  rintro ⟨_, _, _, h, _, _⟩
  change (1 : ℝ) < 0 at h
  norm_num at h

private theorem stationaryParameter_depends :
    ObservationalDependence StationarySignature stationaryParameter := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change stationaryLambda 0 ≠ stationaryLambda 1
  norm_num [stationaryLambda]

def stationaryFamily : Registration stationaryArena (type_of% exists_stationary_characteristic) where
  actual := stationaryParameter
  bridge := Iff.rfl
  variation := ⟨exists_stationary_characteristic, zeroParameter, zeroParameter_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ zeroParameter_fails
  dependence := stationaryParameter_depends

set_option linter.style.longLine false in
def stationaryAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    exists_stationary_characteristic (Realization StationarySignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum.exists_stationary_characteristic.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum.stationaryFamily
  realizationSource := none
  generated := false
  arena := .source ⟨stationaryArena⟩
  objectArena := .source ⟨stationaryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stationaryArena ⟨stationaryFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize StationarySignature (fun _ _ => stationaryLambda) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev ErrorSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => QuantumChannel Qutrit Qutrit) (fun _ => ℝ)

def jointError : Realization ErrorSignature :=
  realize ErrorSignature (fun _ _ => error) (fun e => nomatch e)

private def zeroError : Realization ErrorSignature :=
  realize ErrorSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev optimumArena : Arena where
  signature := ErrorSignature
  Law R := ∃ (b c : ℝ) (h : b ^ 2 + c ^ 2 = 1),
    0.80680296 < b ∧ b < 0.80680298 ∧ 0 ≤ c ∧
    DiagonalReset encoder 0 ∧
    3 * R.readout () () ((decoder b c h).comp encoder) = stationaryLambda b ∧
    (∀ (x y : ℝ) (hxy : x ^ 2 + y ^ 2 = 1), x ∈ Set.Icc (0 : ℝ) 1 →
      x ≠ b → R.readout () () ((decoder b c h).comp encoder) <
        R.readout () () ((decoder x y hxy).comp encoder)) ∧
    (∀ (E : QuantumChannel Qutrit Qubit) (D : QuantumChannel Qubit Qutrit) (t : ℝ),
      DiagonalReset E t → R.readout () () ((decoder b c h).comp encoder) ≤
        R.readout () () (D.comp E))

private theorem zeroError_fails : ¬ optimumArena.Law zeroError := by
  rintro ⟨b, _, _, hb, _, _, _, _, hstrict, _⟩
  have hzero : (0 : ℝ) ≠ b := ne_of_lt (by linarith)
  have h := hstrict 0 1 (by norm_num) ⟨le_rfl, zero_le_one⟩ hzero
  exact (lt_irrefl (0 : ℝ)) h

private theorem jointError_depends : ObservationalDependence ErrorSignature jointError := by
  intro i
  cases i
  obtain ⟨b, c, hbc, hb, _, _, _, _, hstrict, _⟩ := pure_diagonal_reset_optimum
  have hzero : (0 : ℝ) ≠ b := ne_of_lt (by linarith)
  exact ⟨(), (decoder b c hbc).comp encoder, (decoder 0 1 (by norm_num)).comp encoder,
    ne_of_lt (hstrict 0 1 (by norm_num) ⟨le_rfl, zero_le_one⟩ hzero)⟩

def optimumFamily : Registration optimumArena (type_of% pure_diagonal_reset_optimum) where
  actual := jointError
  bridge := Iff.rfl
  variation := ⟨pure_diagonal_reset_optimum, zeroError, zeroError_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ zeroError_fails
  dependence := jointError_depends

set_option linter.style.longLine false in
def optimumAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    pure_diagonal_reset_optimum (Realization ErrorSignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum.pure_diagonal_reset_optimum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum.optimumFamily
  realizationSource := none
  generated := false
  arena := .source ⟨optimumArena⟩
  objectArena := .source ⟨optimumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source optimumArena ⟨optimumFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ErrorSignature (fun _ _ => error) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg",
        "fn", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum
