import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetDistortion

/-! Source-bound readout of the joint trace distance. -/

noncomputable section

open Matrix LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Recovery.LocalCompression.QutritPure
open _root_.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset
open _root_.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetDistortion

namespace Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetDistortion

open private encoder_apply from D5.S3.Quantum.Recovery.LocalCompression.QutritPure

abbrev ErrorSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => QuantumChannel Qutrit Qutrit) (fun _ => ℝ)

def jointError : Realization ErrorSignature :=
  realize ErrorSignature (fun _ _ => error) (fun e => nomatch e)

private def zeroError : Realization ErrorSignature :=
  realize ErrorSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev distortionArena : Arena where
  signature := ErrorSignature
  Law R := ∀ (E : QuantumChannel Qutrit Qubit) (D : QuantumChannel Qubit Qutrit) (t : ℝ),
    DiagonalReset E t → ∃ (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1),
      x = amplitude D ∧ 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧
      IsGreatest {s : ℝ | ∃ v : Qutrit → ℝ, (∑ i, v i ^ 2) = 1 ∧
        quadratic (modelBlock x) v = s} (3 * R.readout () () ((decoder x y h).comp encoder)) ∧
      error ((decoder x y h).comp encoder) ≤ error (D.comp E)

private theorem zeroError_fails : ¬ distortionArena.Law zeroError := by
  intro h
  have hE : DiagonalReset encoder 0 := by
    refine ⟨le_rfl, zero_le_one, fun X => ?_⟩
    rw [encoder_apply]
    simp
  obtain ⟨x, _, _, _, _, _, _, hmax, _⟩ := h encoder (decoder 1 0 (by norm_num)) 0 hE
  have h₁ : 1 - x ^ 2 ≤ 0 := by
    have hm : 1 - x ^ 2 ∈ {s : ℝ | ∃ v : Qutrit → ℝ, (∑ i, v i ^ 2) = 1 ∧
        quadratic (modelBlock x) v = s} :=
      ⟨![0, 1, 0], by norm_num [Fin.sum_univ_three],
        by norm_num [quadratic, modelBlock, Fin.sum_univ_three]⟩
    have hb := hmax.2 hm
    change 1 - x ^ 2 ≤ 3 * (0 : ℝ) at hb
    simpa only [mul_zero] using hb
  have h₂ : x ^ 2 ≤ 0 := by
    have hm : x ^ 2 ∈ {s : ℝ | ∃ v : Qutrit → ℝ, (∑ i, v i ^ 2) = 1 ∧
        quadratic (modelBlock x) v = s} :=
      ⟨![0, 0, 1], by norm_num [Fin.sum_univ_three],
        by norm_num [quadratic, modelBlock, Fin.sum_univ_three]⟩
    have hb := hmax.2 hm
    change x ^ 2 ≤ 3 * (0 : ℝ) at hb
    simpa only [mul_zero] using hb
  linarith

private theorem error_depends : ObservationalDependence ErrorSignature jointError := by
  intro i
  cases i
  obtain ⟨C, _, hC⟩ := (plane_optimum 1).1
  refine ⟨(), (decoder (4 / 5) (3 / 5) (by norm_num)).comp encoder, C, ?_⟩
  change error _ ≠ error C
  rw [hC]
  exact ne_of_lt (qubit_memory_witness.1.trans_lt (by norm_num))

def distortionFamily : Registration distortionArena
    (type_of% diagonal_reset_distortion_converse) where
  actual := jointError
  bridge := Iff.rfl
  variation := ⟨diagonal_reset_distortion_converse, zeroError, zeroError_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ zeroError_fails
  dependence := error_depends

set_option linter.style.longLine false in
def distortionAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    diagonal_reset_distortion_converse (Realization ErrorSignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetDistortion.diagonal_reset_distortion_converse.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetDistortion.distortionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨distortionArena⟩
  objectArena := .source ⟨distortionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source distortionArena ⟨distortionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ErrorSignature (fun _ _ => error) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetDistortion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "fn", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetDistortion
