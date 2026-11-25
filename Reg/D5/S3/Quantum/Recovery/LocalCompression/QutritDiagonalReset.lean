import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset

/-! Source-bound readout of the matched Bell block for plane-preserving resets. -/

noncomputable section

open Matrix LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Recovery.LocalCompression.QutritPure
open _root_.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset

namespace Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset

open private attenuating_block from D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset
open private encoder_apply from D5.S3.Quantum.Recovery.LocalCompression.QutritPure

abbrev BlockSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => QuantumChannel Qutrit Qutrit) (fun _ => Matrix Qutrit Qutrit ℝ)

def bellBlock : Realization BlockSignature :=
  realize BlockSignature (fun _ _ => matchedBlock) (fun e => nomatch e)

private def zeroBlock : Realization BlockSignature :=
  realize BlockSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev comparisonArena : Arena where
  signature := BlockSignature
  Law R := ∀ (E : QuantumChannel Qutrit Qubit) (D : QuantumChannel Qubit Qutrit)
      (t : ℝ), DiagonalReset E t →
    ∃ (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1),
      x = amplitude D ∧ 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧
      R.readout () () ((decoder x y h).comp encoder) = modelBlock x ∧
      ∀ i j, modelBlock x i j ≤
        matchedBlock (D.comp E) (matchedOrder D i) (matchedOrder D j)

private theorem zeroBlock_fails : ¬ comparisonArena.Law zeroBlock := by
  intro h
  have hE : DiagonalReset encoder 0 := by
    refine ⟨le_rfl, zero_le_one, fun X => ?_⟩
    rw [encoder_apply]
    simp
  obtain ⟨x, _, _, _, _, _, _, hblock, _⟩ := h encoder (decoder 1 0 (by norm_num)) 0 hE
  have he := congrArg (fun M : Matrix Qutrit Qutrit ℝ => M 0 2) hblock
  change (0 : ℝ) = 1 at he
  norm_num at he

private theorem block_depends : ObservationalDependence BlockSignature bellBlock := by
  intro i
  cases i
  refine ⟨(), (decoder 1 0 (by norm_num)).comp encoder,
    (decoder 0 1 (by norm_num)).comp encoder, ?_⟩
  change matchedBlock _ ≠ matchedBlock _
  rw [attenuating_block, attenuating_block]
  intro h
  have he := congrArg (fun M : Matrix Qutrit Qutrit ℝ => M 1 1) h
  norm_num [modelBlock] at he

def comparisonFamily : Registration comparisonArena (type_of% diagonal_reset_bell_comparison) where
  actual := bellBlock
  bridge := Iff.rfl
  variation := ⟨diagonal_reset_bell_comparison, zeroBlock, zeroBlock_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ zeroBlock_fails
  dependence := block_depends

set_option linter.style.longLine false in
def comparisonAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    diagonal_reset_bell_comparison (Realization BlockSignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset.diagonal_reset_bell_comparison.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset.comparisonFamily
  realizationSource := none
  generated := false
  arena := .source ⟨comparisonArena⟩
  objectArena := .source ⟨comparisonArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source comparisonArena ⟨comparisonFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize BlockSignature (fun _ _ => matchedBlock) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset
