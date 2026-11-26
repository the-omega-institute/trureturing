import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Recovery.LocalCompression.QutritPure

/-! Source-bound readouts of the joint reconstruction error and the decoder's output. -/

noncomputable section

open Matrix LeanInformationAudit
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Recovery.LocalCompression.QutritPure

namespace Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritPure

abbrev ErrorSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => QuantumChannel Qutrit Qutrit) (fun _ => ℝ)

def jointError : Realization ErrorSignature :=
  realize ErrorSignature (fun _ _ => error) (fun e => nomatch e)

private def zeroError : Realization ErrorSignature :=
  realize ErrorSignature (fun _ _ _ => 0) (fun e => nomatch e)

private def unitError : Realization ErrorSignature :=
  realize ErrorSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev planeArena : Arena where
  signature := ErrorSignature
  Law R := ∀ U : unitaryGroup Qutrit ℂ,
    IsLeast {d : ℝ | ∃ C : QuantumChannel Qutrit Qutrit,
      PlaneSupported U C ∧ R.readout () () C = d} (2 / 3)

abbrev witnessArena : Arena where
  signature := ErrorSignature
  Law R :=
    R.readout () () ((decoder (4 / 5) (3 / 5) (by norm_num)).comp encoder) ≤
      (10189 / 15750 : ℝ) ∧ (10189 / 15750 : ℝ) < 13 / 20

private theorem zeroError_fails : ¬ planeArena.Law zeroError := by
  intro h
  obtain ⟨_, _, he⟩ := (h 1).1
  change (0 : ℝ) = 2 / 3 at he
  norm_num at he

private theorem unitError_fails : ¬ witnessArena.Law unitError := by
  intro h
  have he := h.1
  change (1 : ℝ) ≤ 10189 / 15750 at he
  norm_num at he

private theorem error_depends : ObservationalDependence ErrorSignature jointError := by
  intro i
  cases i
  obtain ⟨C, _, hC⟩ := (plane_optimum 1).1
  refine ⟨(), (decoder (4 / 5) (3 / 5) (by norm_num)).comp encoder, C, ?_⟩
  change error _ ≠ error C
  rw [hC]
  exact ne_of_lt (qubit_memory_witness.1.trans_lt (by norm_num))

def planeFamily : Registration planeArena (type_of% plane_optimum) where
  actual := jointError
  bridge := Iff.rfl
  variation := ⟨plane_optimum, zeroError, zeroError_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ zeroError_fails
  dependence := error_depends

def witnessFamily : Registration witnessArena (type_of% qubit_memory_witness) where
  actual := jointError
  bridge := Iff.rfl
  variation := ⟨qubit_memory_witness, unitError, unitError_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ unitError_fails
  dependence := error_depends

set_option linter.style.longLine false in
def planeAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    plane_optimum (Realization ErrorSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.LocalCompression.QutritPure.plane_optimum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritPure.planeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨planeArena⟩
  objectArena := .source ⟨planeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source planeArena ⟨planeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ErrorSignature (fun _ _ => error) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.QutritPure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "body", "arg", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option linter.style.longLine false in
def witnessAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    qubit_memory_witness (Realization ErrorSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.LocalCompression.QutritPure.qubit_memory_witness.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritPure.witnessFamily
  realizationSource := none
  generated := false
  arena := .source ⟨witnessArena⟩
  objectArena := .source ⟨witnessArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source witnessArena ⟨witnessFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ErrorSignature (fun _ _ => error) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.QutritPure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev DecoderSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix Qubit Qubit ℂ) (fun _ => Matrix Qutrit Qutrit ℂ)

def decoderOutput : Realization DecoderSignature :=
  realize DecoderSignature (fun _ _ X =>
    CStarMatrix.ofMatrix.symm
      ((decoder (4 / 5) (3 / 5) (by norm_num)).toCompletelyPositiveMap
        (CStarMatrix.ofMatrix X))) (fun e => nomatch e)

private def zeroOutput : Realization DecoderSignature :=
  realize DecoderSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev decoderArena : Arena where
  signature := DecoderSignature
  Law R := ¬ ∃ V : Matrix Qutrit Qubit ℂ, ∀ X : Matrix Qubit Qubit ℂ,
    R.readout () () X = V * X * Vᴴ

private theorem zeroOutput_fails : ¬ decoderArena.Law zeroOutput := by
  intro h
  apply h
  refine ⟨0, fun X => ?_⟩
  change 0 = (0 : Matrix Qutrit Qubit ℂ) * X * (0 : Matrix Qutrit Qubit ℂ)ᴴ
  simp

private theorem output_depends : ObservationalDependence DecoderSignature decoderOutput := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  let D := decoder (4 / 5) (3 / 5) (by norm_num)
  change CStarMatrix.ofMatrix.symm (D.toCompletelyPositiveMap (CStarMatrix.ofMatrix 0)) =
    CStarMatrix.ofMatrix.symm (D.toCompletelyPositiveMap (CStarMatrix.ofMatrix 1)) at he
  have ht := congrArg Matrix.trace (CStarMatrix.ofMatrix.symm.injective he)
  rw [D.trace_preserving, D.trace_preserving] at ht
  change (0 : Matrix Qubit Qubit ℂ).trace = (1 : Matrix Qubit Qubit ℂ).trace at ht
  norm_num at ht

def decoderFamily : Registration decoderArena (type_of% witness_decoder_not_isometric) where
  actual := decoderOutput
  bridge := Iff.rfl
  variation := ⟨witness_decoder_not_isometric, zeroOutput, zeroOutput_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ zeroOutput_fails
  dependence := output_depends

set_option linter.style.longLine false in
def decoderAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    witness_decoder_not_isometric (Realization DecoderSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.LocalCompression.QutritPure.witness_decoder_not_isometric.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritPure.decoderFamily
  realizationSource := none
  generated := false
  arena := .source ⟨decoderArena⟩
  objectArena := .source ⟨decoderArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source decoderArena ⟨decoderFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize DecoderSignature (fun _ _ X =>
    CStarMatrix.ofMatrix.symm
      ((decoder (4 / 5) (3 / 5) (by norm_num)).toCompletelyPositiveMap
        (CStarMatrix.ofMatrix X))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.QutritPure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.LocalCompression.QutritPure
