/- GID: D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Placement
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Placement
   mirror-E: none(waiver:source-transfer-proof)
   anchors: []
   utility: none
   digest: Licensed original QFT circuit proof support. -/

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0; the full license is in
Library/Quantum/qudeleap2026qft.md.
Modified for receiver module paths and the retained QFT proof slice.
Source: QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Original file: QuantumAlg/Components/Gates/ControlledPhase/Placement.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Construction
import all D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Construction
import all D5.S3.Quantum.FourierCircuit.Components.Gates.PhaseOperator
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Construction
import all D5.S3.Quantum.FourierCircuit.Components.GateModel.Algorithm
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement.Diagonal
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit

/-!
# Exact physical phases in the native controlled-phase word

The one-qubit phase is read from the original token and its actual selected
wire. The other physical qubit remains an unchanged spectator, including all
off-diagonal coherences when the resulting operator acts on a joint state.
-/

namespace QuantumAlg.Gate.ControlledPhase

noncomputable section

private lemma phase_token_diagonal (angle : Real) :
    ((AlgorithmGate.model.operator (.singleQubit (phaseGateOp angle))).val :
      HilbertOperator (QuantumSignature.qubits 1).register) =
        Matrix.diagonal (fun basis =>
          if QuantumSignature.qubitsIndexEquiv 1 basis = 0 then 1 else
            Complex.exp ((angle : Complex) * Complex.I)) := by
  ext row column
  change (phaseGateOp angle : HilbertOperator (Qubits 1))
    (QuantumSignature.qubitsIndexEquiv 1 row) (QuantumSignature.qubitsIndexEquiv 1 column) = _
  rw [phaseGateOp_diagonal]
  simp only [Matrix.diagonal_apply, Equiv.apply_eq_iff_eq]

/-- Each actual phase occurrence acts on exactly the selected bit of the full two-qubit basis. -/
public lemma controlledPhase_single_phase_diagonal (oracles : OracleModel) (angle : Real)
    (target : Fin 2) (environment : oracles.Interpretation) :
    (((singleQubitAt layout oracles (phaseGateOp angle) target rfl).matrix environment) :
      HilbertOperator layout.register) =
        Matrix.diagonal (fun basis => if basis target = 0 then 1 else
          Complex.exp ((angle : Complex) * Complex.I)) := by
  let application := singleQubitApplication layout (phaseGateOp angle) target rfl
  have selected (basis : layout.Basis) :
      QuantumSignature.qubitsIndexEquiv 1 (application.basisEquiv basis).1 = basis target := by
    have coordinates : (application.basisEquiv basis).1 = fun _ => basis target := by
      funext index
      fin_cases index
      apply Fin.ext
      rfl
    rw [coordinates]
    generalize basis target = bit
    fin_cases bit <;> rfl
  have actual := application.application_operator_diagonal
    (fun basis => if QuantumSignature.qubitsIndexEquiv 1 basis = 0 then 1 else
      Complex.exp ((angle : Complex) * Complex.I)) (phase_token_diagonal angle)
  refine actual.trans ?_
  apply congrArg Matrix.diagonal
  funext basis
  rw [selected]
  rfl

end

end QuantumAlg.Gate.ControlledPhase
