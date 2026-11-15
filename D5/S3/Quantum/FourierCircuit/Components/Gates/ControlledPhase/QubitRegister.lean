/- GID: D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/QubitRegister
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/QubitRegister
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
Original file: QuantumAlg/Components/Gates/ControlledPhase/QubitRegister.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Physical
import all D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Physical
import all D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Construction
public import D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Coordinates
import all D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Coordinates
public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement.Diagonal
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement.Diagonal
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement.Entries
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature

/-!
# Native controlled phase with the original qubit-register target

The exact target is the existing addressed operator on big-endian integer
labels. Reindexing only translates that fixed label convention to the physical
layout basis. The implementation contains the complete native five-gate word.
-/

namespace QuantumAlg.Gate.ControlledPhase

noncomputable section

/-- The original ordered register of the supplied number of physical qubits. -/
@[expose, implicit_reducible]
public def qubitLayout (width : Nat) : QuantumLayout width :=
  (QuantumSignature.qubits width).canonicalPlacement.layout

/-- Execute the full native word at two distinct positions of the original qubit register. -/
public def qubitCircuit (oracles : OracleModel) {width : Nat}
    (control target : Fin width) (distinct : control ≠ target) (angle : Real) :
    UnitaryCircuit AlgorithmGate.model oracles (qubitLayout width) :=
  circuitAt (qubitLayout width) control target distinct rfl rfl oracles angle

/-- The native implementation realizes the unchanged addressed target on every register state. -/
public lemma controlledPhase_qubitCircuit_matrix (oracles : OracleModel) {width : Nat}
    (control target : Fin width) (distinct : control ≠ target) (angle : Real) (environment :
      oracles.Interpretation) :
    ((qubitCircuit oracles control target distinct angle).matrix environment) =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm
        (qftControlledPhaseOperator control target angle) := by
  rw [qubitCircuit, controlledPhase_circuitAt_matrix]
  apply Subtype.ext
  have localDiagonal : (operator angle : HilbertOperator layout.register) =
      Matrix.diagonal (fun (basis : Fin 2 → Fin 2) =>
        if finTwoEquiv (basis 0) && finTwoEquiv (basis 1) then
          Complex.exp ((angle : Complex) * Complex.I) else 1) :=
    qftControlledPhaseOperator_coordinates (width := 2) 0 1 angle
  refine (UnitaryCircuit.operatorAt_diagonal layout (qubitLayout width)
    (positions control target distinct)
    (dimensions (qubitLayout width) control target distinct rfl rfl)
    (operator angle) _ localDiagonal).trans ?_
  rw [qftControlledPhaseOperator_coordinates]
  apply congrArg Matrix.diagonal
  funext basis
  have first :
      UnitaryCircuit.selectedInput layout (qubitLayout width) (positions control target distinct)
        (dimensions (qubitLayout width) control target distinct rfl rfl) basis (0 : Fin 2) =
          basis control := by
    apply Fin.ext
    rfl
  have second :
      UnitaryCircuit.selectedInput layout (qubitLayout width) (positions control target distinct)
        (dimensions (qubitLayout width) control target distinct rfl rfl) basis (1 : Fin 2) =
          basis target := by
    apply Fin.ext
    rfl
  rw [first, second]
dPhase_circuitAt_events (qubitLayout width) control target distinct rfl rfl
    oracles angle

end

end QuantumAlg.Gate.ControlledPhase
