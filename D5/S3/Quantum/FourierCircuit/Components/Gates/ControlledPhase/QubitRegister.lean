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
Library/Fourier/qudeleap2026qft.md.
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
# Native ControlledPhase on the original qubit register

The original placement proof identifies the independently defined local operator
with its addressed target, including every spectator coordinate and exact phase.
-/

namespace QuantumAlg.Gate.ControlledPhase

noncomputable section

/-- The original ordered register of the supplied number of physical qubits. -/
@[expose, implicit_reducible]
public def qubitLayout (width : Nat) : QuantumLayout width :=
  (QuantumSignature.qubits width).canonicalPlacement.layout

/-- The placed native operator has the unchanged addressed target on every register state. -/
public lemma controlledPhase_qubitOperator_matrix {width : Nat}
    (control target : Fin width) (distinct : control ≠ target) (angle : Real) :
    placedOperator (qubitLayout width) control target distinct rfl rfl angle =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm
        (qftControlledPhaseOperator control target angle) := by
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


end

end QuantumAlg.Gate.ControlledPhase
