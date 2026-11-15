/- GID: D5/S3/Quantum/FourierCircuit/Components/Gates/Construction
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/Gates/Construction
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
Original file: QuantumAlg/Components/Gates/Construction.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Components.GateModel.Algorithm
import all D5.S3.Quantum.FourierCircuit.Components.GateModel.Algorithm
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement.Construction
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement.Construction
public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit
import all D5.S3.Quantum.FourierCircuit.Core.Base.Accounting.Event
import all D5.S3.Quantum.FourierCircuit.Core.Base.Accounting.ResourcePool

/-!
# Default native gates at physical positions

The default algorithm language has Toffoli, CNOT and an arbitrary one-qubit
unitary. These constructors select actual ambient wires in argument order.
Each selected wire must be a qubit, and control and target positions must be
distinct. All unselected systems, including non-qubit systems, are spectators.
The oracle declaration is retained independently and grants no extra gates.
-/

namespace QuantumAlg.Gate

noncomputable section

variable {count : Nat} (layout : QuantumLayout count)

/-- Place the actual one-qubit operator on one dimension-two ambient system. -/
@[expose]
public def singleQubitApplication (operator : UnitaryOperator (Qubits 1))
    (target : Fin count) (qubit : (layout.wire target).dimension = 2) :
    GateModel.Application AlgorithmGate.model layout :=
  GateModel.Application.ofPositions AlgorithmGate.model (.singleQubit operator) layout
    ⟨fun _ => target, fun _ _ _ => Subsingleton.elim (α := Fin 1) _ _⟩ (fun _ => qubit)

/-- Execute one actual one-qubit gate in the default algorithm model. -/
public def singleQubitAt (oracles : OracleModel) (operator : UnitaryOperator (Qubits 1))
    (target : Fin count) (qubit : (layout.wire target).dimension = 2) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  .native (singleQubitApplication layout operator target qubit)


end

end QuantumAlg.Gate
