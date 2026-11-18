/- GID: D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Construction
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Construction
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
Original file: QuantumAlg/Components/Gates/ControlledPhase/Construction.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Operator
import all D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Operator
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary.Reindex
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary.Reindex
public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature

/-!
# Independent local controlled-phase operator

The two-qubit target preserves the original angle and big-endian labels.
-/

namespace QuantumAlg.Gate.ControlledPhase

noncomputable section

/-- The two ordered physical qubits of the local operator. -/
@[expose, implicit_reducible]
public def layout : QuantumLayout 2 := (QuantumSignature.qubits 2).canonicalPlacement.layout

/-- The unchanged addressed controlled-phase target in the physical-layout basis. -/
public def operator (angle : Real) : UnitaryOperator layout.register :=
  UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm
    (qftControlledPhaseOperator (n := 2) 0 1 angle)

end

end QuantumAlg.Gate.ControlledPhase
