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
Library/Quantum/qudeleap2026qft.md.
Modified for receiver module paths and the retained QFT proof slice.
Source: QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Original file: QuantumAlg/Components/Gates/ControlledPhase/Construction.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Components.Gates.Construction
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Construction
public import D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Operator
import all D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Operator
public import D5.S3.Quantum.FourierCircuit.Components.Gates.PhaseOperator
import all D5.S3.Quantum.FourierCircuit.Components.Gates.PhaseOperator
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement.Canonical
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature

/-!
# Native phase and CNOT word for controlled phase

The implementation contains three actual one-qubit phase gates and two actual
CNOTs, with both physical qubits present throughout. The original addressed
controlled-phase operator is an independent target. The macro retains the
entire native word, including every sequential event and dependency.
-/

namespace QuantumAlg.Gate.ControlledPhase

noncomputable section

/-- The two ordered physical qubits of the local expansion. -/
@[expose, implicit_reducible]
public def layout : QuantumLayout 2 := (QuantumSignature.qubits 2).canonicalPlacement.layout

/-- The unchanged addressed controlled-phase target in the physical-layout basis. -/
public def operator (angle : Real) : UnitaryOperator layout.register :=
  UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm
    (qftControlledPhaseOperator (n := 2) 0 1 angle)

/-- Execute all three phase gates and both CNOTs without a new controlled-gate token. -/
public def circuit (oracles : OracleModel) (angle : Real) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  let first := singleQubitAt layout oracles (phaseGateOp (angle / 2)) 0 rfl
  let second := singleQubitAt layout oracles (phaseGateOp (angle / 2)) 1 rfl
  let middle := singleQubitAt layout oracles (phaseGateOp (-(angle / 2))) 1 rfl
  let controlled : UnitaryCircuit AlgorithmGate.model oracles layout :=
    .native (GateModel.Application.canonical AlgorithmGate.model .cnot)
  .macroCall "controlled-phase" ((((first.seq second).seq controlled).seq middle).seq controlled)
 [.gate .singleQubit, .gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot] := by
  rfl
circuit oracles angle).evaluatedEventDepth (fun _ => 1) = 5 := by
  rfl
circuit oracles angle).macroCount "controlled-phase" = 1 := by
  rfl

end

end QuantumAlg.Gate.ControlledPhase
