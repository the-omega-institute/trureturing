/- GID: D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/GateModel/Fourier
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
Original file: QuantumAlg/Components/GateModel/Fourier.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Model
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Model
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
public import D5.S3.Quantum.FourierCircuit.Components.Gates.Operator
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Operator
public import D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Construction
import all D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Construction
public import D5.S3.Quantum.FourierCircuit.Components.Gates.Swap
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Swap

/-!
# The natural gate model of the quantum Fourier transform

Hadamard, an exact controlled phase with its real angle, and SWAP are native
instructions in this model. Their operators are independent of any later
compilation into the default algorithm gate model.
-/

namespace QuantumAlg.FourierGate

/-- The three independently counted Fourier instructions. -/
public inductive Coordinate where
  | hadamard
  | controlledPhase
  | swap
deriving DecidableEq

/-- A controlled-phase token retains its full angle, including its sign. -/
public inductive Token where
  | hadamard
  | controlledPhase (angle : Real)
  | swap

/-- A Hadamard acts on one qubit; each phase or SWAP acts on two qubits. -/
@[expose, implicit_reducible]
public def signature : Token → QuantumSignature
  | .hadamard => .qubits 1
  | .controlledPhase _ => .qubits 2
  | .swap => .qubits 2

/-- Count source instructions without discarding their operator parameters. -/
@[expose]
public def coordinate : Token → Coordinate
  | .hadamard => .hadamard
  | .controlledPhase _ => .controlledPhase
  | .swap => .swap

noncomputable section

/-- Exact local operators, with no identification modulo global phase. -/
@[expose]
public def operator : (token : Token) → UnitaryOperator (signature token).register
  | .hadamard =>
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm Gate.HOp
  | .controlledPhase angle => Gate.ControlledPhase.operator angle
  | .swap => Gate.Swap.operator

/-- The natural native language of the canonical Fourier construction. -/
@[expose, implicit_reducible]
public def model : GateModel where
  Token := Token
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature := signature
  operator := operator
  coordinate := coordinate

end
end QuantumAlg.FourierGate
