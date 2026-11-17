/- GID: D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm
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
Original file: QuantumAlg/Components/GateModel/Algorithm.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Model
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Model
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
import all D5.S3.Quantum.FourierCircuit.Core.Base.Control.Operator
public import D5.S3.Quantum.FourierCircuit.Components.QubitPrimitive.Operator
import all D5.S3.Quantum.FourierCircuit.Components.QubitPrimitive.Operator
public import D5.S3.Quantum.FourierCircuit.Components.Gates.Operator
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Operator

/-!
# Default algorithm gate model

Elementary operations are Toffoli, CNOT, and an arbitrary one-qubit unitary.
The one-qubit coordinate counts the actual unitary token without discarding it.
Preparation, measurement and oracle access are separate execution operations.

Resource design priorities are qubit count, then Toffoli count, then quantum
computation time, then CNOT and single-qubit counts. This is guidance rather than
a lexicographic order or a fixed exchange rate: a small constant or logarithmic
workspace increase may justify a substantial improvement in the later metrics.
Classical storage and computation remain independent resource coordinates, with
no conversion into a quantum-resource score. Measurement counts are also
reported separately. The execution event model charges gates and quantum queries
unit quantum duration; measurement, classical operations and fresh zero
preparation have zero duration, while preparation and reset gates are charged.
-/

namespace QuantumAlg

namespace AlgorithmGate

/-- The default algorithm model's three independent native gate counts. -/
public inductive Coordinate where
  | toffoli
  | cnot
  | singleQubit
deriving DecidableEq

/-- Gate instances retain the full one-qubit operator parameter. -/
public inductive Token where
  | toffoli
  | cnot
  | singleQubit (operator : UnitaryOperator (Qubits 1))

/-- Each default-model token has its fixed physical arity. -/
@[expose, implicit_reducible]
public def signature : Token → QuantumSignature
  | .toffoli => .qubits 3
  | .cnot => .qubits 2
  | .singleQubit _ => .qubits 1

/-- Resource coordinates classify tokens without replacing their semantics. -/
@[expose]
public def coordinate : Token → Coordinate
  | .toffoli => .toffoli
  | .cnot => .cnot
  | .singleQubit _ => .singleQubit

noncomputable section

/-- Fixed canonical Toffoli, CNOT and parameterized one-qubit semantics. -/
@[expose]
public def operator : (token : Token) → UnitaryOperator (signature token).register
  | .toffoli =>
    UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 3).symm
      (QubitPrimitive.operator
        (.toffoli 0 1 2 (by decide) (by decide) (by decide) : QubitPrimitive 3))
  | .cnot => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm Gate.CNOTOp
  | .singleQubit op => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm op

/-- The default native model used for logical algorithm resource claims. -/
@[expose, implicit_reducible]
public def model : GateModel where
  Token := Token
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature := signature
  operator := operator
  coordinate := coordinate


end

end AlgorithmGate

end QuantumAlg
