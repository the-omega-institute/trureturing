/- GID: D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Operator
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/Gates/Swap/Operator
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
Original file: QuantumAlg/Components/Gates/Swap/Operator.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Components.QubitPrimitive.Operator
import all D5.S3.Quantum.FourierCircuit.Components.QubitPrimitive.Operator
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary

/-!
# Original addressed SWAP operator

The target retains the original three addressed CNOT operators on the full
qubit register. Its semantics is independent of any executable native model
or resource coordinate.
-/

namespace QuantumAlg

noncomputable section

/-- A genuine addressed wire swap, decomposed semantically into the usual
three addressed CNOT permutations. -/
public def qftSwapOperator {n : Nat} (left right : Fin n) (hne : left ≠ right) :
    UnitaryOperator (Qubits n) :=
  Mul.mul
    (Mul.mul
      (QubitPrimitive.operator (.cnot left right hne))
      (QubitPrimitive.operator (.cnot right left hne.symm)))
    (QubitPrimitive.operator (.cnot left right hne))

end

end QuantumAlg
