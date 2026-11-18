/- GID: D5/S3/Quantum/FourierCircuit/Components/Gates/Operator
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/Gates/Operator
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
Original file: QuantumAlg/Components/Gates/Operator.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
public import D5.S3.Quantum.FourierCircuit.Components.Kets
import all D5.S3.Quantum.FourierCircuit.Components.Kets
import all D5.S3.Quantum.FourierCircuit.Components.QubitPrimitive.Operator
import all D5.S3.Quantum.FourierCircuit.Util.Complex

/-!
# Named elementary qubit operators

Pauli, Hadamard, CNOT, S and T operators and their exact algebra are mathematical
objects. Native gate models and circuit constructors reuse these same operators
without making the operator layer depend on a chosen execution language.
-/

section

namespace QuantumAlg.Gate

open NormalizedVector

noncomputable section

/-- Metadata-free Hadamard operator `H = (1/sqrt 2) [[1, 1], [1, -1]]`. -/
@[expose] public def HOp : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (invSqrt2 • !![(1 : ℂ), 1; 1, -1] : HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff, star_smul, smul_mul_smul_comm,
        star_invSqrt2, invSqrt2_mul_self]
      have hstar : star (!![(1 : ℂ), 1; 1, -1] : HilbertOperator (Qubits 1))
          = !![(1 : ℂ), 1; 1, -1] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]
      have hmul :
          (!![(1 : ℂ), 1; 1, -1] : HilbertOperator (Qubits 1))
            * !![(1 : ℂ), 1; 1, -1] = (2 : ℂ) • 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> norm_num
      rw [hstar, hmul, smul_smul]
      norm_num)


/-- Metadata-free controlled-NOT operator, control = qubit 0. -/
@[expose] public def CNOTOp : UnitaryOperator (Qubits 2) :=
  UnitaryOperator.ofPerm (Equiv.swap 2 3)


/-! ### Clifford+T generator algebra -/


end

end QuantumAlg.Gate

end
