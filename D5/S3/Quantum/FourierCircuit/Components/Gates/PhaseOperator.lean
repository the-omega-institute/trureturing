/- GID: D5/S3/Quantum/FourierCircuit/Components/Gates/PhaseOperator
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/Gates/PhaseOperator
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
Original file: QuantumAlg/Components/Gates/PhaseOperator.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Util.Complex

/-!
# Exact one-qubit phase operators

These two mathematical operators preserve the original phase on each basis
branch. They are independent of the execution model, native gate alphabet,
placement and circuit cost. Native realizations use these same operators.
-/

namespace QuantumAlg

noncomputable section

/-- Metadata-free phase operator `diag(1, e^{iθ})`. -/
public def phaseGateOp (θ : ℝ) : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![1, 0; 0, Complex.exp ((θ : ℝ) * Complex.I)] :
      HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply, conj_exp_I,
          exp_I_mul_exp_neg_I])
 Matrix.star_apply, conj_exp_I,
          exp_I_mul_exp_neg_I])

/-- The original one-branch phase operator is diagonal with its exact complex phase. -/
public lemma phaseGateOp_diagonal (angle : Real) :
    (phaseGateOp angle : HilbertOperator (Qubits 1)) =
      Matrix.diagonal (fun bit => if bit = 0 then 1 else
        Complex.exp ((angle : Complex) * Complex.I)) := by
  ext row column
  fin_cases row <;> fin_cases column <;> rfl
es column <;> rfl

end

end QuantumAlg
