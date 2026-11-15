/- GID: D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix
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
Original file: QuantumAlg/Primitives/QFT/Source/Reverse/Matrix.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Matrix
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Matrix
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Primitive
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Mathematics.BitReverse
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Swap.Label
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Swap.Operator
import all D5.S3.Quantum.FourierCircuit.Util.FinPow.BitReverse
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Components.Kets

/-!
# The complete native bit-reversal operator

Each symmetric swap is one native source instruction in the actual disjoint
parallel word. Its complete operator agrees with the bit-reversal permutation
on every computational label.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

noncomputable section

private lemma swapStep_binaryMatrix (oracles : OracleModel) (n : Nat)
    (index : Fin (n / 2))
    (environment : oracles.Interpretation) :
    onBinaryLabels (swapStep oracles n index) environment =
      qftSwapOperator (qftSwapLeft n index) (qftSwapRight n index)
        (qftSwapLeft_ne_right n index) :=
  qftSource_primitive_binaryMatrix (environment := environment) oracles _

private lemma reversePrefix_binary_apply_ket (oracles : OracleModel) (n count : Nat)
    (bounded : count ≤ n / 2) (label : Fin (2 ^ n))
    (environment : oracles.Interpretation) :
    (onBinaryLabels (reversePrefix oracles n count bounded) environment).applyVec
        (NormalizedVector.ket (R := Qubits n) label : HilbertVector (Qubits n)) =
      (NormalizedVector.ket (R := Qubits n)
        (qftBitReverseLabelPrefix n count bounded label) : HilbertVector (Qubits n)) := by
  induction count with
  | zero =>
      have empty : onBinaryLabels (reversePrefix oracles n 0 bounded) environment = 1 := by
        rw [onBinaryLabels, reversePrefix_zero_matrix (environment := environment),
          UnitaryOperator.unitaryOperator_reindex_one]
      rw [empty, UnitaryOperator.one_applyVec]
      rfl
  | succ count ih =>
      have next : onBinaryLabels (reversePrefix oracles n (count + 1) bounded) environment =
          onBinaryLabels (swapStep oracles n ⟨count, Nat.lt_of_succ_le bounded⟩) environment *
            onBinaryLabels
              (reversePrefix oracles n count (Nat.le_of_succ_le bounded)) environment := by
        unfold onBinaryLabels
        rw [reversePrefix_succ_matrix (environment := environment),
          UnitaryOperator.unitaryOperator_reindex_mul]
      rw [next, UnitaryOperator.mul_applyVec, ih, swapStep_binaryMatrix (environment :=
        environment),
        qftSwapOperator_applyVec_ket]
      rfl

lemma qftSource_reverse_binary_apply_ket (oracles : OracleModel) (n : Nat)
    (label : Fin (2 ^ n))
    (environment : oracles.Interpretation) :
    (onBinaryLabels (bitReverse oracles n) environment).applyVec
        (NormalizedVector.ket (R := Qubits n) label : HilbertVector (Qubits n)) =
      (NormalizedVector.ket (R := Qubits n) (qftReverseBits n label) :
        HilbertVector (Qubits n)) := by
  rw [bitReverse, reversePrefix_binary_apply_ket (environment := environment),
    qftBitReverseLabel_eq]

lemma qftSource_reverse_binaryMatrix (oracles : OracleModel) (n : Nat)
    (environment : oracles.Interpretation) :
    onBinaryLabels (bitReverse oracles n) environment =
      UnitaryOperator.ofPerm (qftReverseBitsPerm n) := by
  apply Subtype.ext
  ext output input
  have actual := congrArg (fun state : HilbertVector (Qubits n) => state output)
    (qftSource_reverse_binary_apply_ket (environment := environment) oracles n input)
  have target := congrArg (fun state : HilbertVector (Qubits n) => state output)
    (UnitaryOperator.ofPerm_applyVec_ket (qftReverseBitsPerm n) input)
  have inverse : (qftReverseBitsPerm n)⁻¹ input = qftReverseBits n input := rfl
  rw [inverse] at target
  have applyKet (A : HilbertOperator (Qubits n)) :
      HilbertOperator.applyVec A (NormalizedVector.ket input : HilbertVector (Qubits n)) output =
        A output input := by
    change (∑ j, A output j * NormalizedVector.ket input j) = _
    simp only [NormalizedVector.ket_apply, mul_ite, mul_one, mul_zero]
    exact Fintype.sum_ite_eq' input (fun j => A output j)
  simpa only [UnitaryOperator.applyVec, applyKet] using actual.trans target.symm

end

end QuantumAlg.QuantumFourierTransform.Source
