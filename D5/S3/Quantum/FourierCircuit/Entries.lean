/- GID: D5/S3/Quantum/FourierCircuit/Entries
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Entries
   mirror-E: none(waiver:source-transfer-proof)
   anchors: []
   utility: none
   digest: Original full-word Fourier entries from no-swap and actual reversal. -/

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Apache-2.0; full license: Library/Fourier/qudeleap2026qft.md.
Original assembly: QuantumAlg/Primitives/QFT/Source/FourierMatrix.lean,
QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Modified to expose the original scalar-entry assembly to the receiver's analytic consumer.
-/


module

public import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.NoSwapMatrix
public import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Reverse.Matrix
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.NoSwapMatrix
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Reverse.Matrix
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Matrix
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Mathematics
import all D5.S3.Quantum.FourierCircuit.Util.FinPow.BitReverse
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary

namespace QuantumAlg.QuantumFourierTransform.Source
noncomputable section

public theorem circuit_entry (oracles : OracleModel) (q : Nat)
  (environment : oracles.Interpretation) (output input : Fin (2 ^ q)) :
    onBinaryLabels (circuit oracles q) environment output input =
      invSqrtN q * ω q ^ (output.val * input.val) := by
  rw [circuit, qftSource_binaryMatrix_seq (environment := environment),
    qftSource_reverse_binaryMatrix (environment := environment)]
  change Matrix.mulVec ((qftReverseBitsPerm q).permMatrix Complex)
    (fun row => onBinaryLabels (noSwap oracles q) environment row input) output = _
  rw [Matrix.permMatrix_mulVec]
  change onBinaryLabels (noSwap oracles q) environment (qftReverseBits q output) input = _
  rw [qftSource_noSwap_binaryMatrix_entry (environment := environment),
    qftReverseBits_involutive]

end
end QuantumAlg.QuantumFourierTransform.Source
