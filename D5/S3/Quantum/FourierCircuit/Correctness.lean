/- GID: D5/S3/Quantum/FourierCircuit/Correctness
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Correctness
   mirror-E: none(waiver:source-transfer-proof)
   anchors: []
   utility: none
   digest: Original actual QFT circuit acts as the independent analytic transform. -/

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Apache-2.0; full license: Library/Fourier/qudeleap2026qft.md.
Original assembly: QuantumAlg/Primitives/QFT/Source/FourierMatrix.lean,
QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Modified to consume the receiver's independent analytic QFT on every vector.
-/


import D5.S3.Quantum.FourierCircuit.Entries
import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Mathematics
import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Matrix
import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import D5.S3.Quantum.ShorCountingMarginal

/-! The original full-word interpreter equals the existing analytic transform. -/

namespace QuantumAlg.QuantumFourierTransform.Source
noncomputable section

/-- The literal recursive native word, with its actual terminal parallel SWAP
network, equals the receiver's positive normalized QFT on every input vector.
No equality modulo global phase is taken. Width zero is included. -/
theorem circuit_action (oracles : OracleModel) (q : Nat)
    (environment : oracles.Interpretation) (v : Fin (2 ^ q) → ℂ) :
    Matrix.mulVec (onBinaryLabels (circuit oracles q) environment) v =
      QuantumPhaseEstimationGeneral.QFT (2 ^ q) v := by
  have scale : invSqrtN q = QuantumPhaseEstimationGeneral.scale (2 ^ q) := by
    simp only [invSqrtN, QuantumPhaseEstimationGeneral.scale, Nat.cast_pow, Nat.cast_ofNat]
  have phase (output input : Fin (2 ^ q)) :
      ω q ^ (output.val * input.val) =
        QuantumPhaseEstimationGeneral.kernel (2 ^ q) output input := by
    rw [ω, ← Complex.exp_nat_mul]
    unfold QuantumPhaseEstimationGeneral.kernel QuantumPhaseEstimationGeneral.phase
    congr 1
    push_cast
    ring
  funext output
  change (∑ input, onBinaryLabels (circuit oracles q) environment output input * v input) = _
  unfold QuantumPhaseEstimationGeneral.QFT
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [circuit_entry, scale, phase]
  ring

end
end QuantumAlg.QuantumFourierTransform.Source
