/- GID: D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/SignedVariational
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed orthonormal pairings are bounded by the Ky Fan singular-value sum. -/

import D5.S3.Combinatorics.Graph.KyFanGap.Defs

/-! Signed variational interfaces for Ky Fan sums. -/

noncomputable section

open scoped BigOperators InnerProductSpace

namespace D5.S3.Combinatorics.Graph.KyFanGap

open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality

structure SignedWitness (k n : ℕ) where
  vectors : Fin k → EuclideanSpace ℝ (Fin n)
  orthonormal_vectors : Orthonormal ℝ vectors
  signs : Fin k → ℝ
  signs_sq : ∀ i, signs i ^ 2 = 1

def signedPairing {k n : ℕ} (W : SignedWitness k n)
    (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, W.signs i * (⟪W.vectors i, Matrix.toEuclideanLin M (W.vectors i)⟫_ℝ)

def signedInvolution (k n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Q.IsSymm ∧ Q * Q * Q = Q ∧
    Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin Q)) = k

theorem signed_pairing_le_kyFan_of_one {k n : ℕ} (hk : k ≤ n)
    (W : SignedWitness k n) (hsign : ∀ i, W.signs i = 1)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    signedPairing W M ≤ kyFan k M := by
  have h := re_sum_inner_map_le_ky_fan_sum
    (A := Matrix.toEuclideanLin M) (k := k) (by simpa using hk)
      W.orthonormal_vectors W.orthonormal_vectors
  simp only [signedPairing, hsign, one_mul]
  simpa [kyFan] using h

def lemmaAStatement : Prop :=
  ∀ {k n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ), M.IsSymm →
    (∀ Q, signedInvolution k n Q → Matrix.trace (Q * M) ≤ kyFan k M) ∧
      ∃ Q, signedInvolution k n Q ∧ Matrix.trace (Q * M) = kyFan k M

end D5.S3.Combinatorics.Graph.KyFanGap
