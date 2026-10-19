/- GID: D5/S3/Combinatorics/Graph/KyFanGap/Upper
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/Upper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The universal square-root upper-bound statement for symmetric zero-one matrices. -/

import D5.S3.Combinatorics.Graph.KyFanGap.SignedVariational

/-! Universal upper-bound interfaces for the graph Ky Fan problem. -/

noncomputable section

namespace D5.S3.Combinatorics.Graph.KyFanGap

def upperBoundStatement : Prop :=
  ∀ (k n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm →
    (∀ i j, A i j = 0 ∨ A i j = 1) →
      kyFan k A ≤ (1 + Real.sqrt k) * n / 2

theorem kyFan_zero (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    kyFan 0 M = 0 := by
  simp [kyFan,
    D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.kyFanSum]

end D5.S3.Combinatorics.Graph.KyFanGap
