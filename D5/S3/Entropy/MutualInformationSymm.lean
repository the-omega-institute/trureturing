/- GID: D5/S3/Entropy/MutualInformationSymm
   generality: G
   mirror-B: D5/B/S3/Entropy/MutualInformationSymm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove finite joint entropy and mutual information are invariant under coordinate swap. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep terms: `mutualInformation`, `mutual_information`,
     `mutualInfo`, `MutualInfo`, `mutual information`, `entropy.*swap`,
     `Equiv.prodComm`, `Fintype.sum_equiv`, `Finset.sum_comm`, and
     `Fintype.sum_prod_type`.
   * No finite mutual-information symmetry theorem was found. Mathlib does provide the
     reindexing tools above; `Fintype.sum_prod_type` and `Finset.sum_comm` directly reduce both
     claims to equality of their summands.
   * Every declaration in `D5/S3/Entropy` and `D5/S3/Divergence` was grepped, together with
     both equality orientations and the entropy-decomposition arrangement. No duplicate or
     rearranged equivalent of either theorem was found.
   * `mutual_information_eq_entropy_sub` requires pointwise nonnegativity. Since symmetry is
     pure finite-sum reindexing, the proof unfolds the definitions directly and avoids adding
     that unnecessary hypothesis.
-/

import D5.S3.Entropy.MaxEntropy
import D5.S3.Entropy.MutualInformation

namespace D5.S3.Entropy.MutualInformationSymm

open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation

/-- Shannon entropy is invariant under swapping the coordinates of a finite joint function. -/
theorem entropy_swap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) :
    shannonEntropy (fun r : κ × ι => p (r.2, r.1)) = shannonEntropy p := by
  classical
  simp only [shannonEntropy, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Mutual information is symmetric under swapping the coordinates of a finite joint function. -/
theorem mutual_information_symm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) :
    mutualInformation (fun r : κ × ι => p (r.2, r.1)) = mutualInformation p := by
  classical
  simp only [mutualInformation, D5.S3.Divergence.ClassicalDPI.klDivergence,
    D5.S3.Divergence.ChainRule.marginal, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [mul_comm]

end D5.S3.Entropy.MutualInformationSymm
