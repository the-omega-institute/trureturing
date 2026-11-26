/- GID: D5/S3/Combinatorics/MonotoneIntervalReconstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MonotoneIntervalReconstruction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [lake/module/OmegaMath.Combinatorics.MonotoneIntervalReconstruction]
   utility: none
   digest: Full unlabelled interval sums reconstruct nonnegative nondecreasing real lists. -/

import OmegaMath.Combinatorics.MonotoneIntervalReconstruction

/-! Book citation of the real, weakly monotone interval reconstruction theorem. -/

namespace D5.S3.Combinatorics.MonotoneIntervalReconstruction

/-- Every interval contributes once, including coincident sums, with both endpoints included. -/
theorem result (A B : List ℝ)
    (hA : 3 ≤ A.length) (hB : 3 ≤ B.length)
    (ha : ∀ x ∈ A, 0 ≤ x) (hb : ∀ x ∈ B, 0 ≤ x)
    (hsA : A.Pairwise (· ≤ ·)) (hsB : B.Pairwise (· ≤ ·))
    (he : Omega.MonotoneIntervalReconstruction.listObservations A =
      Omega.MonotoneIntervalReconstruction.listObservations B) : A = B :=
  Omega.MonotoneIntervalReconstruction.list_reconstruct A B hA hB ha hb hsA hsB he

end D5.S3.Combinatorics.MonotoneIntervalReconstruction
