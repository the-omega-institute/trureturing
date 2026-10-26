/- GID: D5/S3/Combinatorics/RealRootedPermutations/Result
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RealRootedPermutations/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exactly the unimodal permutations weakly sort coefficients of positive real-rooted products. -/

import D5.S3.Combinatorics.RealRootedPermutations.LogConcave
import D5.S3.Combinatorics.RealRootedPermutations.Realization

namespace D5.S3.Combinatorics.RealRootedPermutations.Result

/-- Every unimodal permutation arises, and every arising permutation is unimodal. -/
theorem result : claim := by
  intro n π
  constructor
  · exact LogConcave.unimodal_of_arises π
  · intro hπ
    obtain ⟨r, hr, hs⟩ := Realization.realize_strict π hπ
    exact ⟨r, hr, hs.monotone⟩

end D5.S3.Combinatorics.RealRootedPermutations.Result
