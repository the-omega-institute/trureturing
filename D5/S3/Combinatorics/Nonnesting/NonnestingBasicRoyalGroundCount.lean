/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGroundCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGroundCount
   mirror-E: none(waiver:royal-ground-weight-count)
   anchors: []
   utility: none
   digest: Splits the combined downstep and ground-singleton weight at first return. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalGround
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalDownCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalGroundCount

open NonnestingBasicRoyalGround NonnestingBasicRoyalDownRuns NonnestingBasicRoyalDownCount

noncomputable def groundWeight (n : ℕ) : ℕ :=
  ∑ d : {d : DyckWord // d.semilength = n},
    2 ^ (downPairs d.1.toList + groundSingletons d.1)
end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalGroundCount
