/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalAugCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalAugCount
   mirror-E: none(waiver:royal-augmented-dyck-count)
   anchors: []
   utility: none
   digest: Removes an initial singleton primitive from the augmented Royal weight. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalGroundCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalAugCount

open NonnestingBasicRoyalGround NonnestingBasicRoyalGroundCount NonnestingBasicRoyalDownRuns

noncomputable def augmentedWeight (n : ℕ) : ℕ :=
  ∑ d : {d : DyckWord // d.semilength = n},
    2 ^ (downPairs d.1.toList + groundSingletons d.1) *
      (if d.1 ≠ 0 ∧ d.1.insidePart = 0 then 2 else 1)
end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalAugCount
