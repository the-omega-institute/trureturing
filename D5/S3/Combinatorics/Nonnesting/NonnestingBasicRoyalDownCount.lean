/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalDownCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalDownCount
   mirror-E: none(waiver:royal-downstep-weight-recurrence)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DyckWord]
   utility: none
   digest: Splits the weighted Dyck count at its first return to ground level. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalDownRuns
import Mathlib.Combinatorics.Enumerative.DyckWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalDownCount

open NonnestingBasicRoyalDownRuns

noncomputable def downWeight (n : ℕ) : ℕ :=
  ∑ p : {p : DyckWord // p.semilength = n}, 2 ^ downPairs p.1.toList
end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalDownCount
