/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalDownRuns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalDownRuns
   mirror-E: none(waiver:royal-weighted-dyck-count)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DyckWord]
   utility: none
   digest: Counts consecutive downsteps under Dyck concatenation and nesting. -/
import Mathlib.Combinatorics.Enumerative.DyckWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalDownRuns

open DyckStep

def downPairs : List DyckStep → ℕ
  | a :: b :: s => (if a = D ∧ b = D then 1 else 0) + downPairs (b :: s)
  | _ => 0
end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalDownRuns
