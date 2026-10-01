/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGround
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGround
   mirror-E: none(waiver:royal-ground-singleton-count)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DyckWord]
   utility: none
   digest: Counts singleton primitives after the first under Dyck concatenation. -/
import Mathlib.Combinatorics.Enumerative.DyckWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalGround

def groundSingletons (d : DyckWord) : ℕ :=
  if h : d = 0 then 0 else
    groundSingletons d.outsidePart +
      if d.outsidePart ≠ 0 ∧ d.outsidePart.insidePart = 0 then 1 else 0
termination_by d.semilength
decreasing_by exact d.semilength_outsidePart_lt h

end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalGround
