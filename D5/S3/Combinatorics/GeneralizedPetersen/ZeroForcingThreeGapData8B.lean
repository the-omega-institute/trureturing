/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData8B
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData8B
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Data.Fin.Basic]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskCheck
   digest: Kernel-checked bounded-gap roots for this branch range. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M5
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 8 7 5 [5] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M5


namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8B
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
theorem roots8 (q : Nat) (hlo : 5 ≤ q) (hhi : q ≤ 5) :
    maskCheck 8 7 q [q] = true := by
  interval_cases q <;> simp only [
      ZeroForcingThreeGapData8M5.root]
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8B
