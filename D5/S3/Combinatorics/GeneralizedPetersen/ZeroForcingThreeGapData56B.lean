/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData56B
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData56B
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Data.Fin.Basic]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskCheck
   digest: Kernel-checked bounded-gap roots for this branch range. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6C1
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 6 4 6 [6, 1] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6C1


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6C2
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 6 4 6 [6, 2] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6C2


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6C3
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 6 4 6 [6, 3] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6C3


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6C4
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 6 4 6 [6, 4] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6C4


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6C5
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 6 4 6 [6, 5] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6C5


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6C6
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 6 4 6 [6, 6] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6C6


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 6 5 6 [6] = true := by
  unfold maskCheck
  split_ifs
  · rfl
  · simp only [List.range_succ, List.range_zero, List.all_cons,
      List.all_nil, Bool.and_true, Bool.true_and]
    simp [
      ZeroForcingThreeGapData6M6C1.subtree,
      ZeroForcingThreeGapData6M6C2.subtree,
      ZeroForcingThreeGapData6M6C3.subtree,
      ZeroForcingThreeGapData6M6C4.subtree,
      ZeroForcingThreeGapData6M6C5.subtree,
      ZeroForcingThreeGapData6M6C6.subtree
    ]

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M6


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M7
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 6 5 7 [7] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M7


namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData56B
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
theorem roots6 (q : Nat) (hlo : 6 ≤ q) (hhi : q ≤ 7) :
    maskCheck 6 5 q [q] = true := by
  interval_cases q <;> simp only [
      ZeroForcingThreeGapData6M6.root,
      ZeroForcingThreeGapData6M7.root]
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData56B
