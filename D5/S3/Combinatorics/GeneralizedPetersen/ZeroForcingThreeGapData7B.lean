/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData7B
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData7B
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Data.Fin.Basic]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskCheck
   digest: Kernel-checked bounded-gap roots for this branch range. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M5C1
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 5 [5, 1] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M5C1


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M5C2
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 5 [5, 2] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M5C2


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M5C3
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 5 [5, 3] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M5C3


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M5C4
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 5 [5, 4] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M5C4


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M5C5
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 5 [5, 5] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M5C5


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M5
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 7 6 5 [5] = true := by
  unfold maskCheck
  split_ifs
  · rfl
  · simp only [List.range_succ, List.range_zero, List.all_cons,
      List.all_nil, Bool.and_true, Bool.true_and]
    simp [
      ZeroForcingThreeGapData7M5C1.subtree,
      ZeroForcingThreeGapData7M5C2.subtree,
      ZeroForcingThreeGapData7M5C3.subtree,
      ZeroForcingThreeGapData7M5C4.subtree,
      ZeroForcingThreeGapData7M5C5.subtree
    ]

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M5


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6C1
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 6 [6, 1] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6C1


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6C2
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 6 [6, 2] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6C2


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6C3
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 6 [6, 3] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6C3


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6C4
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 6 [6, 4] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6C4


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6C5
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 6 [6, 5] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6C5


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6C6
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 6 [6, 6] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6C6


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 7 6 6 [6] = true := by
  unfold maskCheck
  split_ifs
  · rfl
  · simp only [List.range_succ, List.range_zero, List.all_cons,
      List.all_nil, Bool.and_true, Bool.true_and]
    simp [
      ZeroForcingThreeGapData7M6C1.subtree,
      ZeroForcingThreeGapData7M6C2.subtree,
      ZeroForcingThreeGapData7M6C3.subtree,
      ZeroForcingThreeGapData7M6C4.subtree,
      ZeroForcingThreeGapData7M6C5.subtree,
      ZeroForcingThreeGapData7M6C6.subtree
    ]

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M6


namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7B
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
theorem roots7 (q : Nat) (hlo : 5 ≤ q) (hhi : q ≤ 6) :
    maskCheck 7 6 q [q] = true := by
  interval_cases q <;> simp only [
      ZeroForcingThreeGapData7M5.root,
      ZeroForcingThreeGapData7M6.root]
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7B
