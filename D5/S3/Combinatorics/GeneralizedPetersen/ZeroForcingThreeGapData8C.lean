/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData8C
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData8C
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Data.Fin.Basic]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskCheck
   digest: Kernel-checked bounded-gap roots for this branch range. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C1
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 7 [7, 1] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C1


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C2
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 7 [7, 2] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C2


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C3
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 7 [7, 3] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C3


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C4
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 7 [7, 4] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C4


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C5
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 7 [7, 5] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C5


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C6
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 7 [7, 6] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C6


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C7
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 7 [7, 7] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7C7


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 8 7 7 [7] = true := by
  unfold maskCheck
  split_ifs
  · rfl
  · simp only [List.range_succ, List.range_zero, List.all_cons,
      List.all_nil, Bool.and_true, Bool.true_and]
    simp [
      ZeroForcingThreeGapData8M7C1.subtree,
      ZeroForcingThreeGapData8M7C2.subtree,
      ZeroForcingThreeGapData8M7C3.subtree,
      ZeroForcingThreeGapData8M7C4.subtree,
      ZeroForcingThreeGapData8M7C5.subtree,
      ZeroForcingThreeGapData8M7C6.subtree,
      ZeroForcingThreeGapData8M7C7.subtree
    ]

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M7


namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8C
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
theorem roots8_top (q : Nat) (hlo : 7 ≤ q) (hhi : q ≤ 7) :
    maskCheck 8 7 q [q] = true := by
  interval_cases q <;> simp only [
      ZeroForcingThreeGapData8M7.root]
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8C

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6C1
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 6 [6, 1] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6C1


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6C2
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 6 [6, 2] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6C2


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6C3
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 6 [6, 3] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6C3


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6C4
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 6 [6, 4] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6C4


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6C5
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 6 [6, 5] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6C5


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6C6
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 6 [6, 6] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6C6


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 8 7 6 [6] = true := by
  unfold maskCheck
  split_ifs
  · rfl
  · simp only [List.range_succ, List.range_zero, List.all_cons,
      List.all_nil, Bool.and_true, Bool.true_and]
    simp [ZeroForcingThreeGapData8M6C1.subtree,
      ZeroForcingThreeGapData8M6C2.subtree,
      ZeroForcingThreeGapData8M6C3.subtree,
      ZeroForcingThreeGapData8M6C4.subtree,
      ZeroForcingThreeGapData8M6C5.subtree,
      ZeroForcingThreeGapData8M6C6.subtree]

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M6


namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8C
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
theorem roots8 (q : Nat) (hlo : 6 ≤ q) (hhi : q ≤ 6) :
    maskCheck 8 7 q [q] = true := by
  interval_cases q <;> simp only [
      ZeroForcingThreeGapData8M6.root]
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8C
