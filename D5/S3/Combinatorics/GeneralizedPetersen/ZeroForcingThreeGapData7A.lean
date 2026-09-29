/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData7A
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData7A
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Data.Fin.Basic]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskCheck
   digest: Kernel-checked bounded-gap roots for this branch range. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C1
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 7 [7, 1] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C1


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C2
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 7 [7, 2] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C2


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C3
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 7 [7, 3] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C3


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C4
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 7 [7, 4] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C4


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C5
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 7 [7, 5] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C5


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C6
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 7 [7, 6] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C6


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C7
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 7 [7, 7] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7C7


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 7 6 7 [7] = true := by
  unfold maskCheck
  split_ifs
  · rfl
  · simp only [List.range_succ, List.range_zero, List.all_cons,
      List.all_nil, Bool.and_true, Bool.true_and]
    simp [
      ZeroForcingThreeGapData7M7C1.subtree,
      ZeroForcingThreeGapData7M7C2.subtree,
      ZeroForcingThreeGapData7M7C3.subtree,
      ZeroForcingThreeGapData7M7C4.subtree,
      ZeroForcingThreeGapData7M7C5.subtree,
      ZeroForcingThreeGapData7M7C6.subtree,
      ZeroForcingThreeGapData7M7C7.subtree
    ]

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M7


namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7A
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
theorem roots7_top (q : Nat) (hlo : 7 ≤ q) (hhi : q ≤ 7) :
    maskCheck 7 6 q [q] = true := by
  interval_cases q <;> simp only [
      ZeroForcingThreeGapData7M7.root]
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7A

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M1
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 7 6 1 [1] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M1


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M2
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 7 6 2 [2] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M2


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M3C1
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 3 [3, 1] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M3C1


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M3C2
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 3 [3, 2] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M3C2


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M3C3
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 7 5 3 [3, 3] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M3C3


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M3
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 7 6 3 [3] = true := by
  unfold maskCheck
  split_ifs
  · rfl
  · simp only [List.range_succ, List.range_zero, List.all_cons,
      List.all_nil, Bool.and_true, Bool.true_and]
    simp [
      ZeroForcingThreeGapData7M3C1.subtree,
      ZeroForcingThreeGapData7M3C2.subtree,
      ZeroForcingThreeGapData7M3C3.subtree
    ]

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M3


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M4
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 7 6 4 [4] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7M4


namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7A
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
theorem roots7 (q : Nat) (hlo : 1 ≤ q) (hhi : q ≤ 4) :
    maskCheck 7 6 q [q] = true := by
  interval_cases q <;> simp only [
      ZeroForcingThreeGapData7M1.root,
      ZeroForcingThreeGapData7M2.root,
      ZeroForcingThreeGapData7M3.root,
      ZeroForcingThreeGapData7M4.root]
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7A
