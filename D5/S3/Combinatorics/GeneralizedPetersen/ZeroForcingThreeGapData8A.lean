/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData8A
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData8A
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Data.Fin.Basic]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskCheck
   digest: Kernel-checked bounded-gap roots for this branch range. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M1
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 8 7 1 [1] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M1


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M2
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 8 7 2 [2] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M2


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M3C1
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 3 [3, 1] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M3C1


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M3C2
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 3 [3, 2] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M3C2


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M3C3
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem subtree : maskCheck 8 6 3 [3, 3] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M3C3


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M3
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 8 7 3 [3] = true := by
  unfold maskCheck
  split_ifs
  · rfl
  · simp only [List.range_succ, List.range_zero, List.all_cons,
      List.all_nil, Bool.and_true, Bool.true_and]
    simp [
      ZeroForcingThreeGapData8M3C1.subtree,
      ZeroForcingThreeGapData8M3C2.subtree,
      ZeroForcingThreeGapData8M3C3.subtree
    ]

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M3


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M4
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 8 7 4 [4] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8M4


namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8A
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
theorem roots8 (q : Nat) (hlo : 1 ≤ q) (hhi : q ≤ 4) :
    maskCheck 8 7 q [q] = true := by
  interval_cases q <;> simp only [
      ZeroForcingThreeGapData8M1.root,
      ZeroForcingThreeGapData8M2.root,
      ZeroForcingThreeGapData8M3.root,
      ZeroForcingThreeGapData8M4.root]
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8A
