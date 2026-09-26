/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData56A
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData56A
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Data.Fin.Basic]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskCheck
   digest: Kernel-checked bounded-gap roots for this branch range. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData5
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root_1 : maskCheck 5 4 1 [1] = true := by decide
private theorem root_2 : maskCheck 5 4 2 [2] = true := by decide
private theorem root_3 : maskCheck 5 4 3 [3] = true := by decide
private theorem root_4 : maskCheck 5 4 4 [4] = true := by decide
private theorem root_5 : maskCheck 5 4 5 [5] = true := by decide
private theorem root_6 : maskCheck 5 4 6 [6] = true := by decide
private theorem root_7 : maskCheck 5 4 7 [7] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData5


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M1
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 6 5 1 [1] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M1


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M2
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 6 5 2 [2] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M2


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M3
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 6 5 3 [3] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M3


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M4
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 6 5 4 [4] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M4


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M5
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private theorem root : maskCheck 6 5 5 [5] = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData6M5


namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData56A
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
theorem roots5 (q : Nat) (hlo : 1 ≤ q) (hhi : q ≤ 7) :
    maskCheck 5 4 q [q] = true := by
  interval_cases q <;> simp only [
      ZeroForcingThreeGapData5.root_1,
      ZeroForcingThreeGapData5.root_2,
      ZeroForcingThreeGapData5.root_3,
      ZeroForcingThreeGapData5.root_4,
      ZeroForcingThreeGapData5.root_5,
      ZeroForcingThreeGapData5.root_6,
      ZeroForcingThreeGapData5.root_7]
theorem roots6 (q : Nat) (hlo : 1 ≤ q) (hhi : q ≤ 5) :
    maskCheck 6 5 q [q] = true := by
  interval_cases q <;> simp only [
      ZeroForcingThreeGapData6M1.root,
      ZeroForcingThreeGapData6M2.root,
      ZeroForcingThreeGapData6M3.root,
      ZeroForcingThreeGapData6M4.root,
      ZeroForcingThreeGapData6M5.root]
end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData56A
