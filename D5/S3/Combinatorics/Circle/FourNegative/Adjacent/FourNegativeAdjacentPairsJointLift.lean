/- GID: D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentPairsJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentPairsJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Every independent adjacent equal-pair gap family admits a physical joint order. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentNearJointLift
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentFarLeft
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentFarRight

/-! Independent paired gaps retain every physical occurrence in both centered moduli. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentPairsJointLift
open PeriodicShortening RunFirstEarTransport FourNegativeAdjacentNearJointLift
open private symbolic from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentFarLeft
open private far_right from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentFarRight

/-- All independent paired gaps have one physical old order and a literal fresh-ear insertion. -/
theorem actualSource_four_negative_adjacent_pairs_joint_lift (r s : ℕ)
    (hr : 2 ≤ r) (hs : 2 ≤ s) :
    ∃ sigma : List (Fin (2*r+2*s)), ∃ j : ℕ, j ≤ 2*r+2*s ∧
      OriginalOrder (2*r+2*s) (1+2^r+2^(2*r)+2^(2*r+s)) sigma ∧
      OriginalOrder (2*r+2*s+1) (2*(1+2^r+2^(2*r)+2^(2*r+s)))
        (earWord (2*r+2*s) sigma j) := by
  by_cases hnear : r ≤ s+1 ∧ s ≤ r+1
  · exact actualSource_four_negative_adjacent_near_joint_lift r s hr hs hnear
  · by_cases hleft : s+2 ≤ r
    · exact symbolic r s hs hleft
    · exact far_right r s hr (by omega)

#print axioms actualSource_four_negative_adjacent_pairs_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentPairsJointLift
