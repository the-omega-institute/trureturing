/- GID: D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentNearJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentNearJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: The three central paired-gap branches have a common physical old/new order. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentEqual
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentReverse

/-! The three central branches consumed by the independent paired-gap endpoint. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentNearJointLift
open PeriodicShortening RunFirstEarTransport
open FourNegativeAdjacentDoublePhysical
open private actualSource_four_negative_adjacent_equal_joint_lift
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentEqual
open private actualSource_four_negative_adjacent_reverse_joint_lift
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentReverse

/-- All three central dyadic branches admit a literal ear on the same physical order. -/
theorem actualSource_four_negative_adjacent_near_joint_lift (r s : ℕ)
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hnear : r ≤ s + 1 ∧ s ≤ r + 1) :
    ∃ sigma : List (Fin (2 * r + 2 * s)), ∃ j : ℕ, j ≤ 2 * r + 2 * s ∧
      OriginalOrder (2 * r + 2 * s) (1 + 2 ^ r + 2 ^ (2 * r) + 2 ^ (2 * r + s)) sigma ∧
      OriginalOrder (2 * r + 2 * s + 1) (2 * (1 + 2 ^ r + 2 ^ (2 * r) + 2 ^ (2 * r + s)))
        (earWord (2 * r + 2 * s) sigma j) := by
  by_cases he : r = s
  · obtain ⟨sigma,hold,hnew⟩ := actualSource_four_negative_adjacent_equal_joint_lift r s hs he
    exact ⟨sigma,0,by omega,hold,hnew⟩
  · by_cases hd : r = s + 1
    · obtain ⟨sigma,hj,hold,hnew⟩ := actualSource_four_negative_adjacent_double_joint_lift r s hs hd
      exact ⟨sigma,2 * s + r,hj,hold,hnew⟩
    · obtain ⟨sigma,hold,hnew⟩ := actualSource_four_negative_adjacent_reverse_joint_lift r s hr (by omega)
      exact ⟨sigma,0,by omega,hold,hnew⟩

end D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentNearJointLift
