/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeSmallestBLargestAJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeSmallestBLargestAJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: One physical order and literal fresh ear throughout the strict b<c<a chamber. -/
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
import D5.S3.Combinatorics.Circle.ThreeNegativeSmallestBLargestAFar
import D5.S3.Combinatorics.Circle.ThreeNegativeSmallestBLargestAAdjacent

/-! One joint physical order for the entire strict chamber. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeSmallestBLargestAJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open private ThreeNegativeMinimumTwoJointLift.realize
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
open private far_certificate from D5.S3.Combinatorics.Circle.ThreeNegativeSmallestBLargestAFar
open private adjacent_certificate from D5.S3.Combinatorics.Circle.ThreeNegativeSmallestBLargestAAdjacent

/-- The entire strict chamber, preserving the physical labels in both moduli. -/
theorem actualSource_three_negative_smallest_b_largest_a_joint_lift (a b c : ℕ)
    (hb : 2 ≤ b) (hbc : b < c) (hca : c < a) :
    ∃ sigma : List (Fin (a + b + c)), ∃ j : ℕ, j ≤ a + b + c ∧
      OriginalOrder (a + b + c) (1 + 2 ^ a + 2 ^ (a + b)) sigma ∧
      OriginalOrder (a + b + c + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b))) (earWord (a + b + c) sigma j) := by
  by_cases hb2 : b=2
  · exact ThreeNegativeMinimumTwoJointLift.actualSource_three_negative_minimum_two_joint_lift
      a b c (by omega) hb (by omega) (by omega)
  have hb3 : 3 ≤ b := by omega
  by_cases hac : a=c + 1
  · obtain ⟨plan,cert⟩ := adjacent_certificate b (c - b) hb3 (by omega)
    have ht : (2:ℤ) ^ c=2 ^ b * 2 ^ (c - b) := by rw [← pow_add]; congr 1; omega
    have hr : (2:ℤ) ^ a=2 * (2 ^ b * 2 ^ (c - b)) := by rw [hac,pow_succ,ht]; ring
    apply ThreeNegativeMinimumTwoJointLift.realize a b c (by omega) hb (by omega) plan
    simpa only [hr,ht] using cert
  · let q : ℤ := 2 ^ (c - b - 1)
    let h : ℤ := 2 ^ (a - c - 2)
    have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
    have hh : 1 ≤ h := by dsimp [h]; exact_mod_cast Nat.one_le_two_pow
    have hs : 8 ≤ (2:ℤ) ^ b := by
      exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hb3)
    have hs2 : 2 * ((2:ℤ) ^ b / 2)=2 ^ b := by
      have he : (2:ℤ) ^ b=2 * 2 ^ (b - 1) := by
        calc
          (2:ℤ) ^ b = 2 ^ ((b - 1) + 1) := by congr 1; omega
          _ = _ := by rw [pow_succ]; ring
      rw [he]; omega
    have ht : (2:ℤ) ^ c=2 * 2 ^ b * q := by
      dsimp [q]
      calc
        (2:ℤ) ^ c = 2 ^ (b + (c - b - 1) + 1) := by congr 1; omega
        _ = _ := by rw [pow_succ,pow_add]; ring
    have hr : (2:ℤ) ^ a=4 * (2 * 2 ^ b * q) * h := by
      dsimp [h]
      rw [← ht]
      calc
        (2:ℤ) ^ a = 2 ^ (c + (a - c - 2) + 2) := by congr 1; omega
        _ = _ := by rw [pow_add,pow_add]; norm_num; ring
    have cert := far_certificate (2 ^ b) q h hs hq hh hs2
    apply ThreeNegativeMinimumTwoJointLift.realize a b c (by omega) hb (by omega) _
    simpa only [hr,ht] using cert

#print axioms actualSource_three_negative_smallest_b_largest_a_joint_lift

end D5.S3.Combinatorics.Circle.ThreeNegativeSmallestBLargestAJointLift
