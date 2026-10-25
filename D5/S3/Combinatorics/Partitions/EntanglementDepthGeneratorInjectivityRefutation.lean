/- GID: D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.claim; result=D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.result; claim=D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.claim
   digest: Noninteger power sums and entanglement dimensions each identify distinct integer partitions. -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormCast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Partitions.EntanglementDepthGeneratorInjectivityRefutation

noncomputable def powerSum {n : ℕ} (q : ℝ) (ξ : Nat.Partition n) : ℝ :=
  (ξ.parts.map (fun x => (x : ℝ) ^ q)).sum

noncomputable def entanglementDimension {n : ℕ} (d : ℝ) (ξ : Nat.Partition n) : ℝ :=
  (ξ.parts.map (fun x => d ^ x)).sum

def claim : Prop :=
  (∀ n (q : ℝ), (∀ k : ℕ, (k : ℝ) ≠ q) →
    Function.Injective (powerSum (n := n) q)) ∨
  (∀ n (d : ℝ), 2 ≤ d → (∀ k : ℕ, (k : ℝ) ≠ d) →
    Function.Injective (entanglementDimension (n := n) d))

private def power_left : Nat.Partition 12 where
  parts := {9, 1, 1, 1}
  parts_pos := by simp
  parts_sum := by norm_num

private def power_right : Nat.Partition 12 where
  parts := {4, 4, 4}
  parts_pos := by simp
  parts_sum := by norm_num

private def dimension_left : Nat.Partition 26 where
  parts := 3 ::ₘ 3 ::ₘ Multiset.replicate 20 1
  parts_pos := by simp
  parts_sum := by norm_num

private def dimension_right : Nat.Partition 26 where
  parts := Multiset.replicate 13 2
  parts_pos := by simp
  parts_sum := by norm_num

private theorem half_not_nat : ∀ k : ℕ, (k : ℝ) ≠ 1 / 2 := by
  sorry

private theorem five_halves_not_nat : ∀ k : ℕ, (k : ℝ) ≠ 5 / 2 := by
  sorry

private theorem power_distinct : power_left ≠ power_right := by
  sorry

private theorem dimension_distinct : dimension_left ≠ dimension_right := by
  sorry

private theorem power_values :
    powerSum (1 / 2) power_left = 6 ∧ powerSum (1 / 2) power_right = 6 := by
  sorry

private theorem dimension_values :
    entanglementDimension (5 / 2) dimension_left = 325 / 4 ∧
    entanglementDimension (5 / 2) dimension_right = 325 / 4 := by
  sorry

theorem result : ¬ claim := by
  rintro (h | h)
  · exact power_distinct (h 12 (1 / 2) half_not_nat
      (power_values.1.trans power_values.2.symm))
  · exact dimension_distinct (h 26 (5 / 2) (by norm_num) five_halves_not_nat
      (dimension_values.1.trans dimension_values.2.symm))

end D5.S3.Combinatorics.Partitions.EntanglementDepthGeneratorInjectivityRefutation
