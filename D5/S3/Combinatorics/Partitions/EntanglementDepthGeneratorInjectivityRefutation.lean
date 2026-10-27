/- GID: D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.claim; result=D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.result; claim=D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.claim
   digest: Noninteger power sums and entanglement dimensions are not injective on partitions. -/

import D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture
import D5.S3.Analytic.BesselProductOrderLogConvexity.Result
import D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation

/-! # Noninjectivity of the power sum and entanglement dimension on integer partitions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Partitions.EntanglementDepthGeneratorInjectivityRefutation

noncomputable def powerSum {n : ℕ} (q : ℝ) (ξ : Nat.Partition n) : ℝ :=
  (ξ.parts.map (fun x : ℕ => (x : ℝ) ^ q)).sum

noncomputable def entanglementDimension {n : ℕ} (d : ℝ) (ξ : Nat.Partition n) : ℝ :=
  (ξ.parts.map (fun x : ℕ => d ^ x)).sum

def claim : Prop :=
  (∀ n (q : ℝ), (∀ k : ℕ, (k : ℝ) ≠ q) →
    Function.Injective (powerSum (n := n) q)) ∨
  (∀ n (d : ℝ), ((2 : ℕ) : ℝ) ≤ d → (∀ k : ℕ, (k : ℝ) ≠ d) →
    Function.Injective (entanglementDimension (n := n) d))

private def power_left : Nat.Partition 12 :=
  Nat.Partition.ofSums 12 {9, 1, 1, 1} (by norm_num)

private def power_right : Nat.Partition 12 :=
  Nat.Partition.ofSums 12 {4, 4, 4} (by norm_num)

private def dimension_left : Nat.Partition 26 :=
  Nat.Partition.ofSums 26 (3 ::ₘ 3 ::ₘ Multiset.replicate 20 1) (by norm_num)

private def dimension_right : Nat.Partition 26 :=
  D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture.partition126 26 13 0 (by decide)

private theorem half_not_nat : ∀ k : ℕ, (k : ℝ) ≠ 1 / 2 := by
  intro k
  simpa using
    (D5.S3.Analytic.BesselProductOrderLogConvexity.Result.half_noninteger 0 (k : ℤ)).symm

private theorem five_halves_not_nat : ∀ k : ℕ, (k : ℝ) ≠ 5 / 2 := by
  intro k
  convert
    (D5.S3.Analytic.BesselProductOrderLogConvexity.Result.half_noninteger 2 (k : ℤ)).symm using 1
  norm_num

private theorem power_distinct : power_left ≠ power_right := by
  intro h
  have hm : 9 ∈ power_left.parts := by decide
  have hn : 9 ∉ power_right.parts := by decide
  exact hn (h ▸ hm)

private theorem dimension_distinct : dimension_left ≠ dimension_right := by
  intro h
  have hm : 3 ∈ dimension_left.parts := by decide
  have hn : 3 ∉ dimension_right.parts := by decide
  exact hn (h ▸ hm)

private theorem power_values :
    powerSum (1 / 2) power_left = 6 ∧ powerSum (1 / 2) power_right = 6 := by
  have h9 : (9 : ℝ) ^ (1 / 2 : ℝ) = 3 := by
    simpa only [show (3 : ℝ) ^ 2 = 9 by norm_num,
      abs_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_one] using
      D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.rpow_square_half 3 1
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_one] using
      D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.rpow_square_half 2 1
  change (({9, 1, 1, 1} : Multiset ℕ).map
      (fun x : ℕ => (x : ℝ) ^ (1 / 2 : ℝ))).sum = 6 ∧
    (({4, 4, 4} : Multiset ℕ).map
      (fun x : ℕ => (x : ℝ) ^ (1 / 2 : ℝ))).sum = 6
  constructor <;> norm_num [h9, h4]

private theorem dimension_values :
    entanglementDimension (5 / 2) dimension_left = 325 / 4 ∧
    entanglementDimension (5 / 2) dimension_right = 325 / 4 := by
  change ((3 ::ₘ 3 ::ₘ Multiset.replicate 20 (1 : ℕ)).map
      (fun x : ℕ => (5 / 2 : ℝ) ^ x)).sum = 325 / 4 ∧
    ((Multiset.replicate 13 (2 : ℕ)).map
      (fun x : ℕ => (5 / 2 : ℝ) ^ x)).sum = 325 / 4
  constructor <;> norm_num

theorem result : ¬ claim := by
  rintro (h | h)
  · exact power_distinct (h 12 (1 / 2) half_not_nat
      (power_values.1.trans power_values.2.symm))
  · exact dimension_distinct (h 26 (5 / 2) (by norm_num) five_halves_not_nat
      (dimension_values.1.trans dimension_values.2.symm))

end D5.S3.Combinatorics.Partitions.EntanglementDepthGeneratorInjectivityRefutation
