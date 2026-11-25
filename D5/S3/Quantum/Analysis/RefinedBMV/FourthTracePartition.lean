/- GID: D5/S3/Quantum/Analysis/RefinedBMV/FourthTracePartition
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/FourthTracePartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth trace contraction for a Hermitian matrix partition. -/

import D5.S3.Quantum.Analysis.RefinedBMV67

/-! # Fourth trace contraction for finite Hermitian partitions -/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace RefinedBMV

open private fourth_trace_le_gram_square from D5.S3.Quantum.Analysis.RefinedBMV67
open private re_trace_sq_le_gram44 from D5.S3.Quantum.Analysis.RefinedBMV44
open private trace_cycle_power from D5.S3.Quantum.Analysis.RefinedBMVTracePower

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- The fourth trace of a product of Hermitian factors is bounded by the
trace of the product of their fourth powers. -/
theorem fourth_trace_mul_le (X Y : Mat) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (trace ((X * Y) ^ 4)).re ≤ (trace (Y ^ 4 * X ^ 4)).re := by
  have hLeft : trace (((X * Y) * (X * Y)ᴴ) ^ 2) = trace ((Y ^ 2 * X ^ 2) ^ 2) := by
    rw [conjTranspose_mul, hY.eq, hX.eq]
    have h₁ : X * Y * (Y * X) = X * (Y ^ 2 * X) := by noncomm_ring
    rw [h₁, trace_cycle_power X (Y ^ 2 * X) 2, mul_assoc, ← pow_two]
  have hRight : trace ((Y ^ 2 * X ^ 2)ᴴ * (Y ^ 2 * X ^ 2)) = trace (Y ^ 4 * X ^ 4) := by
    rw [conjTranspose_mul, conjTranspose_pow, conjTranspose_pow, hX.eq, hY.eq]
    have h₂ : X ^ 2 * Y ^ 2 * (Y ^ 2 * X ^ 2) = X ^ 2 * (Y ^ 4 * X ^ 2) := by noncomm_ring
    rw [h₂, trace_mul_comm (X ^ 2)]
    apply congrArg trace
    noncomm_ring
  have hFirst := fourth_trace_le_gram_square (X * Y)
  have hSecond := re_trace_sq_le_gram44 (Y ^ 2 * X ^ 2)
  rw [hLeft] at hFirst
  rw [hRight] at hSecond
  exact le_trans hFirst hSecond

/-- The trace of the fourth power dominates the sum after multiplication
by a finite family of Hermitian factors whose fourth powers sum to at most one. -/
theorem fourth_trace_partition {ι : Type*} (s : Finset ι) (Y : ι → Mat) (X : Mat)
    (hY : ∀ i ∈ s, (Y i).IsHermitian) (hX : X.IsHermitian)
    (hpartition : (1 - ∑ i ∈ s, Y i ^ 4).PosSemidef) :
    (∑ i ∈ s, (trace ((X * Y i) ^ 4)).re) ≤ (trace (X ^ 4)).re := by
  have hX4 : (X ^ 4).PosSemidef := by
    have hGram := posSemidef_conjTranspose_mul_self (X ^ 2)
    rw [conjTranspose_pow, hX.eq, ← pow_add] at hGram
    exact hGram
  have hR := RHLinalg.trace_mul_nonneg_of_posSemidef hpartition hX4
  change 0 ≤ (trace ((1 - ∑ i ∈ s, Y i ^ 4) * X ^ 4)).re at hR
  rw [sub_mul, one_mul, trace_sub, Complex.sub_re] at hR
  have hSum :
      (∑ i ∈ s, (trace ((X * Y i) ^ 4)).re) ≤ ∑ i ∈ s, (trace (Y i ^ 4 * X ^ 4)).re :=
    Finset.sum_le_sum fun i hi ↦ fourth_trace_mul_le X (Y i) hX (hY i hi)
  have hLinear : (trace ((∑ i ∈ s, Y i ^ 4) * X ^ 4)).re =
      ∑ i ∈ s, (trace (Y i ^ 4 * X ^ 4)).re := by
    rw [Finset.sum_mul, trace_sum, Complex.re_sum]
  rw [← hLinear] at hSum
  exact le_trans hSum (sub_nonneg.mp hR)

end RefinedBMV
