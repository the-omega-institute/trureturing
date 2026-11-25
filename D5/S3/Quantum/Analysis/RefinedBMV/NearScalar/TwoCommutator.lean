/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/TwoCommutator
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proof component of the four-copy refined BMV comparison near a scalar. -/

import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.PowerReorder
import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Clustered
import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Reordering

open Matrix
open scoped Matrix Matrix.Norms.Frobenius

namespace D5.S3.Quantum.Analysis.RefinedBMVNearScalarTwoCommutator

open RefinedBMV (evalWord)
open RefinedBMV.Algebra44 (realTrace)
open RefinedBMV.NearScalarReordering (abs_realTrace_sub_sorted_le)
open D5.S3.Quantum.Analysis.RefinedBMVNearScalarPowerReorder
  (alternating_two_commutator_power_word_bound)
open D5.S3.Quantum.Analysis.RefinedBMVNearScalarClustered
  (clustered_two_commutator_power_word_bound two_boolean_segments_trace_patterns)

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "opNorm" =>
  fun A : Matrix n n ℂ => ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A‖

private theorem power_word_coefficient_le (x y T : ℕ) (hx : x ≤ T) (hy : y ≤ T) :
    1 + 2 * (y : ℝ) + (x : ℝ) * (2 + 4 * (y : ℝ)) ≤
      1 + 2 * (T : ℝ) * (2 + 4 * (T : ℝ)) := by
  have hx' : (x : ℝ) ≤ (T : ℝ) := Nat.cast_le.mpr hx
  have hy' : (y : ℝ) ≤ (T : ℝ) := Nat.cast_le.mpr hy
  have hprod : (x : ℝ) * (2 + 4 * (y : ℝ)) ≤ (T : ℝ) * (2 + 4 * (T : ℝ)) :=
    mul_le_mul hx' (by linarith only [hy']) (by positivity) (by positivity)
  calc
    _ ≤ 1 + 2 * (T : ℝ) + (T : ℝ) * (2 + 4 * (T : ℝ)) :=
      add_le_add (by linarith only [hy']) hprod
    _ ≤ _ := by nlinarith only [sq_nonneg (T : ℝ)]

/-- One false in each segment gives an alternating trace. For counts zero and
two, the classifier starts at the commutator preceding the all-true segment. -/
theorem abs_realTrace_two_commutator_le (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.IsHermitian) (u v : List Bool) (T : ℕ)
    (hT : (u ++ v).count true = T) (hfalse : (u ++ v).count false = 2) :
    |realTrace ((H * B - B * H) * evalWord H B u *
        (H * B - B * H) * evalWord H B v)| ≤
      (1 + 2 * (T : ℝ) * (2 + 4 * (T : ℝ))) * opNorm H ^ T *
        ‖B * (H * B - B * H)‖ ^ 2 := by
  let C := H * B - B * H
  change |(C * evalWord H B u * C * evalWord H B v).trace.re| ≤
    (1 + 2 * (T : ℝ) * (2 + 4 * (T : ℝ))) * opNorm H ^ T * ‖B * C‖ ^ 2
  obtain ⟨a, b, c, d, hsum, hpattern⟩ := two_boolean_segments_trace_patterns H B C u v hfalse
  have htotal : a + b + c + d = T := hsum.trans hT
  have hscaled (x y : ℕ) (hx : x ≤ T) (hy : y ≤ T) :
      (1 + 2 * (y : ℝ) + (x : ℝ) * (2 + 4 * (y : ℝ))) * opNorm H ^ T * ‖B * C‖ ^ 2 ≤
        (1 + 2 * (T : ℝ) * (2 + 4 * (T : ℝ))) * opNorm H ^ T * ‖B * C‖ ^ 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (power_word_coefficient_le x y T hx hy) (by positivity))
      (by positivity)
  rcases hpattern with halt | hcluster
  · rw [halt]
    refine (alternating_two_commutator_power_word_bound H B hH hB a b c d).trans ?_
    simpa only [htotal] using hscaled a c (by omega) (by omega)
  · rw [hcluster]
    refine (clustered_two_commutator_power_word_bound H B hH hB a b c d).trans ?_
    simpa only [htotal] using hscaled b d (by omega) (by omega)

/-- The deviation from the sorted real trace for a word with m copies of H
and four copies of B. -/
theorem abs_realTrace_sub_sorted_le_nearScalar (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.IsHermitian) (w : List Bool) (m : ℕ)
    (hm : w.count true = m) (hfour : w.count false = 4) :
    |realTrace (evalWord H B w) - realTrace (H ^ m * B ^ 4)| ≤
      96 * (m : ℝ) ^ 4 * opNorm H ^ (m - 2) * ‖B * (H * B - B * H)‖ ^ 2 := by
  let t : ℝ := ((m - 2 : ℕ) : ℝ)
  let A : ℝ := 1 + 2 * t * (2 + 4 * t)
  let S : ℝ := opNorm H ^ (m - 2) * ‖B * (H * B - B * H)‖ ^ 2
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hsort := abs_realTrace_sub_sorted_le H B hH hB w m hm hfour
    (A * S) (mul_nonneg hA hS) (by
      intro u v hu hv
      simpa only [A, t, S, mul_assoc] using
        abs_realTrace_two_commutator_le H B hH hB u v (m - 2) hu hv)
  have hcoeff : 12 * (m : ℝ) * ((m - 1 : ℕ) : ℝ) * A ≤ 96 * (m : ℝ) ^ 4 := by
    by_cases hm0 : m = 0
    · simp [hm0]
    have htNat : m - 2 + 1 ≤ m := by omega
    have htCast : ((m - 2 + 1 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr htNat
    have htm : t + 1 ≤ (m : ℝ) := by
      simpa only [t, Nat.cast_add, Nat.cast_one] using htCast
    have hAsq : A ≤ 8 * (m : ℝ) ^ 2 := by
      calc
        A ≤ 8 * (t + 1) ^ 2 := by
          dsimp only [A]
          nlinarith only [ht]
        _ ≤ 8 * (m : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left
            ((sq_le_sq₀ (by positivity) (by positivity)).mpr htm) (by norm_num)
    have hprev : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (Nat.sub_le m 1)
    calc
      _ ≤ 12 * (m : ℝ) * (m : ℝ) * (8 * (m : ℝ) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hprev (by positivity)) hAsq hA (by positivity)
      _ = _ := by ring
  exact hsort.trans (by
    simpa only [S, mul_assoc] using mul_le_mul_of_nonneg_right hcoeff hS)

end D5.S3.Quantum.Analysis.RefinedBMVNearScalarTwoCommutator
