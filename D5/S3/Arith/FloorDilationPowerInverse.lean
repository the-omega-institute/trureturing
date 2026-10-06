/- GID: D5/S3/Arith/FloorDilationPowerInverse
   generality: G
   mirror-B: D5/B/S3/Arith/FloorDilationPowerInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: Quantitative floor dilation inversion on all nonnegative power scales. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.Arith.FloorDilationPowerInverse

open scoped BigOperators

/-- A uniform bound on a floor dilation transform controls its input whenever
the absolute first coefficient strictly dominates every finite absolute tail.
The exponent may be zero, the first coefficient may be negative, and the value
of the input sequence at zero is irrelevant. -/
theorem floorSum_power_inverse
    (b f : ℕ → ℝ) (a C T : ℝ)
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (htail : ∀ N : ℕ, (∑ d ∈ Finset.Ioc 1 N, |b d|) ≤ T)
    (hgap : T < |b 1|)
    (htransform : ∀ N : ℕ, 0 < N →
      |∑ d ∈ Finset.Ioc 0 N, b d * f (N / d)| ≤ C * (N : ℝ) ^ a) :
    ∀ N : ℕ, 0 < N →
      |f N| ≤ (C / (|b 1| - T)) * (N : ℝ) ^ a := by
  have hT : 0 ≤ T := by simpa using htail 1
  have hden : 0 < |b 1| - T := sub_pos.mpr hgap
  have hhead : 0 < |b 1| := lt_of_le_of_lt hT hgap
  let K : ℝ := C / (|b 1| - T)
  have hK : 0 ≤ K := div_nonneg hC hden.le
  have hKden : K * (|b 1| - T) = C :=
    div_mul_cancel₀ C (ne_of_gt hden)
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN
    have hsplit :
        (∑ d ∈ Finset.Ioc 0 N, b d * f (N / d)) =
          b 1 * f N + ∑ d ∈ Finset.Ioc 1 N, b d * f (N / d) := by
      have h := Finset.sum_Ioc_consecutive
        (fun d => b d * f (N / d)) (by omega : 0 ≤ (1 : ℕ))
        (by omega : 1 ≤ N)
      simpa using h.symm
    have hpower : 0 ≤ (N : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg N) a
    have htailbound :
        |∑ d ∈ Finset.Ioc 1 N, b d * f (N / d)| ≤ K * (N : ℝ) ^ a * T := by
      calc
        _ ≤ ∑ d ∈ Finset.Ioc 1 N, |b d * f (N / d)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Finset.Ioc 1 N, |b d| * (K * (N : ℝ) ^ a) := by
          apply Finset.sum_le_sum
          intro d hd
          obtain ⟨hd1, hdN⟩ := Finset.mem_Ioc.mp hd
          have hd0 : 0 < d := by omega
          have hdiv0 : 0 < N / d := Nat.div_pos hdN hd0
          have hdivlt : N / d < N := Nat.div_lt_self hN hd1
          have hdivle : (N / d : ℕ) ≤ N := Nat.div_le_self N d
          have hp : ((N / d : ℕ) : ℝ) ^ a ≤ (N : ℝ) ^ a :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hdivle) ha
          have hf := (ih (N / d) hdivlt hdiv0).trans
            (mul_le_mul_of_nonneg_left hp hK)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hf (abs_nonneg _)
        _ = K * (N : ℝ) ^ a * ∑ d ∈ Finset.Ioc 1 N, |b d| := by
          rw [← Finset.sum_mul]
          ring
        _ ≤ K * (N : ℝ) ^ a * T :=
          mul_le_mul_of_nonneg_left (htail N) (mul_nonneg hK hpower)
    have hbound : |b 1| * |f N| ≤
        C * (N : ℝ) ^ a + K * (N : ℝ) ^ a * T := by
      calc
        _ = |b 1 * f N| := (abs_mul _ _).symm
        _ = |(∑ d ∈ Finset.Ioc 0 N, b d * f (N / d)) -
            ∑ d ∈ Finset.Ioc 1 N, b d * f (N / d)| := by rw [hsplit]; ring_nf
        _ ≤ |∑ d ∈ Finset.Ioc 0 N, b d * f (N / d)| +
            |∑ d ∈ Finset.Ioc 1 N, b d * f (N / d)| := abs_sub _ _
        _ ≤ C * (N : ℝ) ^ a + K * (N : ℝ) ^ a * T :=
          add_le_add (htransform N hN) htailbound
    have habsorb : C * (N : ℝ) ^ a + K * (N : ℝ) ^ a * T =
        |b 1| * (K * (N : ℝ) ^ a) := by
      rw [← hKden]
      ring
    rw [habsorb] at hbound
    exact (mul_le_mul_iff_right₀ hhead).mp hbound

end D5.S3.Arith.FloorDilationPowerInverse
