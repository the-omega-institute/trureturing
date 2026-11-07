/- GID: D5/S3/Arith/Robin/PriceRecord/CurvatureCorrectedArithmeticSurplus
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/CurvatureCorrectedArithmeticSurplus
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Actual full prime-power arithmetic surplus exceeds the log-log curvature loss. -/

import D5.S3.Arith.Robin.LogarithmBounds
import D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus

/-! Two elementary logarithm estimates bound the strict curvature loss.
The full prime-power arithmetic inequality pays this loss for the actual
positive integer, with a strict positive remainder. -/

set_option autoImplicit false

namespace D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus

open D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
  (fullPrimePowerResidual full_prime_power_arithmetic_surplus)

theorem log_one_add_quadratic {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
  refine le_trans ?_ (Real.le_log_one_add_of_nonneg hu)
  apply (le_div_iff₀ (show 0 < u + 2 by linarith)).mpr
  nlinarith [mul_nonneg hu (sq_nonneg u)]

private theorem loglog_curvature {z M : ℝ}
    (hz : 1 < z) (hM : 0 < M) (hMhalf : M < 1 / 2) :
    0 < Real.log (Real.log z) + M / (z * Real.log z) -
        Real.log (Real.log (z + M)) ∧
      Real.log (Real.log z) + M / (z * Real.log z) -
        Real.log (Real.log (z + M)) <
          (Real.log z + 1) / (8 * z ^ 2 * (Real.log z) ^ 2) := by
  have hz0 : 0 < z := by linarith
  have hL : 0 < Real.log z := Real.log_pos hz
  have ht : 0 < M / z := div_pos hM hz0
  have hlogt0 : 0 ≤ Real.log (1 + M / z) :=
    Real.log_nonneg (by linarith only [ht])
  have hlogt : Real.log (1 + M / z) ≤ M / z := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + M / z by positivity)
    linarith only [h]
  have ha0 : 0 ≤ Real.log (1 + M / z) / Real.log z :=
    div_nonneg hlogt0 hL.le
  have ha : Real.log (1 + M / z) / Real.log z ≤ (M / z) / Real.log z :=
    div_le_div_of_nonneg_right hlogt hL.le
  have haLow : (M / z - (M / z) ^ 2 / 2) / Real.log z ≤
      Real.log (1 + M / z) / Real.log z :=
    div_le_div_of_nonneg_right (log_one_add_quadratic ht.le) hL.le
  have hout := log_one_add_quadratic ha0
  have hsquare : (Real.log (1 + M / z) / Real.log z) ^ 2 ≤
      ((M / z) / Real.log z) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha)
      (add_nonneg (ha0.trans ha) ha0)]
  have hzM : z + M = z * (1 + M / z) := by field_simp [hz0.ne'] <;> ring
  have hlogzM : Real.log (z + M) = Real.log z + Real.log (1 + M / z) := by
    rw [hzM, Real.log_mul hz0.ne' (by positivity)]
  have houter : Real.log (Real.log (z + M)) = Real.log (Real.log z) +
      Real.log (1 + Real.log (1 + M / z) / Real.log z) := by
    rw [hlogzM]
    have hid : Real.log z + Real.log (1 + M / z) =
        Real.log z * (1 + Real.log (1 + M / z) / Real.log z) := by
      field_simp [hL.ne'] <;> ring
    rw [hid, Real.log_mul hL.ne' (by positivity)]
  have hquad : Real.log (Real.log z) + M / (z * Real.log z) -
      Real.log (Real.log (z + M)) ≤
        M ^ 2 * (Real.log z + 1) / (2 * z ^ 2 * (Real.log z) ^ 2) := by
    rw [houter]
    have halgebra : M / (z * Real.log z) -
        (M / z - (M / z) ^ 2 / 2) / Real.log z +
          ((M / z) / Real.log z) ^ 2 / 2 =
        M ^ 2 * (Real.log z + 1) / (2 * z ^ 2 * (Real.log z) ^ 2) := by
      field_simp [hz0.ne', hL.ne']
      <;> ring
    rw [← halgebra]
    linarith only [haLow, hout, hsquare]
  constructor
  · have htangent :=
      D5.S3.Arith.Robin.RestrictedDivisorStrictInventory.loglog_tangent
        hz (show 1 < z + M by linarith) (show z ≠ z + M by linarith)
    dsimp only [D5.S3.Arith.Robin.ActualRobinClockCovariance.g] at htangent
    have heq : (z + M - z) * (1 / (z * Real.log z)) = M / (z * Real.log z) := by ring
    rw [heq] at htangent
    linarith only [htangent]
  · apply lt_of_le_of_lt hquad
    have hM2 : M ^ 2 < 1 / 4 := by
      have hp : 0 < (1 / 2 - M) * (1 / 2 + M) :=
        mul_pos (sub_pos.mpr hMhalf) (by linarith)
      nlinarith only [hp]
    apply (div_lt_div_iff₀ (by positivity : 0 < 2 * z ^ 2 * (Real.log z) ^ 2)
      (by positivity : 0 < 8 * z ^ 2 * (Real.log z) ^ 2)).mpr
    have hp : 0 < (Real.log z + 1) * z ^ 2 * (Real.log z) ^ 2 := by positivity
    nlinarith only [mul_pos (sub_pos.mpr hM2) hp]

private theorem curvature_bound_lt_surplus_half {z : ℝ} (hz : 11 < z) :
    (Real.log z + 1) / (8 * z ^ 2 * (Real.log z) ^ 2) <
      Real.log 2 / (12 * z * Real.log z) := by
  have hz0 : 0 < z := by linarith
  have hL : 1 < Real.log z :=
    (Real.lt_log_iff_exp_lt hz0).mpr
      (Real.exp_one_lt_three.trans (by linarith))
  have hlog2 : 2 / 3 < Real.log (2 : ℝ) := by
    have h := Real.lt_log_one_add_of_pos (show (0 : ℝ) < 1 by norm_num)
    norm_num at h
    exact h
  apply (div_lt_div_iff₀ (by positivity : 0 < 8 * z ^ 2 * (Real.log z) ^ 2)
    (by positivity : 0 < 12 * z * Real.log z)).mpr
  have hfactor : 0 < (2 * Real.log 2 * z * Real.log z -
      3 * (Real.log z + 1)) := by
    have h1 : (2 / 3 : ℝ) * z < Real.log 2 * z :=
      mul_lt_mul_of_pos_right hlog2 hz0
    have h2 : (2 / 3 : ℝ) * z * Real.log z <
        Real.log 2 * z * Real.log z :=
      mul_lt_mul_of_pos_right h1 (by linarith)
    have h3 : 11 * Real.log z < z * Real.log z :=
      mul_lt_mul_of_pos_right hz (by linarith)
    nlinarith only [hL, h2, h3]
  have hp : 0 < z * Real.log z := by positivity
  nlinarith only [mul_pos hfactor hp]

/-- The complete arithmetic surplus pays the actual log-log curvature loss.
All omitted prime-power layers and the original positive integer are retained.
This is a finite-state inequality; it asserts no signed-integral identity. -/
theorem arithmetic_surplus_dominates_loglog_curvature {z M : ℝ}
    (hz : 11 < z) (hM : 0 < M) (hMhalf : M < 1 / 2) {n : ℕ}
    (hn : 0 < n)
    (hsupport : n.primeFactors = Nat.primesLE ⌊z⌋₊) :
    let K := Real.log (Real.log z) + M / (z * Real.log z) -
      Real.log (Real.log (z + M))
    0 < K ∧ K < (Real.log z + 1) / (8 * z ^ 2 * (Real.log z) ^ 2) ∧
      Real.log 2 / (12 * z * Real.log z) <
        D5.S3.Arith.Robin.OriginalEndpointPrimeTail.tail n +
          (Real.log (n : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
            fullPrimePowerResidual z - K := by
  dsimp only
  obtain ⟨hk, hquad⟩ := loglog_curvature (by linarith : 1 < z) hM hMhalf
  refine ⟨hk, hquad, ?_⟩
  have hsmall := hquad.trans (curvature_bound_lt_surplus_half hz)
  have harith :=
    full_prime_power_arithmetic_surplus
      (by linarith : 4 ≤ z) hn hsupport
  have hhalf : Real.log 2 / (6 * z * Real.log z) =
      2 * (Real.log 2 / (12 * z * Real.log z)) := by ring
  rw [hhalf] at harith
  linarith only [hsmall, harith]

/-- Half the actual complete surplus pays curvature; the remaining half
retains the explicit root-scale constant. -/
theorem arithmetic_surplus_sub_curvature_root_scale {z M : ℝ}
    (hz : 11 < z) (hM : 0 < M) (hMhalf : M < 1 / 2) {n : ℕ}
    (hn : 0 < n) (hsupport : n.primeFactors = Nat.primesLE ⌊z⌋₊) :
    let K := Real.log (Real.log z) + M / (z * Real.log z) -
      Real.log (Real.log (z + M))
    1 / (4000 * Real.sqrt z * Real.log z) <
      D5.S3.Arith.Robin.OriginalEndpointPrimeTail.tail n +
        (Real.log (n : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
          fullPrimePowerResidual z - K := by
  dsimp only
  obtain ⟨_, hquad⟩ := loglog_curvature (by linarith : 1 < z) hM hMhalf
  have hsmall := hquad.trans (curvature_bound_lt_surplus_half hz)
  have hold := full_prime_power_arithmetic_surplus (by linarith : 4 ≤ z) hn hsupport
  have hroot :=
    D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.full_prime_power_arithmetic_surplus_root_scale
      (by linarith : 4 ≤ z) hn hsupport
  have hhalf : Real.log (Real.log z) + M / (z * Real.log z) -
      Real.log (Real.log (z + M)) <
      (D5.S3.Arith.Robin.OriginalEndpointPrimeTail.tail n +
        (Real.log (n : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
          fullPrimePowerResidual z) / 2 := by
    have heq : Real.log 2 / (6 * z * Real.log z) =
        2 * (Real.log 2 / (12 * z * Real.log z)) := by ring
    linarith only [hsmall, hold, heq]
  have heq : 1 / (2000 * Real.sqrt z * Real.log z) =
      2 * (1 / (4000 * Real.sqrt z * Real.log z)) := by ring
  linarith only [hroot, hhalf, heq]

end D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
