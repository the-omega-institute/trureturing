/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeUnattainedEndpointMass
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeUnattainedEndpointMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-tail negative mass is little-o at the endpoint for an unattained abscissa. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedShortWindows

/-! Endpoint-scale mass over real windows when the zeta zero abscissa is unattained. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa zero_re_le_abscissa)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open MaximalRealPartProjection (maximalSeries)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeUnattainedEndpointMass

open PrimeAttainedShortWindows (normalized_complete_tail_approx normalized_prime_power_error)
open PrimeOnlyTailCorrection (primeTail prime_integrable)

private theorem normalized_prime_tail_tendsto_zero (hΘ : 1 / 2 < zeroAbscissa)
    (hun : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re < zeroAbscissa) :
    Tendsto (fun x : ℝ => x ^ (1 - zeroAbscissa) * primeTail x) atTop (𝓝 0) := by
  have hzero (j : ℕ) : IsNontrivialZero (actualZero j) :=
    actualData.zero_isNontrivial (actualOccurrenceEquiv j).1
  have hmax (j : ℕ) : (actualZero j).re ≤ zeroAbscissa := zero_re_le_abscissa (hzero j)
  have hseries (t : ℝ) : maximalSeries actualCoeff actualZero zeroAbscissa t = 0 := by
    classical
    change (∑' j : ℕ, if (actualZero j).re = zeroAbscissa then
      actualCoeff j * Complex.exp ((t : ℂ) * (actualZero j - (zeroAbscissa : ℂ))) else 0) = 0
    simp only [(hun _ (hzero _)).ne, ite_false, tsum_zero]
  have hcomplete := normalized_complete_tail_approx (by linarith only [hΘ]) hmax
  simp only [hseries, Complex.zero_re, add_zero] at hcomplete
  have hlog := (hcomplete.sub (normalized_prime_power_error hΘ)).comp Real.tendsto_log_atTop
  rw [sub_self] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_def, Real.exp_log hx, Real.rpow_def_of_pos hx]
  rw [mul_comm (Real.log x), ← mul_sub, sub_sub_cancel]

/-- At an unattained zeta zero abscissa above one half, the negative mass of the
prime-only Chebyshev tail is little-o at the endpoint power. -/
theorem prime_tail_endpoint_mass_tendsto_zero (hΘ : 1 / 2 < zeroAbscissa)
    (hun : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re < zeroAbscissa) :
    Tendsto (fun B : ℝ => (∫ x in (2 : ℝ)..B, max (-primeTail x) 0 / Real.sqrt x) /
      B ^ (zeroAbscissa - 1 / 2)) atTop (𝓝 0) := by
  let p : ℝ := zeroAbscissa - 1 / 2
  let mass (x : ℝ) : ℝ := max (-primeTail x) 0 / Real.sqrt x
  change Tendsto (fun B : ℝ => (∫ x in (2 : ℝ)..B, mass x) / B ^ p) atTop (𝓝 0)
  have hp : 0 < p := sub_pos.mpr hΘ
  have hnonneg (x : ℝ) : 0 ≤ mass x := div_nonneg (le_max_right _ _) (Real.sqrt_nonneg x)
  have hint {A B : ℝ} (hA : 2 ≤ A) (hAB : A ≤ B) : IntervalIntegrable mass volume A B := by
    have hone (x : ℝ) (hx : x ∈ uIcc A B) : 1 ≤ x := by
      rw [uIcc_of_le hAB] at hx
      exact one_le_two.trans (hA.trans hx.1)
    exact (((prime_integrable.continuousOn_Ici_primitive_Ioi.mono hone).neg.sup
      continuousOn_const).div Real.continuous_sqrt.continuousOn
        (fun x hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (hone x hx))).ne')).intervalIntegrable
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hc : 0 < ε / 2 * p := mul_pos (half_pos hε) hp
  have hsmall := (Metric.tendsto_nhds.mp (normalized_prime_tail_tendsto_zero hΘ hun)) _ hc
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hsmall
  let X := max 2 Y
  have hX : 2 ≤ X := le_max_left _ _
  have hdom (x : ℝ) (hx : X ≤ x) : mass x ≤ (ε / 2 * p) * x ^ (p - 1) := by
    have hx₀ : 0 < x := (by norm_num : (0 : ℝ) < 2).trans_le (hX.trans hx)
    have hpow : 0 < x ^ (1 - zeroAbscissa) := Real.rpow_pos_of_pos hx₀ _
    have hroot : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx₀
    have hbound := hY x ((le_max_right _ _).trans hx)
    rw [Real.dist_eq, sub_zero] at hbound
    have hneg : -primeTail x * x ^ (1 - zeroAbscissa) ≤ ε / 2 * p := by
      rw [neg_mul, mul_comm (primeTail x)]
      exact (neg_le_abs _).trans hbound.le
    have hweight : x ^ (p - 1) * Real.sqrt x * x ^ (1 - zeroAbscissa) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx₀, ← Real.rpow_add hx₀,
        show p - 1 + 1 / 2 + (1 - zeroAbscissa) = 0 by dsimp [p]; ring, Real.rpow_zero]
    apply (div_le_iff₀ hroot).2
    apply (mul_le_mul_iff_left₀ hpow).1
    change max (-primeTail x) 0 * x ^ (1 - zeroAbscissa) ≤ _
    rw [mul_assoc (ε / 2 * p), mul_assoc (ε / 2 * p), hweight, mul_one,
      max_mul_of_nonneg _ _ hpow.le, zero_mul]
    exact max_le hneg hc.le
  have hheadLimit := (tendsto_rpow_atTop hp).const_div_atTop (∫ x in (2 : ℝ)..X, mass x)
  have hhead := hheadLimit.eventually_lt_const (half_pos hε)
  filter_upwards [eventually_ge_atTop X, hhead] with B hXB hheadB
  have hB : 2 ≤ B := hX.trans hXB
  have hBp : 0 < B ^ p := Real.rpow_pos_of_pos ((by norm_num : (0 : ℝ) < 2).trans_le hB) _
  have hpint : -1 < p - 1 := by linarith only [hp]
  have htail : (∫ x in X..B, mass x) ≤ (ε / 2) * B ^ p := by
    calc
      _ ≤ ∫ x in X..B, (ε / 2 * p) * x ^ (p - 1) :=
        intervalIntegral.integral_mono_on hXB (hint hX hXB)
          ((intervalIntegral.intervalIntegrable_rpow' hpint).const_mul _) (fun x hx => hdom x hx.1)
      _ = (ε / 2) * (B ^ p - X ^ p) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hpint),
          sub_add_cancel, mul_assoc, mul_div_cancel₀ _ hp.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sub_le_self _ (Real.rpow_nonneg ((by norm_num : (0 : ℝ) ≤ 2).trans hX) _)) (half_pos hε).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg
    (intervalIntegral.integral_nonneg_of_forall hB hnonneg) hBp.le),
    ← intervalIntegral.integral_add_adjacent_intervals (hint le_rfl hX) (hint hX hXB), add_div]
  have htailB := (div_le_iff₀ hBp).2 htail
  linarith only [hheadB, htailB]

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeUnattainedEndpointMass
