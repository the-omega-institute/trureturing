/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveEndpoint
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveEndpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Either exponential bound from 5040 characterizes the zeta strip. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveCriterion

/-! Exact exponential bounds for the fixed-anchor signed prime primitive. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U)
open D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity (complete_chebyshev_tail_identity)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveEndpoint

open PrimeOnlyTailCorrection (primeTail prime_integrable prime_power_window_correction)
open SignedPrimePrimitiveCriterion (zeta_zero_re_le_of_signedPrimePrimitive_one_sided_from_5040)

private def primeLogDensity (t : ℝ) : ℝ :=
  primeTail (Real.exp t) / Real.sqrt (Real.exp t) * Real.exp t

private theorem eventually_norm_primeLogDensity_le {β : ℝ} (hβ : 1 / 2 < β)
    (hmax : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≤ β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in atTop,
      ‖primeLogDensity t‖ ≤ C * Real.exp ((β - 1 / 2) * t) := by
  have hzero (j : ℕ) : (actualZero j).re ≤ β :=
    hmax _ (actualData.zero_isNontrivial (actualOccurrenceEquiv j).1).1
  let C : ℝ := ∑' j : ℕ, ‖actualCoeff j‖
  have hC : 0 ≤ C := tsum_nonneg fun _ => norm_nonneg _
  have hH (t : ℝ) (ht : 0 ≤ t) : ‖actualH t‖ ≤ C * Real.exp (β * t) := by
    change ‖∑' j, actualCoeff j * Complex.exp ((t : ℂ) * actualZero j)‖ ≤ _
    refine tsum_of_norm_bounded (actualCoeff_hasSum.summable.norm.hasSum.mul_right _) ?_
    intro j
    rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by
        rw [mul_comm β t]
        exact mul_le_mul_of_nonneg_left (hzero j) ht)) (norm_nonneg _)
  let correction (t : ℝ) := Real.sqrt (Real.exp t) * (Q (Real.exp t) - primeTail (Real.exp t))
  let error (t : ℝ) :=
    RHSharpActualEnvelope.G t - Real.exp (-t / 2) * (actualH t).re + correction t
  have herr : Tendsto error atTop (𝓝 2) := by
    simpa only [error, correction, Function.comp_def, zero_add] using
      RHSharpActualEnvelope.G_sub_normalized_actualH_tendsto_zero.add
      (prime_power_window_correction.1.comp Real.tendsto_exp_atTop)
  refine ⟨C + 3, add_nonneg hC (by norm_num), ?_⟩
  filter_upwards [(Metric.tendsto_nhds.mp herr) 1 zero_lt_one,
    eventually_ge_atTop (0 : ℝ), eventually_ge_atTop (Real.log 2)] with t he ht hlog
  have herror : |error t| ≤ 3 := by
    rw [Real.dist_eq] at he
    have hsum := abs_add_le (error t - 2) (2 : ℝ)
    rw [sub_add_cancel, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hsum
    linarith
  have htwo : 2 ≤ Real.exp t := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hlog
  have hQ := complete_chebyshev_tail_identity chebyshev_error_kernel_integrable htwo
  change Q (Real.exp t) = _ at hQ
  have hU : U (Real.exp t) = -Q (Real.exp t) * Real.exp t := by
    rw [U, hQ]
    field_simp [(Real.exp_pos t).ne']
    ring
  have hroot : Real.exp (-t / 2) * Real.exp t = Real.sqrt (Real.exp t) := by
    rw [← Real.exp_add, ← Real.exp_half]
    congr 1
    ring
  have hG : RHSharpActualEnvelope.G t = -(Real.sqrt (Real.exp t) * Q (Real.exp t)) := by
    rw [RHSharpActualEnvelope.G, hU, ← hroot]
    ring
  have hdensity : primeLogDensity t = Real.sqrt (Real.exp t) * primeTail (Real.exp t) := by
    have hs := Real.sqrt_pos.mpr (Real.exp_pos t)
    have hratio : Real.exp t / Real.sqrt (Real.exp t) = Real.sqrt (Real.exp t) := by
      apply (div_eq_iff hs.ne').2
      rw [← pow_two, Real.sq_sqrt (Real.exp_nonneg t)]
    rw [primeLogDensity, div_mul_eq_mul_div, mul_div_assoc, hratio, mul_comm]
  have hsplit :
      primeLogDensity t = -(Real.exp (-t / 2) * (actualH t).re + error t) := by
    rw [hdensity]
    dsimp only [error, correction]
    rw [hG]
    ring
  have hexp (t : ℝ) : Real.exp (-t / 2) * Real.exp (β * t) = Real.exp ((β - 1 / 2) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hscaled : 1 ≤ Real.exp ((β - 1 / 2) * t) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (sub_nonneg.mpr hβ.le) ht)
  rw [hsplit, norm_neg, Real.norm_eq_abs]
  calc
    _ ≤ |Real.exp (-t / 2) * (actualH t).re| + |error t| := abs_add_le _ _
    _ ≤ Real.exp (-t / 2) * (C * Real.exp (β * t)) + 3 := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact add_le_add (mul_le_mul_of_nonneg_left
        ((Complex.abs_re_le_norm _).trans (hH t ht)) (Real.exp_nonneg _)) herror
    _ = C * Real.exp ((β - 1 / 2) * t) + 3 := by rw [← hexp]; ring
    _ ≤ (C + 3) * Real.exp ((β - 1 / 2) * t) := by
      rw [add_mul]
      exact add_le_add le_rfl (le_mul_of_one_le_right (by norm_num) hscaled)

private theorem abs_primitive_bound_from_5040 {β : ℝ} (hβ : 1 / 2 < β)
    (hmax : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≤ β) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T in atTop,
      |∫ x in (5040 : ℝ)..Real.exp T, primeTail x / Real.sqrt x| ≤
        B * Real.exp ((β - 1 / 2) * T) := by
  obtain ⟨C, hC, hbound⟩ := eventually_norm_primeLogDensity_le hβ hmax
  obtain ⟨R, hR⟩ := eventually_atTop.mp hbound
  let a := Real.log 5040
  let U := max R a
  let p := β - 1 / 2
  let f (x : ℝ) := primeTail x / Real.sqrt x
  let g := primeLogDensity
  have hp : 0 < p := sub_pos.mpr hβ
  have ha : 0 ≤ a := Real.log_nonneg (by norm_num)
  have hU : a ≤ U := le_max_right _ _
  have he (t : ℝ) (ht : a ≤ t) : 1 ≤ Real.exp t := by
    have h := Real.exp_le_exp.mpr ht
    rw [show Real.exp a = 5040 from Real.exp_log (by norm_num)] at h
    linarith
  have hf : ContinuousOn f (Ici 1) :=
    prime_integrable.continuousOn_Ici_primitive_Ioi.div Real.continuous_sqrt.continuousOn
      (fun _ hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)).ne')
  have hg : ContinuousOn g (Ici a) :=
    (hf.comp Real.continuous_exp.continuousOn he).mul Real.continuous_exp.continuousOn
  have hint {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) : IntervalIntegrable g volume u v :=
    (hg.mono (fun _ hx => hu.trans hx.1)).intervalIntegrable_of_Icc huv
  have hpoint (t : ℝ) (ht : U ≤ t) : ‖g t‖ ≤ C * Real.exp (p * t) :=
    hR t ((le_max_left R a).trans ht)
  let H : ℝ := ∫ t in a..U, g t
  refine ⟨‖H‖ + C / p, add_nonneg (norm_nonneg _) (div_nonneg hC hp.le), ?_⟩
  filter_upwards [eventually_ge_atTop U] with T hT
  have haT := hU.trans hT
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := a) (b := T) (f := Real.exp) (f' := Real.exp) (g := f)
    (fun t _ => Real.hasDerivAt_exp t) Real.continuous_exp.continuousOn
    (hf.mono (by
      rintro _ ⟨t, ht, rfl⟩
      exact he t ((uIcc_of_le haT ▸ ht).1)))
  have hsplit : (∫ x in (5040 : ℝ)..Real.exp T, f x) = H + ∫ t in U..T, g t := by
    calc
      _ = ∫ t in a..T, g t := by
        simpa only [a, Real.exp_log (by norm_num : (0 : ℝ) < 5040),
          g, primeLogDensity, f, Function.comp_apply] using hsub.symm
      _ = _ := (intervalIntegral.integral_add_adjacent_intervals (hint le_rfl hU) (hint hU hT)).symm
  have hcont : Continuous (fun t : ℝ => C * Real.exp (p * t)) := by fun_prop
  have hmajor : (∫ t in U..T, C * Real.exp (p * t)) =
      C / p * Real.exp (p * T) - C / p * Real.exp (p * U) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      convert ((Real.hasDerivAt_exp (p * t)).comp t
        ((hasDerivAt_id t).const_mul p)).const_mul (C / p) using 1
      · simp only [Function.comp_apply]
      · field_simp [hp.ne'] <;> ring
    · exact hcont.intervalIntegrable _ _
  change |∫ x in (5040 : ℝ)..Real.exp T, f x| ≤ _
  rw [hsplit, ← Real.norm_eq_abs]
  have hexp : 1 ≤ Real.exp (p * T) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hp.le (ha.trans haT))
  calc
    _ ≤ ‖H‖ + ‖∫ t in U..T, g t‖ := norm_add_le _ _
    _ ≤ ‖H‖ + ∫ t in U..T, ‖g t‖ :=
      add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hT)
    _ ≤ ‖H‖ + ∫ t in U..T, C * Real.exp (p * t) :=
      add_le_add le_rfl (intervalIntegral.integral_mono_on hT (hint hU hT).norm
        (hcont.intervalIntegrable _ _) (fun t ht => hpoint t ht.1))
    _ ≤ ‖H‖ + C / p * Real.exp (p * T) := by
      rw [hmajor]
      exact add_le_add le_rfl (sub_le_self _ (by positivity))
    _ ≤ (‖H‖ + C / p) * Real.exp (p * T) := by
      rw [add_mul]
      exact add_le_add (le_mul_of_one_le_right (norm_nonneg _) hexp) le_rfl

/-- Above one half, a constant majorant at the exact exponential rate on
either nonzero signed multiple of the prime primitive from 5040 is
equivalent to the corresponding zero strip. -/
theorem zeta_strip_iff_signedPrimePrimitive_constant_bound_from_5040 {β c : ℝ}
    (hβ : 1 / 2 < β) (hc : c ≠ 0) :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≤ β) ↔
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T in atTop,
        c * (∫ x in (5040 : ℝ)..Real.exp T, primeTail x / Real.sqrt x) ≤
          Real.exp ((β - 1 / 2) * T) * B := by
  constructor
  · intro hmax
    obtain ⟨B, hB, h⟩ := abs_primitive_bound_from_5040 hβ hmax
    refine ⟨|c| * B, mul_nonneg (abs_nonneg _) hB, h.mono fun T hT => ?_⟩
    calc
      _ ≤ |c * (∫ x in (5040 : ℝ)..Real.exp T, primeTail x / Real.sqrt x)| :=
        le_abs_self _
      _ ≤ |c| * (B * Real.exp ((β - 1 / 2) * T)) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hT (abs_nonneg _)
      _ = _ := by ring
  · rintro ⟨B, _, h⟩ ρ hρ
    by_cases hβ1 : β < 1
    · exact zeta_zero_re_le_of_signedPrimePrimitive_one_sided_from_5040 hβ.le hβ1 hc
        (A := 0) (B := B) (by simpa only [zero_mul, zero_add] using h) hρ
    · exact (le_of_not_gt fun h => riemannZeta_ne_zero_of_one_lt_re h hρ).trans
        (le_of_not_gt hβ1)

#print axioms zeta_strip_iff_signedPrimePrimitive_constant_bound_from_5040

end D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveEndpoint
