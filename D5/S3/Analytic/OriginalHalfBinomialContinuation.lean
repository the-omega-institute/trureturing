/- GID: D5/S3/Analytic/OriginalHalfBinomialContinuation
   generality: I
   mirror-B: D5/B/S3/Analytic/OriginalHalfBinomialContinuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.MeanValue, mathlib/module/Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv]
   utility: none
   digest: Actual slit-disk continuation of the original complementary period ratio and numerator. -/

import D5.S3.Analytic.OriginalHalfBinomialDiskCorrection

/-! The normalized continuation uses the literal original period and its native endpoint. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology

namespace D5.S3.Analytic.OriginalHalfBinomialContinuation
open OriginalHalfBinomialPeriod (period)
open OriginalHalfBinomialWronskian (tau)
open OriginalHalfBinomialDiskCorrection

/-- The unit disk cut along the nonpositive real axis. -/
def slitDisk : Set ℂ := disk ∩ Complex.slitPlane

/-- The full overlap of the original two period disks. -/
def lens : Set ℂ := Metric.ball 0 1 ∩ Metric.ball 1 1

/-- The normalized logarithmic continuation using the actual disk primitive. -/
def t0 (r : ℂ) : ℂ :=
  (Complex.I / (Real.pi : ℂ)) * ((Real.log 16 : ℂ) - Complex.log r) + H r

/-- The continued original numerator. -/
def n0 (r : ℂ) : ℂ := period r * t0 r

private lemma lens_iff (r : ℂ) : r ∈ lens ↔ ‖r‖ < 1 ∧ ‖1 - r‖ < 1 := by
  simp only [lens, mem_inter_iff, Metric.mem_ball, dist_zero_right]
  rw [dist_comm r (1 : ℂ), dist_eq_norm]

private lemma lens_slit {r : ℂ} (hr : r ∈ lens) : r ∈ slitDisk := by
  refine ⟨hr.1, Complex.mem_slitPlane_iff.mpr (Or.inl ?_)⟩
  have h := (Complex.re_le_norm (1 - r)).trans_lt ((lens_iff r).mp hr).2
  simp only [Complex.sub_re, Complex.one_re] at h
  linarith

private lemma slit_open : IsOpen slitDisk :=
  Metric.isOpen_ball.inter Complex.isOpen_slitPlane

private lemma denom_nonzero {r : ℂ} (hr : r ∈ disk) :
    1 - r ≠ 0 ∧ period r ≠ 0 := by
  constructor
  · intro he
    have : r = 1 := (sub_eq_zero.mp he).symm
    simpa [disk, this] using hr
  · exact D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.period_ne_zero
      (by simpa [disk] using hr)

private lemma t0_derivative {r : ℂ} (hr : r ∈ slitDisk) :
    HasDerivAt t0 (-Complex.I / ((Real.pi : ℂ) * r * (1 - r) * period r ^ 2)) r := by
  have hH := disk_correction.2.2.2.2.2.2.2.2.2.1 r hr.1
  have hG := disk_correction.2.2.2.2.2.2.2.1 r
  have hr0 := Complex.slitPlane_ne_zero hr.2
  have hd := (((Complex.hasDerivAt_log hr.2).const_sub (Real.log 16 : ℂ)).const_mul
    (Complex.I / (Real.pi : ℂ))).add hH
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hG' : G r = (R r - 1) / r := (eq_div_iff hr0).mpr (by simpa [mul_comm] using hG)
  convert hd using 1
  · funext z
    rfl
  · rw [hG', R]
    field_simp [hpi, hr0, (denom_nonzero hr.1).1, (denom_nonzero hr.1).2]
    <;> ring

private lemma real_period {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    period (r : ℂ) = ((period (r : ℂ)).re : ℂ) := by
  have hi := (OriginalHalfBinomialIntegral.original_series_eq_integral r hr hr1).2.2
  change period (r : ℂ) = _ at hi
  simp only [hi, Complex.ofReal_re]

/- The product of log r with the first-order period error vanishes. The slope
limit comes from actual differentiability of the literal period at zero. -/
private lemma native_log_error :
    Tendsto (fun r : ℝ => Real.pi * (period ((1 - r : ℝ) : ℂ)).re /
      (period (r : ℂ)).re + Real.log r - Real.log 16) (𝓝[>] 0) (𝓝 0) := by
  let F : ℝ → ℝ := fun r => (period (r : ℂ)).re
  have hF0 : F 0 = 1 := by simp [F, disk_correction.1]
  have hd : HasDerivAt F (deriv period 0).re 0 :=
    (OriginalHalfBinomialPeriod.picard_fuchs (z := 0) (by norm_num)).1.hasDerivAt.real_of_complex
  have hF : Tendsto F (𝓝[>] 0) (𝓝 1) := by
    simpa only [hF0] using hd.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hinv := hd.inv (by rw [hF0]; norm_num)
  have hslope : Tendsto (fun r : ℝ => (1 / F r - 1) / r) (𝓝[>] 0)
      (𝓝 (-((deriv period 0).re))) := by
    simpa [hF0, smul_eq_mul, div_eq_mul_inv, mul_comm] using hinv.tendsto_slope_zero_right
  have hlog : Tendsto (fun r : ℝ => Real.log r * r) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1))
  have herror : Tendsto (fun r : ℝ => Real.log r * (1 / F r - 1))
      (𝓝[>] 0) (𝓝 0) := by
    have h := hlog.mul hslope
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    field_simp [ne_of_gt (show 0 < r from hr)]
  have h := ((OriginalHalfBinomialEndpoint.original_period_log16.div hF (by norm_num)).sub
    herror).sub_const (Real.log 16)
  simp only [div_one, sub_zero, sub_self] at h
  apply h.congr'
  filter_upwards [] with r
  dsimp [F]
  ring

private lemma radial_difference :
    Tendsto (fun r : ℝ => t0 (r : ℂ) - tau (r : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have hH : Tendsto (fun r : ℝ => H (r : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hh := (disk_correction.2.2.2.2.2.2.2.2.2.1 0 (by simp [disk])).continuousAt
    have h := hh.tendsto.comp (Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
    simpa only [Function.comp_def, disk_correction.2.2.2.2.2.2.2.2.1] using! h
  have herr := Complex.continuous_ofReal.continuousAt.tendsto.comp native_log_error
  have h := hH.sub (herr.const_mul (Complex.I / (Real.pi : ℂ)))
  simp only [Complex.ofReal_zero, mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with r hr hr1
  have hr0 : 0 < r := hr
  dsimp only [Function.comp_def]
  rw [t0, tau, real_period hr0.le hr1,
    show (1 : ℂ) - (r : ℂ) = ((1 - r : ℝ) : ℂ) by push_cast; rfl,
    real_period (by linarith) (by linarith), ← Complex.ofReal_log hr0.le]
  simp only [Complex.ofReal_re]
  push_cast
  field_simp
  <;> ring

/-- The logarithmic formula has the native derivative on the whole slit disk
and equals the literal original ratio on the full complex lens. -/
theorem actual_continuation :
    (∀ r ∈ slitDisk, HasDerivAt t0
      (-Complex.I / ((Real.pi : ℂ) * r * (1 - r) * period r ^ 2)) r) ∧
    EqOn t0 tau lens := by
  refine ⟨fun r hr => t0_derivative hr, ?_⟩
  have hd : ∀ r ∈ lens, HasDerivAt (fun z => t0 z - tau z) 0 r := by
    intro r hr
    have h := (lens_iff r).mp hr
    simpa only [sub_self] using! (t0_derivative (lens_slit hr)).sub
      (OriginalHalfBinomialWronskian.original_tau_hasDerivAt h.1 h.2).2
  intro r hr
  have hc (z : ℂ) (hz : z ∈ lens) : t0 z - tau z = t0 r - tau r :=
    (Metric.isOpen_ball.inter Metric.isOpen_ball).is_const_of_deriv_eq_zero
      ((convex_ball (0 : ℂ) 1).inter (convex_ball 1 1)).isPreconnected
      (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hd w hw).deriv) hz hr
  have hlim : Tendsto (fun z : ℝ => t0 (z : ℂ) - tau (z : ℂ))
      (𝓝[>] 0) (𝓝 (t0 r - tau r)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with z hz hz1
    symm
    apply hc
    rw [lens_iff]
    have hz0 : 0 < z := hz
    constructor
    · simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz0] using hz1
    · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (show 0 < 1 - z by linarith)]
      linarith
  exact sub_eq_zero.mp (tendsto_nhds_unique hlim radial_difference)

/-- The actual continued numerator is holomorphic on the full slit disk,
agrees with the original complementary numerator on the full lens, and satisfies
the native Picard-Fuchs equation and oriented Wronskian there. -/
theorem continued_numerator :
    DifferentiableOn ℂ n0 slitDisk ∧
    (∀ r ∈ lens, n0 r = Complex.I * period (1 - r)) ∧
    (∀ r ∈ slitDisk, DifferentiableAt ℂ (deriv n0) r ∧
      r * (1 - r) * deriv (deriv n0) r +
        (1 - 2 * r) * deriv n0 r - (1 / 4 : ℂ) * n0 r = 0 ∧
      deriv n0 r * period r - n0 r * deriv period r =
        -Complex.I / ((Real.pi : ℂ) * r * (1 - r))) := by
  have hp (r : ℂ) (hr : r ∈ slitDisk) := OriginalHalfBinomialPeriod.picard_fuchs
    (z := r) (by simpa [disk] using hr.1)
  have ht : DifferentiableOn ℂ t0 slitDisk :=
    fun r hr => (t0_derivative hr).differentiableAt.differentiableWithinAt
  have hn (r : ℂ) (hr : r ∈ slitDisk) :
      HasDerivAt n0 (deriv period r * t0 r + period r * deriv t0 r) r := by
    exact (hp r hr).1.hasDerivAt.mul (t0_derivative hr).differentiableAt.hasDerivAt
  refine ⟨fun r hr => (hn r hr).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro r hr
    rw [n0, actual_continuation.2 hr, tau]
    field_simp [(denom_nonzero hr.1).2]
  · intro r hr
    have ht2 := (ht.deriv slit_open).differentiableAt (slit_open.mem_nhds hr)
    have ht1 := (t0_derivative hr).differentiableAt.hasDerivAt
    have hen : deriv n0 =ᶠ[𝓝 r]
        (fun z => deriv period z * t0 z + period z * deriv t0 z) := by
      filter_upwards [slit_open.mem_nhds hr] with z hz
      exact (hn z hz).deriv
    have hn2 : HasDerivAt (deriv n0)
        (deriv (deriv period) r * t0 r + deriv period r * deriv t0 r +
          (deriv period r * deriv t0 r + period r * deriv (deriv t0) r)) r := by
      exact (((hp r hr).2.1.hasDerivAt.mul ht1).add
        ((hp r hr).1.hasDerivAt.mul ht2.hasDerivAt)).congr_of_eventuallyEq hen
    have he : (fun z => z * (1 - z) * period z ^ 2 * deriv t0 z) =ᶠ[𝓝 r]
        (fun _ => -Complex.I / (Real.pi : ℂ)) := by
      filter_upwards [slit_open.mem_nhds hr] with z hz
      rw [(t0_derivative hz).deriv]
      field_simp [Complex.slitPlane_ne_zero hz.2, (denom_nonzero hz.1).1,
        (denom_nonzero hz.1).2]
    have ha : HasDerivAt (fun z : ℂ => z * (1 - z)) (1 - 2 * r) r := by
      convert (hasDerivAt_id r).mul ((hasDerivAt_id r).const_sub 1) using 1
      · rfl
      · dsimp
        ring
    have hk := ((ha.mul ((hp r hr).1.hasDerivAt.pow 2)).mul ht2.hasDerivAt)
    have hk0 := hk.unique ((hasDerivAt_const r (-Complex.I / (Real.pi : ℂ))).congr_of_eventuallyEq he)
    simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] at hk0
    refine ⟨hn2.differentiableAt, ?_, ?_⟩
    · rw [hn2.deriv, (hn r hr).deriv, n0]
      apply mul_left_cancel₀ (denom_nonzero hr.1).2
      linear_combination period r * t0 r * (hp r hr).2.2 + hk0
    · rw [(hn r hr).deriv, n0, (t0_derivative hr).deriv]
      field_simp [Complex.slitPlane_ne_zero hr.2, (denom_nonzero hr.1).1,
        (denom_nonzero hr.1).2]
      <;> ring

end D5.S3.Analytic.OriginalHalfBinomialContinuation
