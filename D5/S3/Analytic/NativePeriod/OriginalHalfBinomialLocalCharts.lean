/- GID: D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts
   generality: I
   mirror-B: D5/B/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv]
   utility: none
   digest: Normalized holomorphic local charts for the actual native logarithmic period pair. -/

import D5.S3.Analytic.OriginalHalfBinomialContinuation

/-! The charts preserve the literal native periods, their equation and their phase. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology

namespace D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
open OriginalHalfBinomialPeriod (period)
open OriginalHalfBinomialDiskCorrection
open OriginalHalfBinomialContinuation

/-- The exponential covering half-plane of the punctured unit disk. -/
def E : Set ℂ := {z | z.re < 0}

/-- The original ratio lifted with its fixed log(16) normalization. -/
def T (z : ℂ) : ℂ := Complex.I / (Real.pi : ℂ) * ((Real.log 16 : ℂ) - z) + H (Complex.exp z)

def Y (z : ℂ) : ℂ := period (Complex.exp z)

def N (z : ℂ) : ℂ := Y z * T z

/-- The normalized inverse chart at exp(z), including its specified value z. -/
def localLog (z r : ℂ) : ℂ := z + Complex.log (r / Complex.exp z)

def chartDomain (z : ℂ) : Set ℂ := disk ∩ {r | r / Complex.exp z ∈ Complex.slitPlane}

def chartT (z r : ℂ) : ℂ :=
  Complex.I / (Real.pi : ℂ) * ((Real.log 16 : ℂ) - localLog z r) + H r

def chartN (z r : ℂ) : ℂ := period r * chartT z r

private lemma exp_disk {z : ℂ} (hz : z ∈ E) : Complex.exp z ∈ disk := by
  simpa only [disk, Metric.mem_ball, dist_zero_right, Complex.norm_exp,
    ← Real.exp_zero, Real.exp_lt_exp] using (show z.re < 0 from hz)

private lemma chart_open (z : ℂ) : IsOpen (chartDomain z) :=
  Metric.isOpen_ball.inter (Complex.isOpen_slitPlane.preimage (by fun_prop))

private lemma chart_self {z : ℂ} (hz : z ∈ E) : Complex.exp z ∈ chartDomain z := by
  exact ⟨exp_disk hz, by simp [Complex.exp_ne_zero, Complex.mem_slitPlane_iff]⟩

private lemma chart_ne_zero {z r : ℂ} (hr : r ∈ chartDomain z) : r ≠ 0 := by
  have h := Complex.slitPlane_ne_zero hr.2
  exact fun he => h (by simp [he])

private lemma localLog_exp (z : ℂ) : localLog z (Complex.exp z) = z := by
  simp [localLog, Complex.exp_ne_zero]

private lemma exp_localLog {z r : ℂ} (hr : r ∈ chartDomain z) :
    Complex.exp (localLog z r) = r := by
  rw [localLog, Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero hr.2)]
  field_simp

private lemma localLog_derivative {z r : ℂ} (hr : r ∈ chartDomain z) :
    HasDerivAt (localLog z) (1 / r) r := by
  have hd := ((Complex.hasDerivAt_log hr.2).comp r
    ((hasDerivAt_id r).div_const (Complex.exp z))).const_add z
  convert hd using 1
  · funext w; rfl
  · field_simp [chart_ne_zero hr, Complex.exp_ne_zero]

private lemma localLog_left (z : ℂ) :
    (fun w => localLog z (Complex.exp w)) =ᶠ[𝓝 z] (fun w => w) := by
  have hm : {w : ℂ | (w - z).im ∈ Ioo (-Real.pi) Real.pi} ∈ 𝓝 z := by
    apply (isOpen_Ioo.preimage (by fun_prop : Continuous (fun w : ℂ => (w - z).im))).mem_nhds
    simp [Real.pi_pos]
  filter_upwards [hm] with w hw
  rw [localLog, ← Complex.exp_sub, Complex.log_exp hw.1 hw.2.le]
  ring

private lemma chartT_derivative {z r : ℂ} (hr : r ∈ chartDomain z) :
    HasDerivAt (chartT z)
      (-Complex.I / ((Real.pi : ℂ) * r * (1 - r) * period r ^ 2)) r := by
  have hd := (((localLog_derivative hr).const_sub (Real.log 16 : ℂ)).const_mul
    (Complex.I / (Real.pi : ℂ))).add
    (disk_correction.2.2.2.2.2.2.2.2.2.1 r hr.1)
  have hr0 := chart_ne_zero hr
  have hp : period r ≠ 0 :=
    D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.period_ne_zero
      (by simpa [disk] using hr.1)
  have hr1 : 1 - r ≠ 0 := by
    intro he
    have : r = 1 := (sub_eq_zero.mp he).symm
    simpa [disk, this] using hr.1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hG : G r = (R r - 1) / r := (eq_div_iff hr0).mpr
    (by simpa [mul_comm] using disk_correction.2.2.2.2.2.2.2.1 r)
  convert hd using 1
  · funext w; rfl
  · rw [hG, R]
    field_simp [hpi, hr0, hr1, hp]
    <;> ring

/-- These are inverse holomorphic charts of the actual cover, with neighborhood
compatibility rather than only equality at their centers. -/
theorem native_chart (z : ℂ) (hz : z ∈ E) :
    IsOpen (chartDomain z) ∧ Complex.exp z ∈ chartDomain z ∧
    localLog z (Complex.exp z) = z ∧
    (∀ r ∈ chartDomain z, Complex.exp (localLog z r) = r ∧
      localLog z r ∈ E ∧ HasDerivAt (localLog z) (1 / r) r ∧
      chartT z r = T (localLog z r) ∧ chartN z r = N (localLog z r)) ∧
    (fun w => localLog z (Complex.exp w)) =ᶠ[𝓝 z] (fun w => w) := by
  refine ⟨chart_open z, chart_self hz, localLog_exp z, ?_, localLog_left z⟩
  intro r hr
  have he := exp_localLog hr
  have hE : localLog z r ∈ E := by
    have hn : ‖r‖ < 1 := by simpa [disk] using hr.1
    rw [← he, Complex.norm_exp, ← Real.exp_zero, Real.exp_lt_exp] at hn
    exact hn
  refine ⟨he, hE, localLog_derivative hr, ?_, ?_⟩
  · simp only [chartT, T, he]
  · simp only [chartN, N, Y, chartT, T, he]

/-- Holomorphy of the literal lifted pair and its exact integer deck action. -/
theorem cover_periods :
    DifferentiableOn ℂ T E ∧ DifferentiableOn ℂ Y E ∧ DifferentiableOn ℂ N E ∧
    (∀ z : ℂ, ∀ k : ℤ,
      T (z + k * (2 * (Real.pi : ℂ) * Complex.I)) = T z + 2 * k ∧
      Y (z + k * (2 * (Real.pi : ℂ) * Complex.I)) = Y z ∧
      N (z + k * (2 * (Real.pi : ℂ) * Complex.I)) = N z + 2 * k * Y z) := by
  have ht (z : ℂ) (hz : z ∈ E) : DifferentiableAt ℂ T z := by
    exact (((differentiableAt_id.const_sub (Real.log 16 : ℂ)).const_mul _).add
      ((disk_correction.2.2.2.2.2.2.2.2.2.1 _ (exp_disk hz)).differentiableAt.comp z
        Complex.differentiableAt_exp))
  have hy (z : ℂ) (hz : z ∈ E) : DifferentiableAt ℂ Y z :=
    (OriginalHalfBinomialPeriod.picard_fuchs (by simpa [disk] using exp_disk hz)).1.comp z
      Complex.differentiableAt_exp
  refine ⟨fun z hz => (ht z hz).differentiableWithinAt,
    fun z hz => (hy z hz).differentiableWithinAt,
    fun z hz => ((hy z hz).mul (ht z hz)).differentiableWithinAt, ?_⟩
  intro z k
  have he : Complex.exp (z + k * (2 * (Real.pi : ℂ) * Complex.I)) = Complex.exp z :=
    Complex.exp_eq_exp_iff_exists_int.mpr ⟨k, rfl⟩
  have ht' : T (z + k * (2 * (Real.pi : ℂ) * Complex.I)) = T z + 2 * k := by
    dsimp [T]
    rw [he]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hpi]
    linear_combination -2 * (k : ℂ) * (Real.pi : ℂ) * Complex.I_sq
  refine ⟨ht', by simp only [Y, he], ?_⟩
  simp only [N, ht', Y, he]
  ring

/-- Every normalized r-chart carries the original equation and the original
oriented Wronskian, including charts crossing the principal logarithm cut. -/
theorem chart_equations (z : ℂ) :
    DifferentiableOn ℂ (chartT z) (chartDomain z) ∧
    DifferentiableOn ℂ (chartN z) (chartDomain z) ∧
    (∀ r ∈ chartDomain z,
      HasDerivAt (chartT z)
        (-Complex.I / ((Real.pi : ℂ) * r * (1 - r) * period r ^ 2)) r ∧
      DifferentiableAt ℂ (deriv (chartN z)) r ∧
      r * (1 - r) * deriv (deriv (chartN z)) r +
        (1 - 2 * r) * deriv (chartN z) r - (1 / 4 : ℂ) * chartN z r = 0 ∧
      deriv (chartN z) r * period r - chartN z r * deriv period r =
        -Complex.I / ((Real.pi : ℂ) * r * (1 - r))) := by
  have hp (r : ℂ) (hr : r ∈ chartDomain z) := OriginalHalfBinomialPeriod.picard_fuchs
    (z := r) (by simpa [disk] using hr.1)
  have ht : DifferentiableOn ℂ (chartT z) (chartDomain z) :=
    fun r hr => (chartT_derivative hr).differentiableAt.differentiableWithinAt
  have hn (r : ℂ) (hr : r ∈ chartDomain z) :
      HasDerivAt (chartN z) (deriv period r * chartT z r + period r * deriv (chartT z) r) r :=
    (hp r hr).1.hasDerivAt.mul (chartT_derivative hr).differentiableAt.hasDerivAt
  refine ⟨ht, fun r hr => (hn r hr).differentiableAt.differentiableWithinAt, ?_⟩
  intro r hr
  have ht2 := (ht.deriv (chart_open z)).differentiableAt ((chart_open z).mem_nhds hr)
  have ht1 := (chartT_derivative hr).differentiableAt.hasDerivAt
  have hen : deriv (chartN z) =ᶠ[𝓝 r]
      (fun w => deriv period w * chartT z w + period w * deriv (chartT z) w) := by
    filter_upwards [(chart_open z).mem_nhds hr] with w hw
    exact (hn w hw).deriv
  have hn2 : HasDerivAt (deriv (chartN z))
      (deriv (deriv period) r * chartT z r + deriv period r * deriv (chartT z) r +
        (deriv period r * deriv (chartT z) r + period r * deriv (deriv (chartT z)) r)) r :=
    (((hp r hr).2.1.hasDerivAt.mul ht1).add
      ((hp r hr).1.hasDerivAt.mul ht2.hasDerivAt)).congr_of_eventuallyEq hen
  have hpn : period r ≠ 0 :=
    D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.period_ne_zero
      (by simpa [disk] using hr.1)
  have he : (fun w => w * (1 - w) * period w ^ 2 * deriv (chartT z) w) =ᶠ[𝓝 r]
      (fun _ => -Complex.I / (Real.pi : ℂ)) := by
    filter_upwards [(chart_open z).mem_nhds hr] with w hw
    have hw1 : 1 - w ≠ 0 := by
      intro h
      have : w = 1 := (sub_eq_zero.mp h).symm
      simpa [disk, this] using hw.1
    have hwp := D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.period_ne_zero
      (by simpa [disk] using hw.1)
    rw [(chartT_derivative hw).deriv]
    field_simp [chart_ne_zero hw, hw1, hwp]
  have ha : HasDerivAt (fun w : ℂ => w * (1 - w)) (1 - 2 * r) r := by
    convert (hasDerivAt_id r).mul ((hasDerivAt_id r).const_sub 1) using 1
    · rfl
    · dsimp
      ring
  have hk := (ha.mul ((hp r hr).1.hasDerivAt.pow 2)).mul ht2.hasDerivAt
  have hk0 := hk.unique ((hasDerivAt_const r (-Complex.I / (Real.pi : ℂ))).congr_of_eventuallyEq he)
  simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] at hk0
  refine ⟨chartT_derivative hr, hn2.differentiableAt, ?_, ?_⟩
  · rw [hn2.deriv, (hn r hr).deriv, chartN]
    apply mul_left_cancel₀ hpn
    linear_combination period r * chartT z r * (hp r hr).2.2 + hk0
  · rw [(hn r hr).deriv, chartN, (chartT_derivative hr).deriv]
    field_simp
    <;> ring

/-- Nearby lift parameters give identical holomorphic germs on their overlap. -/
theorem chart_transition (z w : ℂ) (hw : w ∈ E)
    (hzw : (w - z).im ∈ Ioo (-Real.pi) Real.pi) :
    localLog z =ᶠ[𝓝 (Complex.exp w)] localLog w ∧
    chartT z =ᶠ[𝓝 (Complex.exp w)] chartT w ∧
    chartN z =ᶠ[𝓝 (Complex.exp w)] chartN w := by
  have hm : {u : ℂ | (u - z).im ∈ Ioo (-Real.pi) Real.pi} ∈ 𝓝 w :=
    (isOpen_Ioo.preimage (by fun_prop : Continuous (fun u : ℂ => (u - z).im))).mem_nhds hzw
  have he : (fun u => localLog z (Complex.exp u)) =ᶠ[𝓝 w] (fun u => u) := by
    filter_upwards [hm] with u hu
    rw [localLog, ← Complex.exp_sub, Complex.log_exp hu.1 hu.2.le]
    ring
  have hc : Tendsto (localLog w) (𝓝 (Complex.exp w)) (𝓝 w) := by
    simpa only [localLog_exp] using
      (localLog_derivative (chart_self hw)).continuousAt.tendsto
  have hl : localLog z =ᶠ[𝓝 (Complex.exp w)] localLog w := by
    filter_upwards [he.comp_tendsto hc, (chart_open w).mem_nhds (chart_self hw)] with r hr hrD
    simpa only [Function.comp_def, exp_localLog hrD] using hr
  exact ⟨hl, hl.mono (fun r h => by simp only [chartT, h]),
    hl.mono (fun r h => by simp only [chartN, chartT, h])⟩

/-- The initial charts agree on neighborhoods with the actual native pair on
the entire lens, fixing both the additive and scalar normalizations. -/
theorem native_initial_germ (r : ℂ) (hr : r ∈ lens) :
    Complex.log r ∈ E ∧
    chartN (Complex.log r) =ᶠ[𝓝 r] (fun s => Complex.I * period (1 - s)) ∧
    chartT (Complex.log r) =ᶠ[𝓝 r] OriginalHalfBinomialWronskian.tau := by
  have hnorm : ‖r‖ < 1 ∧ ‖1 - r‖ < 1 := by
    simpa only [lens, mem_inter_iff, Metric.mem_ball, dist_zero_right,
      dist_eq_norm, sub_zero, norm_sub_rev] using hr
  have hs : r ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    have h := (Complex.re_le_norm (1 - r)).trans_lt hnorm.2
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith
  have hE : Complex.log r ∈ E := by
    change (Complex.log r).re < 0
    rw [Complex.log_re]
    exact Real.log_neg (norm_pos_iff.mpr (Complex.slitPlane_ne_zero hs)) hnorm.1
  have he := (localLog_left (Complex.log r)).comp_tendsto
    (Complex.hasDerivAt_log hs).continuousAt.tendsto
  have hl : localLog (Complex.log r) =ᶠ[𝓝 r] Complex.log := by
    filter_upwards [he, Complex.isOpen_slitPlane.mem_nhds hs] with s hh hs'
    simpa only [Function.comp_def, Complex.exp_log (Complex.slitPlane_ne_zero hs')] using hh
  have hL : lens ∈ 𝓝 r := (Metric.isOpen_ball.inter Metric.isOpen_ball).mem_nhds hr
  refine ⟨hE, ?_, ?_⟩
  · filter_upwards [hl, hL] with s hh hs'
    simpa only [chartN, chartT, hh, n0, t0] using continued_numerator.2.1 s hs'
  · filter_upwards [hl, hL] with s hh hs'
    simpa only [chartT, hh, t0] using actual_continuation.2 hs'

end D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
