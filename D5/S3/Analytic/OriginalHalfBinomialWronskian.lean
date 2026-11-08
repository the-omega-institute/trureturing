/- GID: D5/S3/Analytic/OriginalHalfBinomialWronskian
   generality: I
   mirror-B: D5/B/S3/Analytic/OriginalHalfBinomialWronskian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.LHopital, mathlib/module/Mathlib.Analysis.Calculus.MeanValue]
   utility: none
   digest: Complementary Wronskian and period-ratio derivative of the original period on the lens. -/

import D5.S3.Analytic.OriginalHalfBinomialEndpoint
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! Native complementary-period calculation for the literal half-binomial-square
series.  The ODE, real integral, logarithmic endpoint and disk nonvanishing are
the imported results used by the proof.  The complementary Wronskian inference
and its quotient derivative are proved here on the intersection of the two open
unit disks.  No continuation, source covariance, Q/C-flow binding, or full
scientific completion is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped Topology
open Set Filter

namespace D5.S3.Analytic.OriginalHalfBinomialWronskian

open OriginalHalfBinomialPeriod (period)

private def lens : Set ℂ := Metric.ball 0 1 ∩ Metric.ball 1 1

private lemma mem_lens (x : ℂ) :
    x ∈ lens ↔ ‖x‖ < 1 ∧ ‖1 - x‖ < 1 := by
  simp only [lens, mem_inter_iff, Metric.mem_ball, dist_zero_right]
  rw [dist_comm x (1 : ℂ), dist_eq_norm]

private def wronskian (x : ℂ) : ℂ :=
  x * (1 - x) *
    (deriv period x * period (1 - x) + period x * deriv period (1 - x))

/- Abel's calculation uses BOTH native differentiability conclusions.  In
   particular, no differentiability of a derivative is silently inferred. -/
private lemma wronskian_hasDerivAt_zero {x : ℂ}
    (hx : ‖x‖ < 1) (hc : ‖1 - x‖ < 1) :
    HasDerivAt wronskian 0 x := by
  obtain ⟨hf, hfp, he⟩ := OriginalHalfBinomialPeriod.picard_fuchs hx
  obtain ⟨hg, hgp, hec⟩ := OriginalHalfBinomialPeriod.picard_fuchs hc
  have hs := (hasDerivAt_id x).const_sub 1
  have hd := ((hasDerivAt_id x).mul hs).mul
    ((hfp.hasDerivAt.mul (hg.hasDerivAt.comp x hs)).add
      (hf.hasDerivAt.mul (hgp.hasDerivAt.comp x hs)))
  convert hd using 1 <;> dsimp [wronskian]
  · rfl
  · ring_nf at he hec ⊢
    linear_combination -(period (1 - x)) * he + period x * hec

private lemma wronskian_eq {x y : ℂ} (hx : x ∈ lens) (hy : y ∈ lens) :
    wronskian x = wronskian y := by
  have ho : IsOpen lens := Metric.isOpen_ball.inter Metric.isOpen_ball
  have hv : Convex ℝ lens := (convex_ball (0 : ℂ) (1 : ℝ)).inter (convex_ball 1 1)
  apply ho.is_const_of_deriv_eq_zero hv.isPreconnected _ _ hx hy
  · intro z hz
    obtain ⟨hz, hcz⟩ := (mem_lens z).mp hz
    exact (wronskian_hasDerivAt_zero hz hcz).differentiableAt.differentiableWithinAt
  · intro z hz
    obtain ⟨hz, hcz⟩ := (mem_lens z).mp hz
    exact (wronskian_hasDerivAt_zero hz hcz).deriv

private def realPeriod (r : ℝ) : ℝ := (period (r : ℂ)).re
private def realPrime (r : ℝ) : ℝ := (deriv period (r : ℂ)).re

private lemma real_norm_lt_one {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ‖(r : ℂ)‖ < 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] using hr1

/- Reality is obtained from the ORIGINAL integral, without changing the series. -/
private lemma period_ofReal {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    period (r : ℂ) = (realPeriod r : ℂ) := by
  have hi := (OriginalHalfBinomialIntegral.original_series_eq_integral r hr hr1).2.2
  change period (r : ℂ) = _ at hi
  simp only [realPeriod, hi, Complex.ofReal_re]

private lemma realPeriod_hasDerivAt {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    HasDerivAt realPeriod (realPrime r) r := by
  exact (OriginalHalfBinomialPeriod.picard_fuchs
    (real_norm_lt_one hr hr1)).1.hasDerivAt.real_of_complex

private lemma prime_ofReal {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    deriv period (r : ℂ) = (realPrime r : ℂ) := by
  have hd := (OriginalHalfBinomialPeriod.picard_fuchs
    (real_norm_lt_one hr.le hr1)).1.hasDerivAt
  have he : (fun t : ℝ => (realPeriod t : ℂ)) =ᶠ[𝓝 r]
      (fun t : ℝ => period (t : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show r ∈ Ioo (0 : ℝ) 1 from ⟨hr, hr1⟩)]
      with t ht
    exact (period_ofReal ht.1.le ht.2).symm
  exact hd.comp_ofReal.unique
    (he.hasDerivAt_iff.mp (realPeriod_hasDerivAt hr.le hr1).ofReal_comp)

private lemma realPeriod_ne_zero {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    realPeriod r ≠ 0 := by
  intro hz
  have hn := D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.period_ne_zero
    (real_norm_lt_one hr hr1)
  apply hn
  rw [period_ofReal hr hr1, hz, Complex.ofReal_zero]

private def abelConstant : ℝ := (wronskian (1 / 2 : ℂ)).re

private lemma midpoint_wronskian_real :
    wronskian (1 / 2 : ℂ) = (abelConstant : ℂ) := by
  have h0 := period_ofReal (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have h1 := prime_ofReal (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  push_cast at h0 h1
  have hm : 1 - (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
  have him : (wronskian (1 / 2 : ℂ)).im = 0 := by
    norm_num [wronskian, hm, h0, h1]
  apply Complex.ext
  · rfl
  · simpa using him

private lemma wronskian_eq_constant {x : ℂ} (hx : ‖x‖ < 1) (hc : ‖1 - x‖ < 1) :
    wronskian x = (abelConstant : ℂ) := by
  have hm : (1 / 2 : ℂ) ∈ lens := by
    apply (mem_lens _).mpr
    norm_num
  exact (wronskian_eq ((mem_lens x).mpr ⟨hx, hc⟩) hm).trans midpoint_wronskian_real

private lemma real_wronskian {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    r * (1 - r) *
      (realPrime r * realPeriod (1 - r) + realPeriod r * realPrime (1 - r)) =
        abelConstant := by
  have hcr : 0 < 1 - r := by linarith
  have hcr1 : 1 - r < 1 := by linarith
  have hc : 1 - (r : ℂ) = ((1 - r : ℝ) : ℂ) := by push_cast; rfl
  have hw := wronskian_eq_constant (real_norm_lt_one hr.le hr1)
    (by rw [hc]; exact real_norm_lt_one hcr.le hcr1)
  have he : wronskian (r : ℂ) =
      ((r * (1 - r) *
        (realPrime r * realPeriod (1 - r) + realPeriod r * realPrime (1 - r)) : ℝ) : ℂ) := by
    simp only [wronskian, hc, period_ofReal hr.le hr1, period_ofReal hcr.le hcr1,
      prime_ofReal hr hr1, prime_ofReal hcr hcr1]
    push_cast <;> rfl
  exact Complex.ofReal_injective (he.symm.trans hw)

private lemma real_ratio_hasDerivAt {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun t : ℝ => realPeriod t / realPeriod (1 - t))
      (abelConstant / (r * (1 - r) * realPeriod (1 - r) ^ 2)) r := by
  have hcr : 0 < 1 - r := by linarith
  have hcr1 : 1 - r < 1 := by linarith
  have hg : HasDerivAt (fun t : ℝ => realPeriod (1 - t)) (-realPrime (1 - r)) r := by
    convert (realPeriod_hasDerivAt hcr.le hcr1).comp r
      ((hasDerivAt_id r).const_sub 1) using 1
    · funext t
      rfl
    · ring
  have hd := (realPeriod_hasDerivAt hr.le hr1).div hg
    (realPeriod_ne_zero hcr.le hcr1)
  convert hd using 1
  rw [← real_wronskian hr hr1]
  field_simp [ne_of_gt hr, ne_of_gt hcr, realPeriod_ne_zero hcr.le hcr1]
  <;> ring

private lemma eventually_real_interval : ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ Ioo (0 : ℝ) 1 := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with r hr hr1
  exact ⟨hr, hr1⟩

private lemma realPeriod_tendsto_one :
    Tendsto realPeriod (𝓝[>] 0) (𝓝 1) := by
  have hi := (OriginalHalfBinomialIntegral.original_series_eq_integral 0
    (by norm_num) (by norm_num)).2.2
  change period (0 : ℂ) = _ at hi
  simp only [zero_mul, sub_zero, Real.sqrt_one, div_one] at hi
  rw [intervalIntegral.integral_const] at hi
  simp only [sub_zero, smul_eq_mul, mul_one] at hi
  have hn : (2 / Real.pi) * (Real.pi / 2) = (1 : ℝ) := by
    field_simp [Real.pi_ne_zero] <;> ring
  have hzero : realPeriod 0 = 1 := by
    have h := congrArg Complex.re hi
    norm_num [realPeriod, hn] at h ⊢
    exact h
  have hd := realPeriod_hasDerivAt (r := 0) (by norm_num) (by norm_num)
  have ht : Tendsto realPeriod (𝓝[>] 0) (𝓝 (realPeriod 0)) :=
    hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rwa [hzero] at ht

/- Divide the native log16 remainder by log r.  This is a consequence of that
   exact endpoint, not an assumed logarithmic coefficient. -/
private lemma complementary_over_log :
    Tendsto (fun r : ℝ => realPeriod (1 - r) / Real.log r)
      (𝓝[>] 0) (𝓝 (-1 / Real.pi)) := by
  have hi : Tendsto (fun r : ℝ => (Real.log r)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
  have he := OriginalHalfBinomialEndpoint.original_period_log16.mul hi
  have ht := (he.sub (tendsto_const_nhds (x := (1 : ℝ)))).div_const Real.pi
  simp only [mul_zero, zero_sub] at ht
  apply ht.congr'
  filter_upwards [eventually_real_interval] with r hr
  change ((Real.pi * realPeriod (1 - r) + Real.log r) * (Real.log r)⁻¹ - 1) /
    Real.pi = realPeriod (1 - r) / Real.log r
  field_simp [Real.pi_ne_zero, ne_of_lt (Real.log_neg hr.1 hr.2)]
  <;> ring

/- The two reciprocal zero/zero forms avoid any unproved derivative asymptotic.
   The L'Hopital conclusion and the actual quotient have the same left-hand
   side; uniqueness determines the Abel constant, including its sign. -/
private lemma abelConstant_eq : abelConstant = 1 / Real.pi := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hlim : (-1 / Real.pi : ℝ) ≠ 0 := div_ne_zero (by norm_num) hpi
  have ht : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hi : Tendsto (fun r : ℝ => (Real.log r)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
  have hglog := complementary_over_log
  have hginv : Tendsto (fun r : ℝ => (realPeriod (1 - r))⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
    have h := hi.div hglog hlim
    simp only [zero_div] at h
    apply h.congr'
    filter_upwards [eventually_real_interval] with r hr
    change (Real.log r)⁻¹ / (realPeriod (1 - r) / Real.log r) =
      (realPeriod (1 - r))⁻¹
    have hg0 := realPeriod_ne_zero (r := 1 - r) (by linarith [hr.2]) (by linarith [hr.1])
    field_simp [hg0, ne_of_lt (Real.log_neg hr.1 hr.2)]
  have hq : Tendsto (fun r : ℝ => realPeriod r / realPeriod (1 - r))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul] using realPeriod_tendsto_one.mul hginv
  have hactual : Tendsto
      (fun r : ℝ => (realPeriod r / realPeriod (1 - r)) / (Real.log r)⁻¹)
      (𝓝[>] 0) (𝓝 (-Real.pi)) := by
    have h := realPeriod_tendsto_one.div hglog hlim
    have hc : (1 : ℝ) / (-1 / Real.pi) = -Real.pi := by field_simp [hpi] <;> ring
    rw [hc] at h
    apply h.congr'
    filter_upwards [eventually_real_interval] with r hr
    change realPeriod r / (realPeriod (1 - r) / Real.log r) =
      (realPeriod r / realPeriod (1 - r)) / (Real.log r)⁻¹
    have hg0 := realPeriod_ne_zero (r := 1 - r) (by linarith [hr.2]) (by linarith [hr.1])
    field_simp [hg0, ne_of_lt (Real.log_neg hr.1 hr.2)]
  have hden : Tendsto
      (fun r : ℝ => (1 - r) * (realPeriod (1 - r) / Real.log r) ^ 2)
      (𝓝[>] 0) (𝓝 ((-1 / Real.pi) ^ 2)) := by
    convert ((tendsto_const_nhds (x := (1 : ℝ))).sub ht).mul (hglog.pow 2)
      using 1 <;> norm_num
  have hdlim : Tendsto
      (fun r : ℝ => (abelConstant / (r * (1 - r) * realPeriod (1 - r) ^ 2)) /
        (-1 / (r * Real.log r ^ 2)))
      (𝓝[>] 0) (𝓝 (-abelConstant * Real.pi ^ 2)) := by
    have h := (tendsto_const_nhds (x := -abelConstant)).div hden (pow_ne_zero 2 hlim)
    have hc : -abelConstant / (-1 / Real.pi) ^ 2 = -abelConstant * Real.pi ^ 2 := by
      field_simp [hpi]
      <;> ring
    rw [hc] at h
    apply h.congr'
    filter_upwards [eventually_real_interval] with r hr
    change -abelConstant / ((1 - r) * (realPeriod (1 - r) / Real.log r) ^ 2) =
      (abelConstant / (r * (1 - r) * realPeriod (1 - r) ^ 2)) /
        (-1 / (r * Real.log r ^ 2))
    have hg0 := realPeriod_ne_zero (r := 1 - r) (by linarith [hr.2]) (by linarith [hr.1])
    field_simp [ne_of_gt hr.1, ne_of_gt (show 0 < 1 - r by linarith [hr.2]),
      hg0, ne_of_lt (Real.log_neg hr.1 hr.2)]
  have hdh (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => (Real.log t)⁻¹) (-1 / (r * Real.log r ^ 2)) r := by
    convert (Real.hasDerivAt_log (ne_of_gt hr.1)).inv
      (ne_of_lt (Real.log_neg hr.1 hr.2)) using 1 <;>
      field_simp [ne_of_gt hr.1, ne_of_lt (Real.log_neg hr.1 hr.2)] <;> ring
  have hdh0 (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      (-1 / (r * Real.log r ^ 2) : ℝ) ≠ 0 :=
    div_ne_zero (by norm_num)
      (mul_ne_zero (ne_of_gt hr.1) (pow_ne_zero 2 (ne_of_lt (Real.log_neg hr.1 hr.2))))
  have hlhop := HasDerivAt.lhopital_zero_right_on_Ioo (a := (0 : ℝ)) (b := 1)
    (by norm_num) (fun r hr => real_ratio_hasDerivAt hr.1 hr.2) hdh hdh0 hq hi hdlim
  have heq : -Real.pi = -abelConstant * Real.pi ^ 2 := tendsto_nhds_unique hactual hlhop
  apply (eq_div_iff hpi).mpr
  have hm : (abelConstant * Real.pi) * Real.pi = 1 * Real.pi := by nlinarith [heq]
  exact mul_right_cancel₀ hpi hm

/-- The exact complementary Wronskian of the ORIGINAL series, on the open lens.
The value is inferred from the native ODE and native log16 endpoint. -/
theorem original_wronskian {x : ℂ} (hx : ‖x‖ < 1) (hc : ‖1 - x‖ < 1) :
    x * (1 - x) *
      (deriv period x * period (1 - x) + period x * deriv period (1 - x)) =
        1 / (Real.pi : ℂ) := by
  have h := wronskian_eq_constant hx hc
  rw [abelConstant_eq] at h
  simpa only [wronskian, Complex.ofReal_div, Complex.ofReal_one] using h

/-- The actual original complementary period ratio. -/
def tau (x : ℂ) : ℂ := Complex.I * period (1 - x) / period x

/-- Both the actual denominator's nonvanishing and the exact derivative of the
original ratio.  The hypotheses assert only membership in the open lens. -/
theorem original_tau_hasDerivAt {x : ℂ} (hx : ‖x‖ < 1) (hc : ‖1 - x‖ < 1) :
    (Real.pi : ℂ) * x * (1 - x) * period x ^ 2 ≠ 0 ∧
      HasDerivAt tau
        (-Complex.I / ((Real.pi : ℂ) * x * (1 - x) * period x ^ 2)) x := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hx0 : x ≠ 0 := by
    intro hz
    simp only [hz, sub_zero, norm_one, lt_self_iff_false] at hc
  have hc0 : 1 - x ≠ 0 := by
    intro hz
    have hx1 : x = 1 := by linear_combination -hz
    simp only [hx1, norm_one, lt_self_iff_false] at hx
  have hf0 := D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.period_ne_zero hx
  refine ⟨mul_ne_zero (mul_ne_zero (mul_ne_zero hpi hx0) hc0) (pow_ne_zero 2 hf0), ?_⟩
  have hf := (OriginalHalfBinomialPeriod.picard_fuchs hx).1.hasDerivAt
  have hg : HasDerivAt (fun z : ℂ => period (1 - z)) (-deriv period (1 - x)) x := by
    convert (OriginalHalfBinomialPeriod.picard_fuchs hc).1.hasDerivAt.comp x
      ((hasDerivAt_id x).const_sub 1) using 1
    · funext z
      rfl
    · ring
  have hd := (hg.const_mul Complex.I).div hf hf0
  have hw := original_wronskian hx hc
  have hw' : (Real.pi : ℂ) * x * (1 - x) *
      (deriv period x * period (1 - x) + period x * deriv period (1 - x)) = 1 := by
    calc
      _ = (Real.pi : ℂ) * (x * (1 - x) *
        (deriv period x * period (1 - x) + period x * deriv period (1 - x))) := by ring
      _ = (Real.pi : ℂ) * (1 / (Real.pi : ℂ)) := by rw [hw]
      _ = 1 := by field_simp [hpi]
  have hden : (Real.pi : ℂ) * x * (1 - x) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hpi hx0) hc0
  have hsum : deriv period x * period (1 - x) + period x * deriv period (1 - x) =
      1 / ((Real.pi : ℂ) * x * (1 - x)) := by
    apply (eq_div_iff hden).2
    calc
      (deriv period x * period (1 - x) + period x * deriv period (1 - x)) *
          ((Real.pi : ℂ) * x * (1 - x)) =
        (Real.pi : ℂ) * x * (1 - x) *
          (deriv period x * period (1 - x) + period x * deriv period (1 - x)) := by ring
      _ = 1 := hw'
  convert hd using 1
  · rfl
  · calc
      -Complex.I / ((Real.pi : ℂ) * x * (1 - x) * period x ^ 2) =
        -Complex.I *
          (deriv period x * period (1 - x) + period x * deriv period (1 - x)) /
            period x ^ 2 := by
        rw [hsum]
        field_simp [hden, hf0]
      _ = (Complex.I * -deriv period (1 - x) * period x -
          Complex.I * period (1 - x) * deriv period x) / period x ^ 2 := by ring

end D5.S3.Analytic.OriginalHalfBinomialWronskian
