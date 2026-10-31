/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/RhPointwise
   generality: I
   mirror-B: none(waiver:source-only-implementation-not-frozen)
   mirror-E: none(waiver:source-only-implementation-not-frozen)
   anchors: []
   utility: none
   digest: Recover a pointwise Chebyshev estimate from the complete integrated formula under RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.WholeFormula
import D5.S3.Weil.Mertens.WeightedPrimeLimit
import D5.S3.Weil.ZetaBridge.RhLocatesZeroData
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Physical shrinking windows recover the actual error, using monotonicity
and the uniformly convergent complete zero series. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Asymptotics
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.WeightedPrimeLimit
open scoped Topology BigOperators

namespace D5.S3.Weil.Mertens.IntegratedExplicit

private lemma kernel_interval {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable psiErrorKernel volume a b := by
  apply IntegrableOn.intervalIntegrable
  apply chebyshev_error_kernel_integrable.mono_set
  intro u hu
  have hmin : (2 : ℝ) ≤ min a b := le_min ha hb
  exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (hmin.trans hu.1)

private lemma tail_difference {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (∫ u in a..b, psiErrorKernel u) = Q a - Q b := by
  have h := intervalIntegral.integral_interval_add_Ioi
    (chebyshev_error_kernel_integrable.mono_set
      (Ioi_subset_Ioi (by linarith : (1 : ℝ) ≤ a)))
    (chebyshev_error_kernel_integrable.mono_set
      (Ioi_subset_Ioi (by linarith : (1 : ℝ) ≤ b)))
  change (∫ u in a..b, psiErrorKernel u) + Q b = Q a at h
  linarith only [h]

/-- A physical right window bounds the upward error, including jump endpoints. -/
private lemma right_window {x d : ℝ} (hx : 2 ≤ x) (hd : 0 < d) :
    Chebyshev.psi x - x ≤ d + (x + d) ^ 2 / d * |Q x - Q (x + d)| := by
  have hx0 : 0 < x := by linarith
  have hb : 2 ≤ x + d := by linarith
  have hfac : 0 ≤ (x + d) ^ 2 / d := by positivity
  by_cases he : Chebyshev.psi x - x ≤ d
  · exact he.trans (le_add_of_nonneg_right (mul_nonneg hfac (abs_nonneg _)))
  have he0 : 0 ≤ Chebyshev.psi x - x - d := by linarith
  have hi := intervalIntegral.integral_mono_on (by linarith : x ≤ x + d)
    (intervalIntegrable_const (c := (Chebyshev.psi x - x - d) / (x + d) ^ 2))
    (kernel_interval hx hb) (fun u hu => show
      (Chebyshev.psi x - x - d) / (x + d) ^ 2 ≤ psiErrorKernel u from by
      have hu0 : 0 < u := hx0.trans_le hu.1
      have hmono := Chebyshev.psi_mono hu.1
      have herr : Chebyshev.psi x - x - d ≤ Chebyshev.psi u - u := by linarith [hu.2]
      dsimp only [psiErrorKernel]
      exact (div_le_div_of_nonneg_left he0 (sq_pos_of_pos hu0)
        (by nlinarith [hu.2] : u ^ 2 ≤ (x + d) ^ 2)).trans
        (div_le_div_of_nonneg_right herr (sq_nonneg u)))
  rw [intervalIntegral.integral_const, tail_difference hx hb] at hi
  simp only [add_sub_cancel_left, smul_eq_mul] at hi
  have h := hi.trans (le_abs_self _)
  have hden : (x + d) ^ 2 > 0 := sq_pos_of_pos (by linarith)
  have hm : d * (Chebyshev.psi x - x - d) ≤ |Q x - Q (x + d)| * (x + d) ^ 2 :=
    (div_le_iff₀ hden).mp (by simpa only [mul_div_assoc] using h)
  have hh := (le_div_iff₀ hd).mpr (by simpa only [mul_comm d] using hm)
  have hh' : Chebyshev.psi x - x - d ≤
      (x + d) ^ 2 / d * |Q x - Q (x + d)| := by
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  linarith only [hh']

/-- The left window controls the other sign with the same actual psi. -/
private lemma left_window {x d : ℝ} (hx : 2 ≤ x - d) (hd : 0 < d) :
    -(Chebyshev.psi x - x) ≤ d + x ^ 2 / d * |Q (x - d) - Q x| := by
  have hx0 : 0 < x := by linarith
  have hx' : 2 ≤ x := by linarith
  have hfac : 0 ≤ x ^ 2 / d := by positivity
  by_cases he : -(Chebyshev.psi x - x) ≤ d
  · exact he.trans (le_add_of_nonneg_right (mul_nonneg hfac (abs_nonneg _)))
  have he0 : 0 ≤ -(Chebyshev.psi x - x + d) := by linarith
  have hi := intervalIntegral.integral_mono_on (by linarith : x - d ≤ x)
    (kernel_interval hx hx')
    (intervalIntegrable_const (c := (Chebyshev.psi x - x + d) / x ^ 2))
    (fun u hu => show psiErrorKernel u ≤ (Chebyshev.psi x - x + d) / x ^ 2 from by
      have hu0 : 0 < u := by linarith [hu.1]
      have hmono := Chebyshev.psi_mono hu.2
      have herr : Chebyshev.psi u - u ≤ Chebyshev.psi x - x + d := by linarith [hu.1]
      have hdiv := div_le_div_of_nonneg_left he0 (sq_pos_of_pos hu0)
        (by nlinarith [hu.2] : u ^ 2 ≤ x ^ 2)
      dsimp only [psiErrorKernel]
      have hneg : (Chebyshev.psi x - x + d) / u ^ 2 ≤
          (Chebyshev.psi x - x + d) / x ^ 2 := by
        simpa only [neg_div, neg_le_neg_iff] using hdiv
      exact (div_le_div_of_nonneg_right herr (sq_nonneg u)).trans hneg)
  rw [intervalIntegral.integral_const, tail_difference hx hx'] at hi
  simp only [sub_sub_cancel, smul_eq_mul] at hi
  have h : -(d * ((Chebyshev.psi x - x + d) / x ^ 2)) ≤ |Q (x - d) - Q x| :=
    (neg_le_neg hi).trans (neg_le_abs _)
  have hden : 0 < x ^ 2 := sq_pos_of_pos hx0
  have hm : d * (-(Chebyshev.psi x - x + d)) ≤ |Q (x - d) - Q x| * x ^ 2 :=
    (div_le_iff₀ hden).mp (by simpa only [neg_mul_eq_mul_neg, neg_div, mul_div_assoc] using h)
  have hh := (le_div_iff₀ hd).mpr (by simpa only [mul_comm d] using hm)
  have hh' : -(Chebyshev.psi x - x + d) ≤ x ^ 2 / d * |Q (x - d) - Q x| := by
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  linarith only [hh']

private def rhOscillation (y : ℝ) : ℂ := (Real.exp (-y / 2) : ℂ) * actualH y

private lemma rh_oscillation_package (hRH : RiemannHypothesis) :
    UniformContinuous rhOscillation ∧ ∃ M : ℝ, ∀ y : ℝ, ‖rhOscillation y‖ ≤ M := by
  let f : ℕ → ℝ → ℂ := fun k y =>
    actualCoeff k * Complex.exp ((y * (actualZero k).im : ℝ) * Complex.I)
  have hnorm (k : ℕ) (y : ℝ) : ‖f k y‖ ≤ ‖actualCoeff k‖ := by
    dsimp only [f]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hid (y : ℝ) : rhOscillation y = ∑' k : ℕ, f k y := by
    dsimp only [rhOscillation, actualH]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    have hline : (actualZero k).re = 1 / 2 :=
      D5.S3.Weil.ZetaBridge.RhLocatesZeroData.zeroData_zero_on_critical_line_of_rh
        hRH actualData (actualOccurrenceEquiv k).1
    have he : ((-y / 2 : ℝ) : ℂ) + (y : ℂ) * actualZero k =
        (y * (actualZero k).im : ℝ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hline] <;> ring
    dsimp only [f]
    rw [Complex.ofReal_exp]
    calc
      Complex.exp ((-y / 2 : ℝ) : ℂ) *
          (actualCoeff k * Complex.exp ((y : ℂ) * actualZero k)) =
        actualCoeff k * Complex.exp (((-y / 2 : ℝ) : ℂ) + (y : ℂ) * actualZero k) := by
          rw [Complex.exp_add]; ring
      _ = _ := by rw [he]
  have huc (k : ℕ) : UniformContinuous (f k) := by
    have hu : UniformContinuous (fun y : ℝ => y * (actualZero k).im) :=
      uniformContinuous_id.mul_const' _
    have hc := Complex.ofRealCLM.uniformContinuous.comp
      (Real.lipschitzWith_cos.uniformContinuous.comp hu)
    have hs := Complex.ofRealCLM.uniformContinuous.comp
      (Real.lipschitzWith_sin.uniformContinuous.comp hu)
    simpa only [f, Complex.exp_ofReal_mul_I, Function.comp_def, Complex.ofRealCLM_apply] using
      (hc.add (hs.mul_const' Complex.I)).const_mul' (actualCoeff k)
  have heq : rhOscillation = fun y => ∑' k : ℕ, f k y := funext hid
  rw [heq]
  constructor
  · exact (tendstoUniformly_tsum actualCoeff_hasSum.summable.norm hnorm).uniformContinuous
      (Eventually.of_forall (fun s => s.uniformContinuous_sum (fun k _ => huc k))).frequently
  · exact ⟨∑' k : ℕ, ‖actualCoeff k‖, fun y =>
      tsum_of_norm_bounded actualCoeff_hasSum.summable.norm.hasSum (fun k => hnorm k y)⟩

private lemma normalized_tail_formula {x : ℝ} (hx : 2 ≤ x) :
    Real.sqrt x * Q x + (rhOscillation (Real.log x)).re =
      (trivialT (Real.log x) - Real.log (2 * Real.pi)) / Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  have hroot : Real.exp (Real.log x / 2) = Real.sqrt x := by
    have he : Real.exp (Real.log x / 2) ^ 2 = x := by
      rw [← Real.exp_nat_mul]
      convert Real.exp_log hx0 using 2 <;> ring
    nlinarith [Real.sq_sqrt hx0.le, Real.exp_pos (Real.log x / 2), Real.sqrt_nonneg x]
  have hscale : Real.exp (-Real.log x / 2) = (Real.sqrt x)⁻¹ := by
    rw [show -Real.log x / 2 = -(Real.log x / 2) by ring, Real.exp_neg, hroot]
  have hf := congrArg Complex.re
    (actual_integrated_explicit_formula (Real.log_pos (by linarith : 1 < x)))
  rw [Real.exp_log hx0] at hf
  simp only [Complex.ofReal_re] at hf
  have hQ := CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
    chebyshev_error_kernel_integrable hx
  change Q x = _ at hQ
  have hqu : x * Q x = -U x := by
    rw [hQ]
    dsimp only [U]
    field_simp [hx0.ne']
    <;> ring
  dsimp only [rhOscillation]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hscale]
  apply (eq_div_iff hs0).mpr
  field_simp [hs0]
  rw [Real.sq_sqrt hx0.le, hqu, hf]
  ring

private lemma normalized_tail_remainder :
    Tendsto (fun x : ℝ => Real.sqrt x * Q x + (rhOscillation (Real.log x)).re)
      atTop (𝓝 0) := by
  have hO : (fun x : ℝ => trivialT (Real.log x) - Real.log (2 * Real.pi))
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    apply IsBigO.of_bound (|1 - Real.log 2| + |Real.log (2 * Real.pi)|)
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    rw [Real.norm_eq_abs, norm_one, mul_one]
    calc
      _ ≤ |trivialT (Real.log x)| + |Real.log (2 * Real.pi)| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (trivialT_nonneg hl)]
        linarith [(trivialT_le_mass hl).trans (le_abs_self (1 - Real.log 2))]
  have hi : Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have h := (hO.mul (isBigO_refl (fun x : ℝ => (Real.sqrt x)⁻¹) atTop)).trans_tendsto
    (by simpa only [one_mul, Pi.mul_apply] using hi)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  simpa only [div_eq_mul_inv] using (normalized_tail_formula hx).symm

/-- Uniform continuity is used between two moving log endpoints, rather than
replaced by continuity at a single fixed endpoint. -/
private lemma oscillation_moving_difference (hRH : RiemannHypothesis)
    {v : ℝ → ℝ} (hv : Tendsto (fun x : ℝ => v x / x) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ =>
      (rhOscillation (Real.log (v x))).re - (rhOscillation (Real.log x)).re)
      atTop (𝓝 0) := by
  have hl : Tendsto (fun x : ℝ => Real.log (v x / x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hv
  have hvpos : ∀ᶠ x : ℝ in atTop, 0 < v x / x := hv.eventually (lt_mem_nhds zero_lt_one)
  have hlog : Tendsto (fun x : ℝ => Real.log (v x) - Real.log x) atTop (𝓝 0) := by
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ), hvpos] with x hx hvx
    have hvx0 : 0 < v x := (div_pos_iff_of_pos_right hx).mp hvx
    exact Real.log_div hvx0.ne' hx.ne'
  have hpair : Tendsto (fun x : ℝ => (Real.log (v x), Real.log x)) atTop (uniformity ℝ) := by
    apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq, abs_zero] using hlog.abs
  have huc := Complex.uniformContinuous_re.comp (rh_oscillation_package hRH).1
  have huc' : Tendsto (fun p : ℝ × ℝ =>
      ((rhOscillation p.1).re, (rhOscillation p.2).re)) (uniformity ℝ) (uniformity ℝ) := huc
  have hout := tendsto_uniformity_iff_dist_tendsto_zero.mp (huc'.comp hpair)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  simpa only [Real.dist_eq, Function.comp_def] using hout

private lemma tail_slow_variation (hRH : RiemannHypothesis) {v : ℝ → ℝ}
    (hvtop : Tendsto v atTop atTop)
    (hv : Tendsto (fun x : ℝ => v x / x) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => Real.sqrt x * (Q x - Q (v x))) atTop (𝓝 0) := by
  have hv0 := hvtop.eventually_gt_atTop 0
  have hx0 := eventually_gt_atTop (0 : ℝ)
  have hk : Tendsto (fun x : ℝ => Real.sqrt x / Real.sqrt (v x)) atTop (𝓝 1) := by
    have hs : Tendsto (fun x : ℝ => Real.sqrt (v x / x)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, Real.sqrt_one] using Real.continuous_sqrt.tendsto 1 |>.comp hv
    have hi := hs.inv₀ one_ne_zero
    simp only [inv_one] at hi
    apply hi.congr'
    filter_upwards [hv0] with x hvx
    rw [Real.sqrt_div hvx.le, inv_div]
  let H : ℝ → ℝ := fun x => (rhOscillation (Real.log (v x))).re
  have hH : IsBoundedUnder (· ≤ ·) atTop (norm ∘ H) := by
    obtain ⟨M, hM⟩ := (rh_oscillation_package hRH).2
    exact isBoundedUnder_of ⟨M, fun x =>
      (RCLike.norm_re_le_norm _).trans (hM (Real.log (v x)))⟩
  have hsmall := NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
    (by simpa only [sub_self] using hk.sub (tendsto_const_nhds (x := (1 : ℝ)))) hH
  have hright := hk.mul (normalized_tail_remainder.comp hvtop)
  have hdiff := oscillation_moving_difference hRH hv
  have ht := ((normalized_tail_remainder.sub hright).add hdiff).add hsmall
  simp only [mul_zero, sub_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [hv0] with x hvx
  dsimp only [Function.comp_def, H, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  field_simp [(Real.sqrt_pos.mpr hvx).ne']
  <;> ring

private lemma shift_ratio (s : ℝ) :
    Tendsto (fun x : ℝ => (x + s * x ^ (3 / 4 : ℝ)) / x) atTop (𝓝 1) := by
  have hp := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add (hp.const_mul s)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have he : x ^ (-(1 / 4 : ℝ)) = x ^ (3 / 4 : ℝ) / x := by
    rw [show -(1 / 4 : ℝ) = 3 / 4 - 1 by norm_num, Real.rpow_sub hx, Real.rpow_one]
  rw [he]
  field_simp

private lemma shift_atTop (s : ℝ) :
    Tendsto (fun x : ℝ => x + s * x ^ (3 / 4 : ℝ)) atTop atTop := by
  have h := tendsto_id.atTop_mul_pos zero_lt_one (shift_ratio s)
  apply h.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  field_simp
  rfl

private lemma scale_identity {x : ℝ} (hx : 0 < x) :
    (x ^ (3 / 4 : ℝ)) ^ 2 * Real.sqrt x = x ^ 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le,
    ← Real.rpow_add hx]
  norm_num

/-- RH alone gives the literal actual pointwise little-o estimate. The live
Tauberian step compares both physical windows of length c*x^(3/4), for each
fixed positive c, before letting c tend to zero. -/
theorem chebyshev_error_isLittleO_rpow_three_quarters (hRH : RiemannHypothesis) :
    (fun x : ℝ => Chebyshev.psi x - x) =o[atTop] (fun x : ℝ => x ^ (3 / 4 : ℝ)) := by
  apply IsLittleO.of_bound
  intro ε hε
  let c : ℝ := ε / 2
  have hc : 0 < c := half_pos hε
  have hplus := tail_slow_variation hRH (shift_atTop c) (shift_ratio c)
  have hminus := tail_slow_variation hRH (shift_atTop (-c)) (shift_ratio (-c))
  have hpabs : Tendsto (fun x : ℝ => Real.sqrt x *
      |Q x - Q (x + c * x ^ (3 / 4 : ℝ))|) atTop (𝓝 0) := by
    simpa only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_zero] using hplus.abs
  have hmabs : Tendsto (fun x : ℝ => Real.sqrt x *
      |Q (x - c * x ^ (3 / 4 : ℝ)) - Q x|) atTop (𝓝 0) := by
    simpa only [neg_mul, ← sub_eq_add_neg, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_zero, abs_sub_comm] using hminus.abs
  have hquarter := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have hfactor : Tendsto (fun x : ℝ => (1 + c * x ^ (-(1 / 4 : ℝ))) ^ 2 / c)
      atTop (𝓝 (1 / c)) := by
    simpa only [mul_zero, add_zero, one_pow] using
      (((tendsto_const_nhds (x := (1 : ℝ))).add (hquarter.const_mul c)).pow 2).div_const c
  have hright : Tendsto (fun x : ℝ => (1 + c * x ^ (-(1 / 4 : ℝ))) ^ 2 / c *
      (Real.sqrt x * |Q x - Q (x + c * x ^ (3 / 4 : ℝ))|)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hfactor.mul hpabs
  have hleft : Tendsto (fun x : ℝ => Real.sqrt x *
      |Q (x - c * x ^ (3 / 4 : ℝ)) - Q x| / c) atTop (𝓝 0) := by
    simpa only [zero_div] using hmabs.div_const c
  have hleft_endpoint : ∀ᶠ x : ℝ in atTop, 2 ≤ x - c * x ^ (3 / 4 : ℝ) := by
    simpa only [neg_mul, ← sub_eq_add_neg] using (shift_atTop (-c)).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop (2 : ℝ), hleft_endpoint,
    hright.eventually (gt_mem_nhds (half_pos hε)),
    hleft.eventually (gt_mem_nhds (half_pos hε))] with x hx hxm hpr hml
  have hx0 : 0 < x := by linarith
  have hp : 0 < x ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hd : 0 < c * x ^ (3 / 4 : ℝ) := mul_pos hc hp
  have hupper := right_window hx hd
  have hlower := left_window hxm hd
  have hq : x ^ (-(1 / 4 : ℝ)) = x ^ (3 / 4 : ℝ) / x := by
    rw [show -(1 / 4 : ℝ) = 3 / 4 - 1 by norm_num, Real.rpow_sub hx0, Real.rpow_one]
  have hs : Real.sqrt x = x ^ 2 / (x ^ (3 / 4 : ℝ)) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hp.ne')).mpr
    simpa only [mul_comm] using scale_identity hx0
  have hcoeffR :
      ((1 + c * x ^ (-(1 / 4 : ℝ))) ^ 2 / c *
        (Real.sqrt x * |Q x - Q (x + c * x ^ (3 / 4 : ℝ))|)) * x ^ (3 / 4 : ℝ) =
      (x + c * x ^ (3 / 4 : ℝ)) ^ 2 / (c * x ^ (3 / 4 : ℝ)) *
        |Q x - Q (x + c * x ^ (3 / 4 : ℝ))| := by
    rw [hq, hs]
    field_simp [hx0.ne', hc.ne', hp.ne']
    <;> ring
  have hcoeffL :
      (Real.sqrt x * |Q (x - c * x ^ (3 / 4 : ℝ)) - Q x| / c) * x ^ (3 / 4 : ℝ) =
      x ^ 2 / (c * x ^ (3 / 4 : ℝ)) * |Q (x - c * x ^ (3 / 4 : ℝ)) - Q x| := by
    rw [hs]
    field_simp [hc.ne', hp.ne']
    <;> ring
  have hR := mul_lt_mul_of_pos_right hpr hp
  have hL := mul_lt_mul_of_pos_right hml hp
  rw [hcoeffR] at hR
  rw [hcoeffL] at hL
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp]
  apply abs_le.mpr
  dsimp only [c] at hupper hlower
  constructor <;> linarith only [hupper, hlower, hR, hL]

#print axioms chebyshev_error_isLittleO_rpow_three_quarters

end D5.S3.Weil.Mertens.IntegratedExplicit
