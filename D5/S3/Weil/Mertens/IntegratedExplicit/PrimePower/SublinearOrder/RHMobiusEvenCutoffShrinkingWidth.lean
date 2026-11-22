/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffShrinkingWidth
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffShrinkingWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The centered root spectrum of shrinking logarithmic windows. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusEvenCutoff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! The centered zero series controls the normalized root increment on shrinking windows. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open Set Filter MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius Topology
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency frequency_real)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

/-- The centered real root series divided by the positive decay parameter. -/
def rootSignal (r u : ℝ) : ℝ :=
  (∑' k, rootCoeff r k * Complex.exp (frequency k / (r : ℂ) * (u : ℂ))).re /
    (1/2 - (2*r)⁻¹)

private theorem phase_uniformContinuous :
    UniformContinuous (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) := by
  apply LipschitzWith.uniformContinuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [show Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      (Complex.exp (Complex.I * ((x-y : ℝ) : ℂ)) - 1) * Complex.exp (Complex.I * (y : ℂ)) by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    push_cast
    ring_nf]
  rw [norm_mul, show ‖Complex.exp (Complex.I * (y : ℂ))‖ = 1 by
    simp [Complex.norm_exp, Complex.mul_re], mul_one]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem root_signal_uniformContinuous (hRH : RiemannHypothesis) {r : ℝ}
    (hr : 1 < r) : UniformContinuous (rootSignal r) := by
  let term (k : ℕ) (u : ℝ) := rootCoeff r k * Complex.exp (frequency k / (r : ℂ) * (u : ℂ))
  have mode_re (k : ℕ) : (frequency k / (r : ℂ)).re = 0 := by
    simp [Complex.div_re, frequency_real hRH k]
  have hterms (k : ℕ) : UniformContinuous (term k) := by
    let z := frequency k / (r : ℂ)
    have hz : z = (z.im : ℂ) * Complex.I := by
      simpa only [show z.re = 0 from mode_re k, Complex.ofReal_zero, zero_add] using
        (Complex.re_add_im z).symm
    have hrewrite : term k =
        fun u => rootCoeff r k * Complex.exp (Complex.I * ((z.im * u : ℝ) : ℂ)) := by
      funext u
      change rootCoeff r k * Complex.exp (z * (u : ℂ)) = _
      conv_lhs => rw [hz]
      push_cast
      ring_nf
    rw [hrewrite]
    exact (phase_uniformContinuous.comp (Real.uniformContinuous_const_mul (x := z.im))).const_mul' _
  have hnorm (k : ℕ) (u : ℝ) : ‖term k u‖ ≤ r * ‖actualCoeff k‖ := by
    simpa only [term, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mode_re, zero_mul, mul_zero, sub_zero, Real.exp_zero, mul_one] using
      rootCoeff_bound hr k
  have hlim := tendstoUniformly_tsum (actualCoeff_hasSum.summable.norm.mul_left r) hnorm
  have hfinite (indices : Finset ℕ) :
      UniformContinuous (fun u => ∑ k ∈ indices, term k u) := by
    induction indices using Finset.induction_on with
    | empty => simpa using (uniformContinuous_const : UniformContinuous fun _ : ℝ => (0 : ℂ))
    | insert k indices hk ih =>
      simpa only [Finset.sum_insert hk] using (hterms k).add ih
  have hsum := hlim.uniformContinuous (Eventually.of_forall hfinite).frequently
  exact (Complex.uniformContinuous_re.comp hsum).div_const' _

private theorem root_density_eq_signal {r : ℝ} (hr : 1 < r) (u : ℝ) :
    let s : ℝ := 1/2 - (2*r)⁻¹
    rootDensity r u = (s * Real.exp (-s*u)) * rootSignal r u := by
  let s : ℝ := 1/2 - (2*r)⁻¹
  have hr₀ : 0 < r := zero_lt_one.trans hr
  have hs : 0 < s := by
    dsimp only [s]
    rw [show (1 : ℝ)/2 = 2⁻¹ by norm_num]
    exact sub_pos.mpr (inv_strictAnti₀ (by norm_num) (by linarith))
  have hshift (k : ℕ) : rootExponent r k =
      -(s : ℂ) + frequency k / (r : ℂ) := by
    simp only [rootExponent, frequency, s]
    push_cast
    field_simp
    ring
  change rootDensity r u = (s * Real.exp (-s*u)) * rootSignal r u
  unfold rootDensity rootSignal
  change (∑' k, rootMode r u k).re =
    (s * Real.exp (-s*u)) * ((∑' k, rootCoeff r k *
      Complex.exp (frequency k / (r : ℂ) * (u : ℂ))).re / s)
  rw [show ∀ x : ℝ, s * Real.exp (-s*u) * (x / s) = Real.exp (-s*u) * x by
    intro x
    field_simp [hs.ne']]
  rw [← Complex.re_ofReal_mul, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  change rootCoeff r k * Complex.exp (rootExponent r k * (u : ℂ)) = _
  rw [hshift, add_mul, Complex.exp_add, Complex.ofReal_exp]
  push_cast
  ring

private theorem width_weight_integral {s L : ℝ} (hs : 0 < s) :
    (∫ t in (0 : ℝ)..L, Real.exp (-s*t)) = (1 - Real.exp (-s*L))/s := by
  have hneg : -s ≠ 0 := neg_ne_zero.mpr hs.ne'
  have h := intervalIntegral.integral_comp_mul_left Real.exp hneg (a := 0) (b := L)
  simpa [inv_mul_eq_div, div_neg, ← neg_div] using h

theorem root_increment_eq_weighted_average {r L : ℝ} (hr : 1 < r) (hL : 0 < L) (u : ℝ) :
    let s : ℝ := 1/2 - (2*r)⁻¹
    (rootPrimitive r (Real.exp (u+L)) - rootPrimitive r (Real.exp u)) /
      powerGap s (Real.exp u) (Real.exp (u+L)) =
    (∫ t in (0 : ℝ)..L, Real.exp (-s*t) * rootSignal r (u+t)) /
      (∫ t in (0 : ℝ)..L, Real.exp (-s*t)) := by
  let s : ℝ := 1/2 - (2*r)⁻¹
  have hs : 0 < s := by
    dsimp only [s]
    rw [show (1 : ℝ)/2 = 2⁻¹ by norm_num]
    exact sub_pos.mpr (inv_strictAnti₀ (by norm_num) (by linarith))
  have hpositive : 0 < 1 - Real.exp (-s*L) := by
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) hL)
  change (rootPrimitive r (Real.exp (u+L)) - rootPrimitive r (Real.exp u)) /
      powerGap s (Real.exp u) (Real.exp (u+L)) =
    (∫ t in (0 : ℝ)..L, Real.exp (-s*t) * rootSignal r (u+t)) /
      (∫ t in (0 : ℝ)..L, Real.exp (-s*t))
  rw [← (root_density_integral hr u (u+L)).2, exp_power_gap, width_weight_integral hs]
  have h := intervalIntegral.integral_comp_add_left (rootDensity r) (a := 0) (b := L) u
  rw [add_zero] at h
  rw [← h]
  have hsplit (t : ℝ) :
      s * Real.exp (-s*(u+t)) * rootSignal r (u+t) =
      (s * Real.exp (-s*u)) * (Real.exp (-s*t) * rootSignal r (u+t)) := by
    rw [show -s*(u+t) = -s*u + -s*t by ring, Real.exp_add]
    ring
  rw [show (∫ t in (0 : ℝ)..L, rootDensity r (u+t)) =
      (s * Real.exp (-s*u)) * (∫ t in (0 : ℝ)..L, Real.exp (-s*t) * rootSignal r (u+t)) by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    change rootDensity r (u+t) =
      (s * Real.exp (-s*u)) * (Real.exp (-s*t) * rootSignal r (u+t))
    exact (root_density_eq_signal hr (u+t)).trans (hsplit t)]
  field_simp [(Real.exp_pos (-s*u)).ne', hpositive.ne', hs.ne']

/-- A normalized positive-width root increment equals the centered signal at a window point. -/
theorem root_increment_eq_signal_at (hRH : RiemannHypothesis) {r L : ℝ}
    (hr : 1 < r) (hL : 0 < L) (u : ℝ) :
    let s : ℝ := 1/2 - (2*r)⁻¹
    ∃ t ∈ Icc 0 L,
      (rootPrimitive r (Real.exp (u+L)) - rootPrimitive r (Real.exp u)) /
        powerGap s (Real.exp u) (Real.exp (u+L)) = rootSignal r (u+t) := by
  let s : ℝ := 1/2 - (2*r)⁻¹
  have hs : 0 < s := by
    dsimp only [s]
    rw [show (1 : ℝ)/2 = 2⁻¹ by norm_num]
    exact sub_pos.mpr (inv_strictAnti₀ (by norm_num) (by linarith))
  let w (t : ℝ) := Real.exp (-s*t)
  let S (t : ℝ) := rootSignal r (u+t)
  have hw : Continuous w := by fun_prop
  have hS : Continuous S :=
    (root_signal_uniformContinuous hRH hr).continuous.comp (continuous_const.add continuous_id)
  let mass := ∫ t in (0 : ℝ)..L, w t
  have hmass : 0 < mass := by
    change 0 < ∫ t in (0 : ℝ)..L, Real.exp (-s*t)
    rw [width_weight_integral hs]
    exact div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr
      (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) hL))) hs
  have hwi : IntervalIntegrable w volume 0 L := hw.intervalIntegrable _ _
  obtain ⟨t, ht, hav⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    hS.continuousOn hwi
    (fun t _ => Real.exp_nonneg (-s*t))
  rw [uIcc_of_le hL.le] at ht
  refine ⟨t, ht, ?_⟩
  rw [root_increment_eq_weighted_average hr hL]
  change (∫ x in (0 : ℝ)..L, w x * S x) / mass = S t
  simp_rw [mul_comm (w _)]
  rw [hav]
  exact mul_div_cancel_right₀ _ hmass.ne'

private theorem root_increment_near_signal (hRH : RiemannHypothesis) {r : ℝ}
    (hr : 1 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ u L : ℝ, 0 < L → L < L₀ →
      let s : ℝ := 1/2 - (2*r)⁻¹
      |(rootPrimitive r (Real.exp (u+L)) - rootPrimitive r (Real.exp u)) /
        powerGap s (Real.exp u) (Real.exp (u+L)) - rootSignal r u| ≤ ε := by
  obtain ⟨L₀, hL₀, hmod⟩ := Metric.uniformContinuous_iff.mp
    (root_signal_uniformContinuous hRH hr) ε hε
  refine ⟨L₀, hL₀, fun u L hL hsmall => ?_⟩
  obtain ⟨t, ht, hmean⟩ := root_increment_eq_signal_at hRH hr hL u
  dsimp only
  rw [hmean]
  have hdist : dist (u+t) u < L₀ := by
    rw [Real.dist_eq, show u+t-u = t by ring, abs_of_nonneg ht.1]
    exact ht.2.trans_lt hsmall
  simpa only [Real.dist_eq] using (hmod hdist).le

/-- Shrinking logarithmic widths recover the centered root spectrum uniformly in the late start. -/
theorem signed_window_even_cutoff_shrinking_width (hRH : RiemannHypothesis) :
    ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ m r : ℕ, 2 ≤ m → m+1 = 2*r →
      let s := orderRate m
      let δ := ((m : ℝ)+1)⁻¹ - ((m : ℝ)+2)⁻¹
      let c := (μ (m+1) : ℝ) * (((m : ℝ)+1)/((m : ℝ)*s))
      let S := rootSignal (r : ℝ)
      (∀ u L : ℝ, 0 < L →
        (rootPrimitive (r : ℝ) (Real.exp (u+L)) - rootPrimitive (r : ℝ) (Real.exp u)) /
          powerGap s (Real.exp u) (Real.exp (u+L)) =
        (∫ t in (0 : ℝ)..L, Real.exp (-s*t) * S (u+t)) /
          (∫ t in (0 : ℝ)..L, Real.exp (-s*t))) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, 0 < L₀ ∧
        ∀ u L : ℝ, U₀ ≤ u → 0 < L → L < L₀ →
          |signedWindowResidual m (Real.exp u) (Real.exp (u+L)) /
            powerGap s (Real.exp u) (Real.exp (u+L)) + c + (μ r : ℝ) * S u| ≤
            ε + K * Real.exp (-δ*u) := by
  obtain ⟨a₀, K, ha₂, hK, hexpansion⟩ := signed_window_even_cutoff_expansion hRH
  have ha₀ : 0 < a₀ := by linarith
  refine ⟨Real.log a₀, Real.log_pos (by linarith), fun m r hm heven => ?_⟩
  let s := orderRate m
  let δ := ((m : ℝ)+1)⁻¹ - ((m : ℝ)+2)⁻¹
  let c := (μ (m+1) : ℝ) * (((m : ℝ)+1)/((m : ℝ)*s))
  let W := K * (((m+1 : ℕ) : ℝ) * (1 + Real.log ((m+1 : ℕ) : ℝ))^2)
  have hr : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hq : (m : ℝ)+1 = 2*(r : ℝ) := by exact_mod_cast heven
  have hs' : s = 1/2 - (2*(r : ℝ))⁻¹ := by dsimp [s, orderRate]; rw [hq]
  have hs : 0 < s := by
    rw [hs', show (1 : ℝ)/2 = 2⁻¹ by norm_num]
    exact sub_pos.mpr (inv_strictAnti₀ (by norm_num) (by linarith))
  have hδ : 0 < δ := sub_pos.mpr (inv_strictAnti₀ (by positivity) (by linarith))
  refine ⟨?_, W*((s+δ)/s), by dsimp only [W]; positivity, ?_⟩
  · intro u L hL
    simpa only [← hs'] using root_increment_eq_weighted_average hr hL u
  · intro ε hε
    let μr : ℝ := μ r
    have hμ : 0 < 1 + |μr| := by positivity
    obtain ⟨L₀, hL₀, hclose⟩ := root_increment_near_signal hRH hr
      (div_pos hε hμ)
    refine ⟨L₀, hL₀, fun u L hu hL hsmall => ?_⟩
    let a := Real.exp u
    let b := Real.exp (u+L)
    let P := rootPrimitive (r : ℝ) b - rootPrimitive (r : ℝ) a
    let gap := powerGap s a b
    have haus : a₀ ≤ a := by
      rw [← Real.exp_log ha₀]
      exact Real.exp_le_exp.mpr hu
    have hab : a < b := Real.exp_lt_exp.mpr (by linarith)
    have hg : 0 < gap :=
      sub_pos.mpr (Real.rpow_lt_rpow_of_neg (Real.exp_pos _) hab (neg_neg_of_pos hs))
    have hterm : |signedWindowResidual m a b + c*gap + μr*P| ≤
        (W*((s+δ)/s)) * Real.exp (-δ*u) * gap := by
      have h := hexpansion m r hm heven a b haus hab.le
      simpa only [s, δ, c, W, μr, P, gap, a, Real.rpow_def_of_pos (Real.exp_pos _),
        Real.log_exp, mul_comm u (-δ)] using h.1.trans h.2
    have hnorm : |signedWindowResidual m a b / gap + c + μr*(P/gap)| ≤
        (W*((s+δ)/s)) * Real.exp (-δ*u) := by
      rw [show signedWindowResidual m a b / gap + c + μr*(P/gap) =
          (signedWindowResidual m a b + c*gap + μr*P) / gap by field_simp [hg.ne'],
        abs_div, abs_of_pos hg, div_le_iff₀ hg]
      exact hterm
    have hP : |P/gap - rootSignal (r : ℝ) u| ≤ ε/(1+|μr|) := by
      simpa only [P, gap, a, b, ← hs'] using hclose u L hL hsmall
    have hε' : |μr| * (ε/(1+|μr|)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ hμ]
      nlinarith
    change |signedWindowResidual m a b / gap + c + μr*rootSignal (r : ℝ) u| ≤ _
    rw [show signedWindowResidual m a b / gap + c + μr*rootSignal (r : ℝ) u =
        (signedWindowResidual m a b / gap + c + μr*(P/gap)) -
          μr*(P/gap - rootSignal (r : ℝ) u) by ring]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    linarith only [hnorm, (mul_le_mul_of_nonneg_left hP (abs_nonneg μr)).trans hε']

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
