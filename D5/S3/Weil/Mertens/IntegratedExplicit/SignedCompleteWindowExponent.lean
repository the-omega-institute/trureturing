/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/SignedCompleteWindowExponent
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/SignedCompleteWindowExponent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both signed complete Chebyshev power-window masses have exact logarithmic growth exponent. -/

import D5.S3.Arith.Robin.ForwardKernel.KappaGap
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth
import D5.S3.Weil.Mertens.ZeroAbscissaPower

/-! Both signed power-window masses of the complete Mangoldt ramp measure the
supremum of the real parts of the nontrivial zeta zeros. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.SignedCompleteWindowExponent

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap
  (zeroAbscissa zero_real_parts_nonempty zero_re_le_abscissa)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
  (zetaZeroData zetaZeroData_isNontrivial zetaZeroData_reflection)
open D5.S3.Weil.Mertens.ZeroAbscissaPower (primitive_eq_negative_tail)
open RHSharpActualEnvelope (G abs_G_sub_normalized_actualH_le)
open PrimeWindowPoleGrowth (off_line_zero_forces_signed_complete_window_mass)

/-- The weighted positive or negative mass of the complete Chebyshev tail. -/
def signedMass (e b Y : ℝ) : ℝ :=
  ∫ x in Y..Y ^ b, max (e * (-Q x)) 0 / Real.sqrt x

private theorem half_le_abscissa : (1 / 2 : ℝ) ≤ zeroAbscissa := by
  have h := zero_re_le_abscissa (zetaZeroData_isNontrivial 0)
  have hr := zero_re_le_abscissa (zetaZeroData_isNontrivial (zetaZeroData.reflection 0))
  rw [zetaZeroData_reflection] at hr
  simp only [Complex.sub_re, Complex.one_re] at hr
  linarith only [h, hr]

/-- An upper bound on the real parts of the zeros bounds the complete Mangoldt
ramp at the same power, including when the bound is an unattained supremum. -/
private theorem abs_U_le_mul_rpow_of_zero_bound {θ : ℝ} (hθ : 0 ≤ θ)
    (hzeros : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → |U x| ≤ C * x ^ θ := by
  let A : ℝ := ∑' k : ℕ, ‖actualCoeff k‖
  let R : ℝ := |Real.log (2 * Real.pi)|
  refine ⟨A + R, add_nonneg (tsum_nonneg fun _ => norm_nonneg _) (abs_nonneg _), ?_⟩
  intro x hx
  let y := Real.log x
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hy : 0 ≤ y := Real.log_nonneg hx
  have hterm (k : ℕ) :
      ‖actualCoeff k * Complex.exp ((y : ℂ) * actualZero k)‖ ≤
        ‖actualCoeff k‖ * Real.exp (y * θ) := by
    have hz := hzeros (actualZero k)
      (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz hy))
      (norm_nonneg _)
  have hH : ‖actualH y‖ ≤ A * Real.exp (y * θ) :=
    (actualH_summable y).hasSum.norm_le_of_bounded
      (actualCoeff_hasSum.summable.norm.hasSum.mul_right _) hterm
  have hR := (abs_G_sub_normalized_actualH_le hy).le
  rw [G, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _), Real.exp_log hx0] at hR
  have herror : |U x - (actualH y).re| ≤ R :=
    (le_of_mul_le_mul_left hR (Real.exp_pos _)).trans (le_abs_self _)
  rw [Real.rpow_def_of_pos hx0]
  have hone : 1 ≤ Real.exp (y * θ) := Real.one_le_exp_iff.mpr (mul_nonneg hy hθ)
  calc
    |U x| = |(actualH y).re + (U x - (actualH y).re)| := by rw [add_sub_cancel]
    _ ≤ |(actualH y).re| + |U x - (actualH y).re| := abs_add_le _ _
    _ ≤ A * Real.exp (y * θ) + R :=
      add_le_add ((Complex.abs_re_le_norm _).trans hH) herror
    _ ≤ (A + R) * Real.exp (y * θ) := by
      rw [add_mul]
      exact add_le_add_right (le_mul_of_one_le_right (abs_nonneg _) hone) _

local notation "massDensity" => fun (e x : ℝ) => max (e * (-Q x)) 0 / Real.sqrt x

private theorem density_nonneg (e x : ℝ) : 0 ≤ massDensity e x :=
  div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)

private theorem density_continuousAt (e : ℝ) {x : ℝ} (hx : 2 < x) :
    ContinuousAt (massDensity e) x := by
  have hx0 : 0 < x := by linarith
  have heq : (fun t : ℝ => max (e * (U t / t)) 0 / Real.sqrt t) =ᶠ[𝓝 x]
      massDensity e := by
    filter_upwards [lt_mem_nhds hx] with t ht
    rw [primitive_eq_negative_tail ht.le]
  have hU := (U_continuousAt_pos hx0).div continuousAt_id hx0.ne'
  apply ContinuousAt.congr ?_ heq
  exact (((continuousAt_const.mul hU).max continuousAt_const).div
    Real.continuous_sqrt.continuousAt (Real.sqrt_pos.mpr hx0).ne')

private theorem density_le_inv_bound {θ C e Y b x : ℝ} (hθ : 1 / 2 ≤ θ) (hC : 0 ≤ C)
    (he : e = 1 ∨ e = -1) (hx : 2 ≤ x) (hxb : x ≤ Y ^ b)
    (hY : 0 < Y) (hU : |U x| ≤ C * x ^ θ) :
    massDensity e x ≤ (C * Y ^ (b * (θ - 1 / 2))) * x⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hsign : max (e * U x) 0 ≤ |U x| := by
    refine max_le ?_ (abs_nonneg _)
    rcases he with rfl | rfl
    · simpa only [one_mul] using le_abs_self (U x)
    · simpa only [neg_one_mul] using neg_le_abs (U x)
  have hweight : x ^ θ / Real.sqrt x = x ^ (θ - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_sub hx0]
  have hpow : x ^ (θ - 1 / 2) ≤ Y ^ (b * (θ - 1 / 2)) := by
    rw [Real.rpow_mul hY.le]
    exact Real.rpow_le_rpow hx0.le hxb (sub_nonneg.mpr hθ)
  have hsplit : max (e * (U x / x)) 0 = max (e * U x) 0 / x := by
    rw [← mul_div_assoc, ← max_div_div_right hx0.le (e * U x) 0, zero_div]
  change max (e * (-Q x)) 0 / Real.sqrt x ≤ _
  rw [← primitive_eq_negative_tail hx, hsplit]
  calc
    _ ≤ (C * x ^ θ / x) / Real.sqrt x :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (hsign.trans hU) hx0.le) (Real.sqrt_nonneg _)
    _ = (C * x ^ (θ - 1 / 2)) * x⁻¹ := by
      rw [div_right_comm, mul_div_assoc, hweight, div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC)
      (inv_nonneg.mpr hx0.le)

/-- A pointwise power envelope for the ramp yields a uniform mass bound for
both signs, with a single logarithmic factor at the endpoint power. -/
private theorem signedMass_le_of_ramp_bound {θ C b Y : ℝ} (hθ : 1 / 2 ≤ θ) (hC : 0 ≤ C)
    (hU : ∀ x : ℝ, 2 ≤ x → |U x| ≤ C * x ^ θ)
    (hb : 1 < b) (hY : 2 < Y) {e : ℝ} (he : e = 1 ∨ e = -1) :
    signedMass e b Y ≤ (C * (b - 1)) * Y ^ (b * (θ - 1 / 2)) * Real.log Y := by
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hYY : Y ≤ Y ^ b := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY1 hb.le
  have hYb : 0 < Y ^ b := hY0.trans_le hYY
  have hpos (x : ℝ) (hx : x ∈ uIcc Y (Y ^ b)) : Y ≤ x := by
    rw [uIcc_of_le hYY] at hx
    exact hx.1
  have hint : IntervalIntegrable (massDensity e) volume Y (Y ^ b) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (density_continuousAt e (hY.trans_le (hpos x hx))).continuousWithinAt
  have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume Y (Y ^ b) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (continuousAt_id.inv₀ (hY0.trans_le (hpos x hx)).ne').continuousWithinAt
  unfold signedMass
  calc
    _ ≤ ∫ x in Y..Y ^ b, (C * Y ^ (b * (θ - 1 / 2))) * x⁻¹ :=
      intervalIntegral.integral_mono_on hYY hint (hinv.const_mul _) (fun x hx =>
        density_le_inv_bound hθ hC he (hY.le.trans hx.1) hx.2 hY0
          (hU x (hY.le.trans hx.1)))
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hY0 hYb,
        Real.log_div hYb.ne' hY0.ne', Real.log_rpow hY0]
      ring

/-- The abscissa gives the upper power envelope without any zero-free-strip
or endpoint-attainment hypothesis. -/
private theorem eventually_signedMass_le (b : ℝ) (hb : 1 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Y : ℝ in atTop, ∀ e : ℝ, e = 1 ∨ e = -1 →
      signedMass e b Y ≤ C * Y ^ (b * (zeroAbscissa - 1 / 2)) * Real.log Y := by
  obtain ⟨C, hC, hU⟩ := abs_U_le_mul_rpow_of_zero_bound
    ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans half_le_abscissa)
    (fun _ hρ => zero_re_le_abscissa hρ)
  refine ⟨C * (b - 1), mul_nonneg hC (sub_nonneg.mpr hb.le), ?_⟩
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with Y hY e he
  exact signedMass_le_of_ramp_bound half_le_abscissa hC
    (fun x hx => hU x (one_le_two.trans hx)) hb hY he

/-- If the abscissa is above the critical line, each subterminal exponent is a
lower power bound on every sufficiently late window, simultaneously for both signs. -/
private theorem eventually_rpow_le_signedMass {b a : ℝ} (hb : 1 < b) (hΘ : 1 / 2 < zeroAbscissa)
    (hab : a < b * (zeroAbscissa - 1 / 2)) :
    ∀ᶠ Y : ℝ in atTop, ∀ e : ℝ, e = 1 ∨ e = -1 → Y ^ a ≤ signedMass e b Y := by
  have hb0 := zero_lt_one.trans hb
  have hcut : 1 / 2 + a / b < zeroAbscissa := by
    have h := (div_lt_iff₀ hb0).mpr (by simpa only [mul_comm] using hab)
    linarith only [h]
  obtain ⟨r, ⟨ρ, hρ, rfl⟩, hr⟩ :=
    exists_lt_of_lt_csSup zero_real_parts_nonempty (max_lt hΘ hcut)
  have hρhalf : 1 / 2 < ρ.re := (le_max_left _ _).trans_lt hr
  have hρa : a < b * (ρ.re - 1 / 2) := by
    have hr := (le_max_right (1 / 2) (1 / 2 + a / b)).trans_lt hr
    have h : a / b < ρ.re - 1 / 2 := by linarith only [hr]
    simpa only [mul_comm] using (div_lt_iff₀ hb0).mp h
  simpa only [signedMass, sub_sub_cancel] using
    off_line_zero_forces_signed_complete_window_mass hρ.1 hρhalf hb (sub_pos.mpr hρa)

private theorem signedMass_nonneg {b Y : ℝ} (hb : 1 < b) (hY : 1 ≤ Y) (e : ℝ) :
    0 ≤ signedMass e b Y := by
  have hYY : Y ≤ Y ^ b := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY hb.le
  exact intervalIntegral.integral_nonneg_of_forall hYY (density_nonneg e)

/-- For either sign, the complete arithmetic power-window mass has exact
logarithmic growth exponent determined by the rightmost zeta zero abscissa. -/
theorem tendsto_log_one_add_signedMass {b e : ℝ} (hb : 1 < b) (he : e = 1 ∨ e = -1) :
    Tendsto (fun Y : ℝ => Real.log (1 + signedMass e b Y) / Real.log Y)
      atTop (𝓝 (b * (zeroAbscissa - 1 / 2))) := by
  let p := b * (zeroAbscissa - 1 / 2)
  have hb0 := zero_lt_one.trans hb
  have hp : 0 ≤ p := mul_nonneg hb0.le (sub_nonneg.mpr half_le_abscissa)
  change Tendsto _ atTop (𝓝 p)
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    by_cases hneg : a < 0
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
      exact hneg.trans_le (div_nonneg
        (Real.log_nonneg (le_add_of_nonneg_right (signedMass_nonneg hb hY.le e)))
        (Real.log_nonneg hY.le))
    have hΘ : 1 / 2 < zeroAbscissa :=
      sub_pos.mp (pos_of_mul_pos_right ((le_of_not_gt hneg).trans_lt ha) hb0.le)
    filter_upwards [eventually_rpow_le_signedMass hb hΘ ha,
      eventually_gt_atTop (1 : ℝ)] with Y hlow hY
    have hY0 := zero_lt_one.trans hY
    have hlog := Real.log_pos hY
    apply (lt_div_iff₀ hlog).2
    rw [← Real.log_rpow hY0]
    exact Real.log_lt_log (Real.rpow_pos_of_pos hY0 _)
      ((hlow e he).trans_lt (lt_add_of_pos_left _ zero_lt_one))
  · intro a ha
    obtain ⟨C, hC, hub⟩ := eventually_signedMass_le b hb
    have hsmall : Tendsto (fun Y : ℝ => Real.log (Real.log Y) / Real.log Y) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
    have hconst : Tendsto (fun Y : ℝ => Real.log (1 + C) / Real.log Y) atTop (𝓝 0) :=
      Real.tendsto_log_atTop.const_div_atTop _
    have hlimit : Tendsto (fun Y : ℝ =>
        (Real.log (1 + C) / Real.log Y + Real.log (Real.log Y) / Real.log Y) + p)
        atTop (𝓝 p) := by simpa only [add_zero, zero_add] using (hconst.add hsmall).add_const p
    filter_upwards [hub, hlimit.eventually (gt_mem_nhds ha),
      eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with Y hupper hstrict hY hlog1
    have hY0 := zero_lt_one.trans hY
    have hlog := Real.log_pos hY
    have hpow := Real.rpow_pos_of_pos hY0 p
    have hdenom : 0 < 1 + C := add_pos_of_pos_of_nonneg zero_lt_one hC
    have hcap : 1 + signedMass e b Y ≤ ((1 + C) * Real.log Y) * Y ^ p := by
      calc
        _ ≤ Y ^ p + C * Y ^ p * Real.log Y :=
          add_le_add (Real.one_le_rpow hY.le hp) (hupper e he)
        _ = (1 + C * Real.log Y) * Y ^ p := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by rw [add_mul, one_mul]; exact add_le_add_left hlog1 _) hpow.le
    apply lt_of_le_of_lt _ hstrict
    calc
      _ ≤ Real.log (((1 + C) * Real.log Y) * Y ^ p) / Real.log Y :=
        div_le_div_of_nonneg_right
          (Real.log_le_log (add_pos_of_pos_of_nonneg zero_lt_one
            (signedMass_nonneg hb hY.le e)) hcap) hlog.le
      _ = _ := by
        rw [Real.log_mul (mul_pos hdenom hlog).ne' hpow.ne',
          Real.log_mul hdenom.ne' hlog.ne', Real.log_rpow hY0, add_div, add_div,
          mul_div_cancel_right₀ _ hlog.ne']

end D5.S3.Weil.Mertens.IntegratedExplicit.SignedCompleteWindowExponent
