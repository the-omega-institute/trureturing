/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The prime-power bias has a signed square correction and a cube main term. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootTail
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SquareSpectrum
import D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
import D5.S3.Weil.Mertens.IntegratedExplicit.WidePrimeWindowMass
import D5.S3.Weil.Mertens.ZeroAbscissaPower

/-! The integrated complete tail controls both root cutoffs. The fifth-root majorant
dominates the errors after scaling to logarithmic density. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.Mertens.ZeroAbscissaPower (primitive_eq_negative_tail)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
  (actualZero actualData actualOccurrenceEquiv actual_height_gt_ten firstLiMass firstLiMass_lt_one)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
  (primeTail prime_integrable prime_power_window_correction)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean
  (windowError normalizedMass normalizedZeroSeries)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (prime_window_remainder_of_rh spectralPrimitive windowDiscrepancy)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
  (G abs_G_sub_normalized_actualH_le actual_G_control coeff_norm_hasSum)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

private def C : ℝ := |Real.log (2 * Real.pi)|

private def M : ℝ := firstLiMass + C

private lemma mass_nonneg (hRH : RiemannHypothesis) : 0 ≤ firstLiMass := by
  rw [← (coeff_norm_hasSum hRH).tsum_eq]
  exact tsum_nonneg fun _ => norm_nonneg _

private def qError (x : ℝ) : ℝ := Q x + (zeroTail (Real.log x)).re

private lemma q_continuous : ContinuousOn Q (Ici 2) :=
  chebyshev_error_kernel_integrable.continuousOn_Ici_primitive_Ioi.mono
    (Ici_subset_Ici.mpr (by norm_num))

private lemma z_continuous : ContinuousOn (fun x => (zeroTail (Real.log x)).re) (Ici 2) := by
  simp_rw [zeroTail_eq]
  have hlog : ContinuousOn Real.log (Ici (2 : ℝ)) :=
    Real.continuousOn_log.mono (fun x hx => by simpa using (show x ≠ 0 by linarith [mem_Ici.mp hx]))
  exact Complex.continuous_re.comp_continuousOn
    ((((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).mul
      actualH_continuous).comp_continuousOn hlog))

private lemma qError_bound {x : ℝ} (hx : 2 ≤ x) : |qError x| ≤ C * x ^ (-1 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hh := (abs_G_sub_normalized_actualH_le (Real.log_nonneg (by linarith : 1 ≤ x))).le
  rw [G, Real.exp_log hx0, ← mul_sub, abs_mul, abs_of_nonneg (Real.exp_nonneg _)] at hh
  have hU : |U x - (actualH (Real.log x)).re| ≤ C :=
    ((mul_le_mul_iff_right₀ (Real.exp_pos _)).mp hh).trans (le_abs_self _)
  have hQ : Q x = -(U x / x) := by linarith only [primitive_eq_negative_tail hx]
  rw [qError, zeroTail_eq, Complex.re_ofReal_mul, Real.exp_neg, Real.exp_log hx0,
    hQ, Real.rpow_neg_one]
  have h : -(U x / x) + x⁻¹ * (actualH (Real.log x)).re =
      -((U x - (actualH (Real.log x)).re) * x⁻¹) := by rw [div_eq_mul_inv]; ring
  rw [h, abs_neg, abs_mul, abs_of_nonneg (inv_nonneg.mpr hx0.le)]
  exact mul_le_mul_of_nonneg_right hU (inv_nonneg.mpr hx0.le)

private lemma z_bound (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    |(zeroTail (Real.log x)).re| ≤ firstLiMass * x ^ (-(1 / 2) : ℝ) := by
  have he : Real.exp (-Real.log x / 2) = x ^ (-(1 / 2) : ℝ) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [← he]
  exact (Complex.abs_re_le_norm _).trans (norm_zeroTail_le hRH _)

private lemma q_bound (hRH : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    |Q x| ≤ M * x ^ (-(1 / 2) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have he : Q x = qError x - (zeroTail (Real.log x)).re := by unfold qError; ring
  rw [he]
  calc
    _ ≤ |qError x| + |(zeroTail (Real.log x)).re| := abs_sub _ _
    _ ≤ C * x ^ (-1 : ℝ) + firstLiMass * x ^ (-(1 / 2) : ℝ) :=
      add_le_add (qError_bound hx) (z_bound hRH hx0)
    _ ≤ M * x ^ (-(1 / 2) : ℝ) := by
      rw [M, add_mul, add_comm (firstLiMass * _)]
      have hp : x ^ (-1 : ℝ) ≤ x ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hc := mul_le_mul_of_nonneg_left hp (show 0 ≤ C from abs_nonneg _)
      linarith only [hc]

private lemma weighted_bound {f : ℝ → ℝ} {y b d D : ℝ} (hy : 2 ≤ y) (hbd : 1 < b + d)
    (hc : ContinuousOn f (Ici 2))
    (hb : ∀ s, 2 ≤ s → |f s| ≤ D * s ^ (-d)) :
    IntegrableOn (fun s => s ^ (-b) * f s) (Ioi y) ∧
      |∫ s in Ioi y, s ^ (-b) * f s| ≤ D / (b + d - 1) * y ^ (1 - (b + d)) := by
  have hy0 : 0 < y := by linarith
  have hmajor : IntegrableOn (fun s => D * s ^ (-(b + d))) (Ioi y) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hy0).const_mul D
  have hcomp (s : ℝ) (hs : y < s) : ‖s ^ (-b) * f s‖ ≤ D * s ^ (-(b + d)) := by
    have hs0 := hy0.trans hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs0 _),
      show -(b + d) = -b + -d by ring, Real.rpow_add hs0]
    exact (mul_le_mul_of_nonneg_left (hb s (hy.trans hs.le)) (by positivity)).trans_eq (by ring)
  have hf : IntegrableOn (fun s => s ^ (-b) * f s) (Ioi y) := by
    apply hmajor.mono'
    · have hp : ContinuousOn (fun s : ℝ => s ^ (-b)) (Ioi y) :=
        fun s hs => ContinuousAt.continuousWithinAt
          (Real.continuousAt_rpow_const s (-b) (Or.inl (hy0.trans hs).ne'))
      exact (hp.mul (hc.mono (fun _ hs => hy.trans (mem_Ioi.mp hs).le))).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using hcomp s hs
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ s in Ioi y, ‖s ^ (-b) * f s‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (f := fun s => s ^ (-b) * f s)
          (μ := volume.restrict (Ioi y)))
    _ ≤ ∫ s in Ioi y, D * s ^ (-(b + d)) :=
      setIntegral_mono_on hf.norm hmajor measurableSet_Ioi hcomp
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hy0,
        show -(b + d) + 1 = 1 - (b + d) by ring,
        show 1 - (b + d) = -(b + d - 1) by ring]
      rw [neg_div, div_neg, neg_neg]
      ring

private def centered (r x : ℝ) : ℝ :=
  Real.sqrt x * (∫ t in Ioi x, (Chebyshev.psi (t ^ r⁻¹) - t ^ r⁻¹) / t ^ 2)

private lemma square_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 4 ≤ x) :
    |centered 2 x - squareDensity (Real.log x)| ≤ (4 * C) * x ^ (-(1 / 2) : ℝ) := by
  have hx0 : 0 < x := by linarith
  let y := Real.sqrt x
  have hy : 2 ≤ y := by
    calc
      2 = Real.sqrt 4 := by norm_num
      _ ≤ y := Real.sqrt_le_sqrt hx
  have hy0 : 0 < y := by linarith
  have hroot : x ^ (2 : ℝ)⁻¹ = y := by
    change _ = Real.sqrt x
    rw [Real.sqrt_eq_rpow, one_div]
  have ht := centered_root_tail (r := 2) (by norm_num) hx0
  dsimp only at ht
  change centered 2 x = _ at ht
  rw [hroot] at ht
  have hcut : centered 2 x = 2 * (Q y - y * (∫ s in Ioi y, s ^ (-2 : ℝ) * Q s)) := by
    rw [ht, show (1 - 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    rw [show (2 : ℝ) - 1 = 1 by norm_num]
    change 2 * y * (Q y * y⁻¹ - 1 * _) = _
    field_simp [hy0.ne']
  have hphase : Real.exp (Real.log x / 2) = y := by
    rw [show y = Real.sqrt x from rfl, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have hs := square_spectral_transform (Real.log x)
  dsimp only at hs
  rw [hphase] at hs
  obtain ⟨he, hb⟩ := weighted_bound (f := qError) (b := 2) (d := 1) hy (by norm_num)
    (q_continuous.add z_continuous) (fun _ hx => qError_bound hx)
  obtain ⟨hz, _⟩ := weighted_bound (b := 2) (d := 1 / 2) hy (by norm_num)
    z_continuous (fun _ hx => z_bound hRH (by linarith))
  have hsplit : (∫ s in Ioi y, s ^ (-2 : ℝ) * Q s) =
      (∫ s in Ioi y, s ^ (-2 : ℝ) * qError s) -
        (∫ s in Ioi y, s ^ (-2 : ℝ) * (zeroTail (Real.log s)).re) := by
    rw [← integral_sub (f := fun s => s ^ (-2 : ℝ) * qError s)
      (g := fun s => s ^ (-2 : ℝ) * (zeroTail (Real.log s)).re) he hz]
    exact setIntegral_congr_fun measurableSet_Ioi (fun s _ => by unfold qError; ring)
  rw [hcut, ← hs, hsplit]
  have heq : 2 * (Q y - y * ((∫ s in Ioi y, s ^ (-2 : ℝ) * qError s) -
        ∫ s in Ioi y, s ^ (-2 : ℝ) * (zeroTail (Real.log s)).re)) -
      2 * (-(zeroTail (Real.log y)).re +
        y * (∫ s in Ioi y, s ^ (-2 : ℝ) * (zeroTail (Real.log s)).re)) =
      2 * (qError y - y * (∫ s in Ioi y, s ^ (-2 : ℝ) * qError s)) := by unfold qError; ring
  rw [heq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hb' : |∫ s in Ioi y, s ^ (-2 : ℝ) * qError s| ≤ C / 2 * y ^ (-2 : ℝ) := by
    norm_num at hb ⊢
    exact hb
  have hweight : y * y ^ (-2 : ℝ) = y ^ (-1 : ℝ) := by
    calc
      _ = y ^ (1 : ℝ) * y ^ (-2 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hy0]; norm_num
  have hscale : y ^ (-1 : ℝ) = x ^ (-(1 / 2) : ℝ) := by
    rw [show y = Real.sqrt x by rfl, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    norm_num
  calc
    _ ≤ 2 * (|qError y| + y * |∫ s in Ioi y, s ^ (-2 : ℝ) * qError s|) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (abs_sub _ _).trans_eq (by rw [abs_mul, abs_of_pos hy0])
    _ ≤ 2 * (C * y ^ (-1 : ℝ) + y * (C / 2 * y ^ (-2 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (qError_bound hy) (mul_le_mul_of_nonneg_left hb' hy0.le)) (by norm_num)
    _ ≤ _ := by
      rw [show y * (C / 2 * y ^ (-2 : ℝ)) = C / 2 * (y * y ^ (-2 : ℝ)) by ring, hweight, hscale]
      have hp : 0 ≤ C * x ^ (-(1 / 2) : ℝ) :=
        mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hx0.le _)
      nlinarith only [hp]

private lemma cube_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 8 ≤ x) :
    |centered 3 x| ≤ (9 * M) * x ^ (-(1 / 3) : ℝ) := by
  have hx0 : 0 < x := by linarith
  let y := x ^ (3 : ℝ)⁻¹
  have hy : 2 ≤ y := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 8) hx
      (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
    rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num [Real.rpow_natCast],
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
    norm_num at h
    simpa [y, one_div] using h
  have hy0 : 0 < y := by linarith
  have ht := centered_root_tail (r := 3) (by norm_num) hx0
  dsimp only at ht
  change centered 3 x = 3 * Real.sqrt x *
    (Q y * y ^ (1 - (3 : ℝ)) - (3 - 1) * (∫ s in Ioi y, s ^ (-3 : ℝ) * Q s)) at ht
  rw [show (1 - 3 : ℝ) = -2 by norm_num, show (3 - 1 : ℝ) = 2 by norm_num] at ht
  obtain ⟨_, hb⟩ := weighted_bound (b := 3) (d := 1 / 2) hy (by norm_num)
    q_continuous (fun _ hx => q_bound hRH hx)
  have hM : 0 ≤ M := add_nonneg (mass_nonneg hRH) (abs_nonneg _)
  have he (e : ℝ) : 0 ≤ y ^ e := Real.rpow_nonneg hy0.le _
  have hweighted : |∫ s in Ioi y, s ^ (-3 : ℝ) * Q s| ≤ M * y ^ (-(5 / 2) : ℝ) := by
    have hbd : (3 : ℝ) + 1 / 2 - 1 = 5 / 2 := by norm_num
    rw [hbd, show (1 - (3 + 1 / 2) : ℝ) = -(5 / 2) by norm_num] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (div_le_self hM (by norm_num)) (he _))
  have hscale : Real.sqrt x * y ^ (-(5 / 2) : ℝ) = x ^ (-(1 / 3) : ℝ) := by
    dsimp [y]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
    norm_num
  rw [ht, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 * Real.sqrt x)]
  calc
    _ ≤ 3 * Real.sqrt x * (|Q y| * y ^ (-2 : ℝ) +
        2 * |∫ s in Ioi y, s ^ (-3 : ℝ) * Q s|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (abs_sub _ _).trans_eq (by
        rw [abs_mul, abs_mul, abs_of_nonneg (he (-2)), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)])
    _ ≤ 3 * Real.sqrt x * (M * y ^ (-(1 / 2) : ℝ) * y ^ (-2 : ℝ) +
        2 * (M * y ^ (-(5 / 2) : ℝ))) := by
      gcongr
      exact q_bound hRH hy
    _ = _ := by
      rw [mul_assoc M, ← Real.rpow_add hy0, show -(1 / 2 : ℝ) + -2 = -(5 / 2) by norm_num,
        ← hscale]
      ring

/-- The normalized prime-power correction has the signed square-mode term and cube
coefficient (3/2), with the fifth-root error envelope. -/
theorem rh_prime_power_density (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 8 ≤ x →
      |Real.sqrt x * (Q x - primeTail x) - 2 -
        (3 / 2) * x ^ (-(1 / 6) : ℝ) - squareDensity (Real.log x)| ≤
          K * x ^ (-(3 / 10) : ℝ) := by
  let L := (Real.log 4 + 4) * (5 / 4)
  have hC : 0 ≤ C := abs_nonneg _
  have hM : 0 ≤ M := add_nonneg (mass_nonneg hRH) hC
  have hL : 0 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  refine ⟨L + 4 * C + 9 * M + 1, by positivity, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  let E := Q x - primeTail x -
    (∫ t in Ioi x, Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
    (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2)
  have hrem : 0 ≤ E ∧ Real.sqrt x * E ≤ L * x ^ (-(3 / 10) : ℝ) :=
    root_cutoff_remainder hx0
  have h2 := root_tail_main (r := 2) (by norm_num) hx0
  change _ = _ + centered 2 x at h2
  rw [show (2 : ℝ) / (2 - 1) = 2 by norm_num,
    show (2 : ℝ)⁻¹ - 1 / 2 = 0 by norm_num, Real.rpow_zero, mul_one] at h2
  have h3 := root_tail_main (r := 3) (by norm_num) hx0
  change _ = _ + centered 3 x at h3
  have hcoef : (3 : ℝ)⁻¹ - 1 / 2 = -(1 / 6) := by norm_num
  rw [hcoef, show (3 : ℝ) / (3 - 1) = 3 / 2 by norm_num] at h3
  have heq : Real.sqrt x * (Q x - primeTail x) - 2 -
      (3 / 2) * x ^ (-(1 / 6) : ℝ) - squareDensity (Real.log x) =
      (centered 2 x - squareDensity (Real.log x)) + centered 3 x + Real.sqrt x * E := by
    dsimp [E]
    linear_combination h2 + h3
  rw [heq]
  calc
    _ ≤ |centered 2 x - squareDensity (Real.log x)| + |centered 3 x| + Real.sqrt x * E := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hrem.1)]
      exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (4 * C) * x ^ (-(1 / 2) : ℝ) + (9 * M) * x ^ (-(1 / 3) : ℝ) +
        L * x ^ (-(3 / 10) : ℝ) :=
      add_le_add (add_le_add (square_error hRH (by linarith)) (cube_error hRH hx)) hrem.2
    _ ≤ _ := by
      have h2r := Real.rpow_le_rpow_of_exponent_le hx1
        (show -(1 / 2 : ℝ) ≤ -(3 / 10) by norm_num)
      have h3r := Real.rpow_le_rpow_of_exponent_le hx1
        (show -(1 / 3 : ℝ) ≤ -(3 / 10) by norm_num)
      have h2c := mul_le_mul_of_nonneg_left h2r (show 0 ≤ 4 * C by positivity)
      have h3c := mul_le_mul_of_nonneg_left h3r (show 0 ≤ 9 * M by positivity)
      nlinarith [Real.rpow_nonneg hx0.le (-(3 / 10 : ℝ))]


/-- The prime-power correction and the ordinary complete-tail error in log coordinates. -/
def rootWindowDensity (u : ℝ) : ℝ :=
  Real.sqrt (Real.exp u) * (Q (Real.exp u) - primeTail (Real.exp u)) - 2 +
    (G u - Real.exp (-u / 2) * (actualH u).re)

private lemma exp_decay_integral {r a b : ℝ} (hr : 0 < r) :
    (∫ u in a..b, Real.exp (-r * u)) = (Real.exp (-r * a) - Real.exp (-r * b)) / r := by
  have hi : IntervalIntegrable (fun u => Real.exp (-r * u)) volume a b :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (-r * u))).intervalIntegrable _ _
  have hd (u : ℝ) : HasDerivAt (fun t => Real.exp (-r * t) / (-r)) (Real.exp (-r * u)) u := by
    have hh := (((hasDerivAt_id u).const_mul (-r)).exp).div_const (-r)
    simp only [id, mul_one] at hh
    convert hh using 1
    field_simp [hr.ne']
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi]
  ring

private lemma exp_rpow (u r : ℝ) : (Real.exp u) ^ r = Real.exp (r * u) := by
  rw [← Real.exp_mul, mul_comm]

private lemma exp_neg_log_rpow {x : ℝ} (hx : 0 < x) (r : ℝ) :
    Real.exp (-r * Real.log x) = x ^ (-r) := by
  rw [← exp_rpow, Real.exp_log hx]

private lemma complete_scaled {x : ℝ} (hx : 2 ≤ x) :
    G (Real.log x) = -(Real.sqrt x * Q x) := by
  have hx0 : 0 < x := by linarith
  have hU := (div_eq_iff hx0.ne').mp (primitive_eq_negative_tail hx)
  have hscale : Real.exp (-Real.log x / 2) * x = Real.sqrt x := by
    calc
      _ = x ^ (-(1 / 2) : ℝ) * x ^ (1 : ℝ) := by
        rw [Real.rpow_one, ← exp_neg_log_rpow hx0]
        congr 2
        ring
      _ = _ := by rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
  rw [G, Real.exp_log hx0, hU]
  linear_combination -Q x * hscale

private lemma late_strict_prime_tail (hRH : RiemannHypothesis) :
    ∀ᶠ x : ℝ in atTop, 0 < Real.sqrt x * (-primeTail x) := by
  have hG := (actual_G_control hRH).1 (1 / 2) (by norm_num)
  have hb := prime_power_window_correction.1.eventually_const_lt (show (3 / 2 : ℝ) < 2 by norm_num)
  filter_upwards [Real.tendsto_log_atTop.eventually hG, hb, eventually_ge_atTop (2 : ℝ)]
    with x hg hb hx
  rw [complete_scaled hx] at hg
  linarith only [(abs_lt.mp hg).1, firstLiMass_lt_one, hb,
    mul_sub (Real.sqrt x) (Q x) (primeTail x), mul_neg (Real.sqrt x) (primeTail x)]

private lemma rootWindowDensity_continuousOn :
    ContinuousOn rootWindowDensity (Ici (Real.log 2)) := by
  have htexp : MapsTo Real.exp (Ici (Real.log 2)) (Ici 2) := by
    intro u hu
    exact (Real.exp_log (by norm_num : (0 : ℝ) < 2)) ▸ Real.exp_le_exp.mpr hu
  have hq := q_continuous.comp Real.continuous_exp.continuousOn htexp
  have hp := prime_integrable.continuousOn_Ici_primitive_Ioi.comp
    Real.continuous_exp.continuousOn
    (htexp.mono_right (Ici_subset_Ici.mpr (by norm_num : (1 : ℝ) ≤ 2)))
  have hb := ((Real.continuous_sqrt.comp Real.continuous_exp).continuousOn.mul
    (hq.sub hp)).sub (continuousOn_const (c := (2 : ℝ)))
  have hG : ContinuousOn G (Ici (Real.log 2)) := by
    unfold G
    exact ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-u / 2))).mul
      U_exp_continuous).continuousOn
  have hZ : Continuous (fun u : ℝ => Real.exp (-u / 2) * (actualH u).re) :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (-u / 2))).mul
      (Complex.continuous_re.comp actualH_continuous)
  exact hb.add (hG.sub hZ.continuousOn)

/-- The integrated root-cutoff correction on a common window, with both endpoint
powers retained. The same cutoff ensures the prime-only density is strictly positive. -/
theorem rh_root_correction_window (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 8 ≤ a₀ ∧ 0 < K ∧
      (∀ x : ℝ, a₀ ≤ x → 0 < Real.sqrt x * (-primeTail x)) ∧
      ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
        |(∫ u in Real.log a..Real.log B, rootWindowDensity u) -
          9 * (a ^ (-(1 / 6) : ℝ) - B ^ (-(1 / 6) : ℝ)) -
          squarePrimitive B + squarePrimitive a| ≤
            K * (a ^ (-(3 / 10) : ℝ) - B ^ (-(3 / 10) : ℝ)) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (late_strict_prime_tail hRH)
  obtain ⟨K, hK, hKbound⟩ := rh_prime_power_density hRH
  have hC : 0 ≤ C := abs_nonneg _
  refine ⟨max T 8, (K + C) / (3 / 10), le_max_right _ _, by positivity,
    fun x hx => hT x ((le_max_left _ _).trans hx), ?_⟩
  intro a B ha hab
  have ha8 := (le_max_right T 8).trans ha
  have ha0 : 0 < a := by linarith
  have hB0 := ha0.trans_le hab
  have hablog := Real.log_le_log ha0 hab
  let E (u : ℝ) := rootWindowDensity u - (3 / 2) * Real.exp (-(1 / 6 : ℝ) * u) - squareDensity u
  have hcut (u : ℝ) (hu : u ∈ Icc (Real.log a) (Real.log B)) : 8 ≤ Real.exp u :=
    ha8.trans (by simpa [Real.exp_log ha0] using Real.exp_le_exp.mpr hu.1)
  have hE (u : ℝ) (hu : u ∈ Icc (Real.log a) (Real.log B)) :
      |E u| ≤ (K + C) * Real.exp (-(3 / 10 : ℝ) * u) := by
    have hu0 : 0 ≤ u := by
      apply Real.exp_le_exp.mp
      rw [Real.exp_zero]
      linarith only [hcut u hu]
    have h := hKbound (Real.exp u) (hcut u hu)
    rw [Real.log_exp, exp_rpow, exp_rpow] at h
    have hG := (abs_G_sub_normalized_actualH_le hu0).le
    have hg : |G u - Real.exp (-u / 2) * (actualH u).re| ≤
        C * Real.exp (-(3 / 10 : ℝ) * u) := by
      refine hG.trans ?_
      rw [mul_comm (Real.exp _)]
      exact mul_le_mul (le_abs_self _) (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _) hC
    unfold E rootWindowDensity
    have heq : ∀ b c d e : ℝ, b - 2 + c - d - e = (b - 2 - d - e) + c := by
      intros
      ring
    rw [heq]
    exact (abs_add_le _ _).trans ((add_le_add h hg).trans_eq (by ring))
  have hmain : IntervalIntegrable (fun u : ℝ => (3 / 2) * Real.exp (-(1 / 6 : ℝ) * u))
      volume (Real.log a) (Real.log B) :=
    (by fun_prop : Continuous (fun u : ℝ => (3 / 2) * Real.exp (-(1 / 6 : ℝ) * u))).intervalIntegrable
      _ _
  obtain ⟨hsq, hsqint⟩ := square_density_integral (Real.log a) (Real.log B)
  have hwin : IntervalIntegrable rootWindowDensity volume (Real.log a) (Real.log B) :=
    (rootWindowDensity_continuousOn.mono (by
      rw [uIcc_of_le hablog]
      intro u hu
      exact (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith)).trans hu.1)).intervalIntegrable
  have hEi : IntervalIntegrable E volume (Real.log a) (Real.log B) := (hwin.sub hmain).sub hsq
  have hupper : IntervalIntegrable (fun u : ℝ => (K + C) * Real.exp (-(3 / 10 : ℝ) * u))
      volume (Real.log a) (Real.log B) :=
    (show Continuous (fun u : ℝ => (K + C) * Real.exp (-(3 / 10 : ℝ) * u)) by fun_prop)
      |>.intervalIntegrable _ _
  have hbound : |∫ u in Real.log a..Real.log B, E u| ≤
      ∫ u in Real.log a..Real.log B, (K + C) * Real.exp (-(3 / 10 : ℝ) * u) :=
    (intervalIntegral.abs_integral_le_integral_abs hablog).trans
      (intervalIntegral.integral_mono_on hablog hEi.abs hupper hE)
  change |(∫ u in Real.log a..Real.log B,
    rootWindowDensity u - (3 / 2) * Real.exp (-(1 / 6 : ℝ) * u) - squareDensity u)| ≤ _ at hbound
  rw [intervalIntegral.integral_sub (hwin.sub hmain) hsq,
    intervalIntegral.integral_sub hwin hmain, hsqint, Real.exp_log hB0, Real.exp_log ha0,
    intervalIntegral.integral_const_mul, exp_decay_integral (by norm_num : (0 : ℝ) < 1 / 6),
    exp_neg_log_rpow ha0, exp_neg_log_rpow hB0, intervalIntegral.integral_const_mul,
    exp_decay_integral (by norm_num : (0 : ℝ) < 3 / 10),
    exp_neg_log_rpow ha0, exp_neg_log_rpow hB0] at hbound
  convert hbound using 1
  · congr 1
    ring
  · ring


/-- The late prime-only negative mass with its ordinary zero primitive, cube main
term and square-cutoff primitive, on the same pair of endpoints. -/
theorem prime_window_cube_and_square_of_rh (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧ ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |(∫ x in a..B, max (-primeTail x) 0 / Real.sqrt x) - 2 * Real.log (B / a) -
        spectralPrimitive (phaseOrbit (Real.log B)) + spectralPrimitive (phaseOrbit (Real.log a)) -
        9 * (a ^ (-(1 / 6) : ℝ) - B ^ (-(1 / 6) : ℝ)) - squarePrimitive B + squarePrimitive a| ≤
          K * (a ^ (-(3 / 10) : ℝ) - B ^ (-(3 / 10) : ℝ)) := by
  obtain ⟨a₀, K, ha₀, hK, hpositive, hwindow⟩ := rh_root_correction_window hRH
  refine ⟨a₀, K, by linarith, hK, fun a B ha hab => ?_⟩
  have ha0 : 0 < a := by linarith
  have hlog := Real.log_le_log ha0 hab
  have hIntegral : (∫ u in Real.log a..Real.log B, windowError u) =
      ∫ u in Real.log a..Real.log B, rootWindowDensity u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hlog] at hu
    have hx : a ≤ Real.exp u := by simpa [Real.exp_log ha0] using Real.exp_le_exp.mpr hu.1
    have hpos := hpositive (Real.exp u) (ha.trans hx)
    have hscaled := complete_scaled (x := Real.exp u) (by linarith)
    rw [Real.log_exp] at hscaled
    rw [windowError, normalizedMass, normalizedZeroSeries, max_eq_left hpos.le,
      rootWindowDensity, Complex.re_ofReal_mul, hscaled]
    ring
  have hIdentity := (prime_window_remainder_of_rh hRH).2.2 a B (by linarith) hab
  change |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
    spectralPrimitive (phaseOrbit (Real.log a)) -
    9 * (a ^ (-(1 / 6) : ℝ) - B ^ (-(1 / 6) : ℝ)) - squarePrimitive B + squarePrimitive a| ≤ _
  rw [hIdentity, hIntegral]
  exact hwindow a B ha hab

private lemma endpoint_primitives_bounded :
    ∃ M : ℝ, ∀ x : ℝ, 1 ≤ x →
      |spectralPrimitive (phaseOrbit (Real.log x))| ≤ M ∧ |squarePrimitive x| ≤ 4 * M := by
  let M := ∑' k : ℕ, ‖actualCoeff k‖
  have hM : HasSum (fun k : ℕ => ‖actualCoeff k‖) M :=
    actualCoeff_hasSum.summable.norm.hasSum
  refine ⟨M, fun x hx => ⟨?_, ?_⟩⟩
  · unfold spectralPrimitive
    refine (Complex.abs_re_le_norm _).trans (tsum_of_norm_bounded hM fun k => ?_)
    have hg : 10 < |(actualZero k).im| :=
      actual_height_gt_ten _ (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
    rw [norm_div, norm_mul, Circle.norm_coe, mul_one, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact div_le_self (norm_nonneg _) (by linarith)
  · have hx0 : 0 < x := zero_lt_one.trans_le hx
    change |4 * (∑' k : ℕ, (x : ℂ) ^ ((actualZero k - 1) / 2) /
      (actualZero k * (1 - actualZero k) * (2 - actualZero k))).re| ≤ 4 * M
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans
      (tsum_of_norm_bounded hM fun k => ?_)) (by norm_num)
    have hstrip := (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2
    change (actualZero k).re < 1 at hstrip
    have hgap : 1 ≤ ‖2 - actualZero k‖ := by
      have h := Complex.abs_re_le_norm (2 - actualZero k)
      rw [Complex.sub_re, Complex.re_ofNat, abs_of_pos (by linarith)] at h
      linarith
    have hp : ‖(x : ℂ) ^ ((actualZero k - 1) / 2)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      apply Real.rpow_le_one_of_one_le_of_nonpos hx
      norm_num [Complex.div_re, Complex.sub_re]
      linarith
    rw [show (x : ℂ) ^ ((actualZero k - 1) / 2) /
        (actualZero k * (1 - actualZero k) * (2 - actualZero k)) =
        ((x : ℂ) ^ ((actualZero k - 1) / 2) * actualCoeff k) / (2 - actualZero k) by
      simp only [actualCoeff, div_eq_mul_inv, mul_inv, mul_assoc, one_mul]]
    rw [norm_div, norm_mul]
    exact (div_le_self (by positivity) hgap).trans
      (mul_le_of_le_one_left (norm_nonneg _) hp)

/-- The full corrected prime-only window estimate characterizes RH. -/
theorem rh_iff_prime_window_cube_and_square :
    RiemannHypothesis ↔
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧ ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |(∫ x in a..B, max (-primeTail x) 0 / Real.sqrt x) - 2 * Real.log (B / a) -
        spectralPrimitive (phaseOrbit (Real.log B)) + spectralPrimitive (phaseOrbit (Real.log a)) -
        9 * (a ^ (-(1 / 6) : ℝ) - B ^ (-(1 / 6) : ℝ)) - squarePrimitive B + squarePrimitive a| ≤
          K * (a ^ (-(3 / 10) : ℝ) - B ^ (-(3 / 10) : ℝ)) := by
  refine ⟨prime_window_cube_and_square_of_rh, ?_⟩
  rintro ⟨a, K, ha, hK, hwindow⟩
  by_contra hRH
  obtain ⟨M, hM⟩ := endpoint_primitives_bounded
  obtain ⟨S, hS⟩ := (WidePrimeWindowMass.prime_tail_wide_window_mass 2 (by norm_num)).1
    hRH (K + 10 * M + 10)
  let B := max S (a ^ (2 : ℝ))
  have ha1 : 1 ≤ a := by linarith
  have hab : a ≤ B := (Real.self_le_rpow_of_one_le ha1 (by norm_num)).trans (le_max_right _ _)
  obtain ⟨hpa, hAa⟩ := hM a ha1
  obtain ⟨hpB, hAB⟩ := hM B (ha1.trans hab)
  have hup := (abs_le.mp (hwindow a B le_rfl hab)).2
  have hlow := hS B (le_max_left _ _) a ha (le_max_right _ _)
  have hc : a ^ (-(1 / 6) : ℝ) - B ^ (-(1 / 6) : ℝ) ≤ 1 :=
    sub_le_self _ (Real.rpow_nonneg (by linarith) _) |>.trans
      (Real.rpow_le_one_of_one_le_of_nonpos ha1 (by norm_num))
  have he : a ^ (-(3 / 10) : ℝ) - B ^ (-(3 / 10) : ℝ) ≤ 1 :=
    sub_le_self _ (Real.rpow_nonneg (by linarith) _) |>.trans
      (Real.rpow_le_one_of_one_le_of_nonpos ha1 (by norm_num))
  linarith only [hup, hlow, hc, mul_le_of_le_one_right hK.le he,
    (abs_le.mp hpa).1, (abs_le.mp hAa).1, (abs_le.mp hpB).2, (abs_le.mp hAB).2]

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
