/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuadraticMidpoint
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuadraticMidpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A quadratic midpoint remainder for the exponentially weighted actual root spectrum. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootMidpointAverage
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHSignedShrinkingLower
import Batteries.Tactic.OpenPrivate

/-! Pair the exponential modes before taking their norms. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualZero firstLiMass firstLiMass_pos)
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp (c R cusp_remainder_bound)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity (K K_zero)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity (weight)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower (rootCoeff rootCoeff_bound)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (coeff_real)
open private integral_pair continuous_cusp_profile integral_cusp_profile from
  D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootMidpointAverage
open private odd_root_increment from
  D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHSignedShrinkingLower

private def halfPair (a x : ℝ) : ℂ :=
  ⟨-Real.cosh a * (1 - Real.cos x), -Real.sinh a * Real.sin x⟩

private theorem norm_halfPair_le (a x : ℝ) :
    ‖halfPair a x‖ ≤ (1 - Real.cos x) + Real.sinh a ^ 2 := by
  have hq : 0 ≤ 1 - Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg hq (sq_nonneg _))).1
  rw [Complex.sq_norm, Complex.normSq_apply]
  change (-Real.cosh a * (1 - Real.cos x)) * (-Real.cosh a * (1 - Real.cos x)) +
    (-Real.sinh a * Real.sin x) * (-Real.sinh a * Real.sin x) ≤ _
  calc
    _ = (1 - Real.cos x) ^ 2 * Real.cosh a ^ 2 +
        Real.sin x ^ 2 * Real.sinh a ^ 2 := by ring
    _ = (1 - Real.cos x) ^ 2 + 2 * (1 - Real.cos x) * Real.sinh a ^ 2 := by
      rw [Real.cosh_sq, Real.sin_sq]
      ring
    _ ≤ _ := by nlinarith only [sq_nonneg (Real.sinh a ^ 2)]

private theorem paired_exp_eq (a x : ℝ) :
    (Real.exp (-a) : ℂ) * (Complex.exp ((x : ℂ) * Complex.I) - 1) +
      (Real.exp a : ℂ) * (Complex.exp (((-x : ℝ) : ℂ) * Complex.I) - 1) =
        2 * halfPair a x := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.exp_ofReal_mul_I_re, Real.cos_neg,
      halfPair, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, Real.cosh_eq]
    ring
  · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_im, Complex.exp_ofReal_mul_I_im, Real.sin_neg,
      halfPair, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero, sub_zero,
      Real.sinh_eq]
    ring

private def weightedPair (f : ℝ → ℝ) (s u h : ℝ) : ℝ :=
  Real.exp (-(s * h)) * (f (u + h) - f u) +
    Real.exp (s * h) * (f (u - h) - f u)

private theorem weighted_root_pair_le (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r)
    (u h : ℝ) :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    |weightedPair (rootSignal r) s u h| ≤
      ((2 * r) * (K 0 - K (h / r)) + (2 * r * Real.sinh (s * h) ^ 2) * firstLiMass) / s := by
  dsimp only
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  have hr0 : 0 < r := by linarith
  have hs : 0 < s := by
    dsimp [s]
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  let phase (v : ℝ) (k : ℕ) := Complex.exp (frequency k / (r : ℂ) * (v : ℂ))
  let term (v : ℝ) (k : ℕ) := (rootCoeff r k * phase v k).re
  let total (v : ℝ) := (∑' k, rootCoeff r k * phase v k).re
  have hsum (v : ℝ) : HasSum (term v) (total v) := root_series_hasSum hRH hr v
  have hparts := (((hsum (u + h)).sub (hsum u)).mul_left (Real.exp (-(s * h)))).add
    (((hsum (u - h)).sub (hsum u)).mul_left (Real.exp (s * h)))
  have hw : HasSum weight firstLiMass := by
    unfold weight
    simpa only [coeff_real hRH, Complex.ofReal_re] using Complex.hasSum_re actualCoeff_hasSum
  have hmajor := ((cosine_difference_hasSum hRH (h / r)).mul_left (-r)).add
    (hw.mul_left (2 * r * Real.sinh (s * h) ^ 2))
  have hb (k : ℕ) : |weightedPair (fun v => term v k) s u h| ≤
      -r * (2 * (Real.cos ((actualZero k).im * (h / r)) - 1) * weight k) +
        (2 * r * Real.sinh (s * h) ^ 2) * weight k := by
    let x := (actualZero k).im * (h / r)
    have hadd (v w : ℝ) : phase (v + w) k = phase v k * phase w k := by
      simp only [phase, Complex.ofReal_add, mul_add, Complex.exp_add]
    have hpos : phase h k = Complex.exp ((x : ℂ) * Complex.I) := by
      simp only [phase, phase_eq hRH hr, x]
    have hneg : phase (-h) k = Complex.exp (((-x : ℝ) : ℂ) * Complex.I) := by
      simp only [phase, phase_eq hRH hr, neg_div, mul_neg, x]
    have hcollapse : weightedPair (fun v => term v k) s u h =
        (rootCoeff r k * phase u k * (2 * halfPair (s * h) x)).re := by
      rw [← paired_exp_eq]
      simp only [weightedPair, term, sub_eq_add_neg u h, hadd, hpos, hneg, mul_add, mul_sub,
        Complex.add_re, Complex.sub_re]
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, Complex.one_im, zero_mul, mul_zero, sub_zero, add_zero]
      ring
    have hcoef : ‖rootCoeff r k‖ ≤ r * weight k := by
      have heq : actualCoeff k = (weight k : ℂ) := coeff_real hRH k
      have hwk : 0 ≤ weight k := by unfold weight; positivity
      simpa only [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwk]
        using rootCoeff_bound hr k
    have hphase : ‖phase u k‖ = 1 := by
      dsimp only [phase]
      rw [phase_eq hRH hr, Complex.norm_exp_ofReal_mul_I]
    rw [hcollapse]
    calc
      _ ≤ ‖rootCoeff r k * phase u k * (2 * halfPair (s * h) x)‖ := Complex.abs_re_le_norm _
      _ = ‖rootCoeff r k‖ * (2 * ‖halfPair (s * h) x‖) := by
        rw [norm_mul, norm_mul, hphase, mul_one, norm_mul]
        norm_num
      _ ≤ (r * weight k) * (2 * ((1 - Real.cos x) + Real.sinh (s * h) ^ 2)) :=
        mul_le_mul hcoef (mul_le_mul_of_nonneg_left (norm_halfPair_le _ _) (by norm_num))
          (by positivity) (by unfold weight; positivity)
      _ = _ := by dsimp [x]; ring
  have htsum : |weightedPair total s u h| ≤
      -r * (2 * (K (h / r) - K 0)) + (2 * r * Real.sinh (s * h) ^ 2) * firstLiMass := by
    change HasSum _ (weightedPair total s u h) at hparts
    rw [← hparts.tsum_eq, ← hmajor.tsum_eq, ← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm hparts.summable.norm).trans
      (hparts.summable.norm.tsum_le_tsum (fun k => by
        simpa only [Real.norm_eq_abs, weightedPair] using hb k) hmajor.summable)
  have hscale (v : ℝ) : rootSignal r v = total v / s := rfl
  change |weightedPair (rootSignal r) s u h| ≤ _
  simp only [weightedPair, hscale, ← sub_div, ← mul_div_assoc, ← add_div, abs_div, abs_of_pos hs]
  apply div_le_div_of_nonneg_right _ hs.le
  change |weightedPair total s u h| ≤ _
  exact htsum.trans_eq (by ring)

private theorem sinh_small {s h : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 2)
    (hh : 0 ≤ h) (hh' : h ≤ 1) : |Real.sinh (s * h)| ≤ h := by
  have hx : 0 ≤ s * h := mul_nonneg hs hh
  have hx' : s * h ≤ h / 2 := by
    linarith only [mul_le_mul_of_nonneg_right hs' hh]
  have hpos : |Real.exp (s * h) - 1| ≤ 2 * (s * h) := by
    simpa only [abs_of_nonneg hx] using
      Real.abs_exp_sub_one_le (x := s * h) (by rw [abs_of_nonneg hx]; linarith)
  have hneg : |Real.exp (-(s * h)) - 1| ≤ 2 * (s * h) := by
    simpa only [abs_neg, abs_of_nonneg hx] using
      Real.abs_exp_sub_one_le (x := -(s * h))
        (by rw [abs_neg, abs_of_nonneg hx]; linarith)
  rw [Real.sinh_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := abs_sub (Real.exp (s * h) - 1) (Real.exp (-(s * h)) - 1)
  rw [sub_sub_sub_cancel_right] at h
  linarith only [h, hpos, hneg, hx']

private theorem cosh_small {s h : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 2)
    (hh : 0 ≤ h) (hh' : h ≤ 1) : 0 ≤ Real.cosh (s * h) - 1 ∧
      Real.cosh (s * h) - 1 ≤ h ^ 2 := by
  have hlow := Real.one_le_cosh (s * h)
  have habs := sinh_small hs hs' hh hh'
  have hsq := (sq_le_sq₀ (abs_nonneg _) hh).2 habs
  rw [sq_abs] at hsq
  exact ⟨sub_nonneg.mpr hlow, by
    nlinarith only [hsq, Real.cosh_sq_sub_sinh_sq (s * h),
      sq_nonneg (Real.cosh (s * h) - 1), hlow]⟩

private theorem integral_midpoint_sum {f : ℝ → ℝ} (hf : Continuous f) (L : ℝ) :
    (∫ t in (0 : ℝ)..L, f t) =
      ∫ h in (0 : ℝ)..(L / 2), f (L / 2 + h) + f (L / 2 - h) := by
  have hpair := integral_pair hf 0 L
  simp only [zero_add] at hpair
  have hcont : Continuous (fun h : ℝ => f (L / 2 + h) + f (L / 2 - h)) :=
    (hf.comp (continuous_const.add continuous_id)).add
      (hf.comp (continuous_const.sub continuous_id))
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const, sub_zero, sub_zero,
    smul_eq_mul, smul_eq_mul] at hpair
  linarith only [hpair]

private theorem weighted_average_pair {f : ℝ → ℝ} (hf : Continuous f) (s u L : ℝ)
    (hL : 0 < L) :
    (∫ t in (0 : ℝ)..L, Real.exp (-s * t) * f (u + t)) /
        (∫ t in (0 : ℝ)..L, Real.exp (-s * t)) - f (u + L / 2) =
      (∫ h in (0 : ℝ)..(L / 2), weightedPair f s (u + L / 2) h) /
        (∫ h in (0 : ℝ)..(L / 2), 2 * Real.cosh (s * h)) := by
  let w : ℝ → ℝ := fun t => Real.exp (-s * t)
  let v := u + L / 2
  have hw : Continuous w := by fun_prop
  have hF : Continuous (fun t => f (u + t)) := hf.comp (continuous_const.add continuous_id)
  have hW : 0 < ∫ t in (0 : ℝ)..L, w t :=
    intervalIntegral.integral_pos hL hw.continuousOn (fun t _ => (Real.exp_pos _).le)
      ⟨0, ⟨le_rfl, hL.le⟩, Real.exp_pos _⟩
  have hplus (h : ℝ) : w (L / 2 + h) = w (L / 2) * Real.exp (-(s * h)) := by
    simp only [w, mul_add, neg_mul, neg_add, Real.exp_add]
  have hminus (h : ℝ) : w (L / 2 - h) = w (L / 2) * Real.exp (s * h) := by
    dsimp only [w]
    rw [show -s * (L / 2 - h) = -s * (L / 2) + s * h by ring, Real.exp_add]
  have hm :
      (∫ t in (0 : ℝ)..L, w t) =
        w (L / 2) * ∫ h in (0 : ℝ)..(L / 2), 2 * Real.cosh (s * h) := by
    rw [integral_midpoint_sum hw, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro h _
    dsimp only
    rw [hplus, hminus, Real.cosh_eq]
    ring
  have hn :
      (∫ t in (0 : ℝ)..L, w t * (f (u + t) - f v)) =
        w (L / 2) * ∫ h in (0 : ℝ)..(L / 2), weightedPair f s v h := by
    have hg : Continuous (fun t => w t * (f (u + t) - f v)) :=
      hw.mul (hF.sub continuous_const)
    rw [integral_midpoint_sum hg, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro h _
    dsimp only
    rw [hplus, hminus, show u + (L / 2 + h) = v + h by dsimp [v]; ring,
      show u + (L / 2 - h) = v - h by dsimp [v]; ring]
    dsimp only [weightedPair]
    ring
  have hsub :
      (∫ t in (0 : ℝ)..L, w t * (f (u + t) - f v)) =
        (∫ t in (0 : ℝ)..L, w t * f (u + t)) - (∫ t in (0 : ℝ)..L, w t) * f v := by
    simp only [mul_sub]
    rw [intervalIntegral.integral_sub (f := fun t => w t * f (u + t))
      (g := fun t => w t * f v) ((hw.mul hF).intervalIntegrable _ _)
      ((hw.mul continuous_const).intervalIntegrable _ _), intervalIntegral.integral_mul_const]
  change (∫ t in (0 : ℝ)..L, w t * f (u + t)) / (∫ t in (0 : ℝ)..L, w t) - f v = _
  rw [div_sub' hW.ne', ← hsub, hn, hm, mul_div_mul_left _ _ (Real.exp_ne_zero _)]

/-- The normalized exponential root average has a uniform quadratic midpoint remainder.
The signed average of the window centered at zero gives the matching lower comparison. -/
theorem root_signal_exponential_midpoint_quadratic (hRH : RiemannHypothesis)
    {r : ℝ} (hr : 1 < r) :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    let G := fun L : ℝ => (L / (8 * s)) * (Real.log (1 / L) + Real.log (2 * r) - 2 * c + 1 / 2)
    let M := fun u L : ℝ =>
      (∫ t in (0 : ℝ)..L, Real.exp (-s * t) * rootSignal r (u + t)) /
        (∫ t in (0 : ℝ)..L, Real.exp (-s * t)) - rootSignal r (u + L / 2)
    ∃ C > 0, ∀ L : ℝ, 0 < L → L ≤ 1 / 4 →
      (∀ u : ℝ, |M u L| ≤ G L + C * L ^ 2) ∧
      G L - C * L ^ 2 ≤ M (-L / 2) L := by
  dsimp only
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  let G := fun L : ℝ => (L / (8 * s)) * (Real.log (1 / L) + Real.log (2 * r) - 2 * c + 1 / 2)
  let A := fun h : ℝ => (h / s) * (Real.log (1 / h) + (Real.log r - 2 * c))
  have hr0 : 0 < r := by linarith
  have hs : 0 < s := by
    dsimp [s]
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  have hs' : s ≤ 1 / 2 := sub_le_self _ (by positivity)
  have hA : Continuous A := continuous_cusp_profile s (Real.log r - 2 * c)
  have hS := (root_signal_uniformContinuous hRH hr).continuous
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image hA.abs).bddAbove
  have hB0 : 0 ≤ B :=
    (abs_nonneg (A 0)).trans (hB ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)
  obtain ⟨D, hD, hcusp⟩ := root_signal_symmetric_cusp hRH hr
  let O := 2 * (r - 1) * firstLiMass / s
  let U := 4 / (r * s) + 2 * r * firstLiMass / s
  let V := B + 2 * D + O
  have hO : 0 ≤ O := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hr.le)) firstLiMass_pos.le) hs.le
  have hm : 0 < firstLiMass := firstLiMass_pos
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hpupper (u h : ℝ) (hh : 0 < h) (hh' : h ≤ 1 / 8) :
      |weightedPair (rootSignal r) s u h| ≤ A h + U * h ^ 2 := by
    let t := h / r
    have ht : 0 < t := div_pos hh hr0
    have ht' : t ≤ 1 / 2 := (div_le_iff₀ hr0).2 (by linarith)
    have hlog : Real.log (1 / h) + Real.log r = -Real.log t := by
      rw [one_div, Real.log_inv, Real.log_div hh.ne' hr0.ne']
      ring
    have heq : (2 * r) * (K 0 - K t) / s - A h = -(2 * r) * R t / s := by
      dsimp only [A]
      rw [show Real.log (1 / h) + (Real.log r - 2 * c) = -Real.log t - 2 * c by linarith,
        R, K_zero]
      have htScale : r * t = h := by dsimp [t]; field_simp
      rw [← htScale]
      ring
    have he := (abs_le.mp (cusp_remainder_bound ht ht')).1
    have hk : -(2 * r) * R t / s ≤ 4 / (r * s) * h ^ 2 := by
      calc
        -(2 * r) * R t / s = (2 * r) * (-R t) / s := by ring
        _ ≤ (2 * r) * (2 * t ^ 2) / s :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith only [he] : -R t ≤ _) (by positivity)) hs.le
        _ = _ := by dsimp [t]; field_simp [hr0.ne', hs.ne'] <;> norm_num
    have hsh := (sq_le_sq₀ (abs_nonneg _) hh.le).2
      (sinh_small hs.le hs' hh.le (by linarith))
    rw [sq_abs] at hsh
    have hpert := mul_le_mul_of_nonneg_left hsh
      (show 0 ≤ 2 * r * firstLiMass / s by positivity)
    have hp := weighted_root_pair_le hRH hr u h
    change |weightedPair (rootSignal r) s u h| ≤
      ((2 * r) * (K 0 - K t) + (2 * r * Real.sinh (s * h) ^ 2) * firstLiMass) / s at hp
    rw [add_div, show (2 * r * Real.sinh (s * h) ^ 2) * firstLiMass / s =
      (2 * r * firstLiMass / s) * Real.sinh (s * h) ^ 2 by ring] at hp
    dsimp only [U]
    rw [add_mul]
    linarith only [hp, hk, heq, hpert]
  have hplower (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1 / 8) :
      A h - V * h ^ 2 ≤ weightedPair (rootSignal r) s 0 h := by
    let f := rootSignal r
    let d := f h + f (-h) - 2 * f 0
    let o := f h - f (-h)
    have hc := cosh_small hs.le hs' hh.le (by linarith)
    have hcosh0 : 0 ≤ Real.cosh (s * h) := (Real.cosh_pos _).le
    have hcosh2 : Real.cosh (s * h) ≤ 2 := by
      nlinarith [hc.2, mul_nonneg hh.le (show 0 ≤ 1 - h by linarith)]
    have hbound : |A h| ≤ B := hB ⟨h, ⟨hh.le, by linarith⟩, rfl⟩
    have hAprod : -(B * h ^ 2) ≤ (Real.cosh (s * h) - 1) * A h := by
      have hp := mul_nonneg hc.1 (show 0 ≤ A h + B by linarith only [(abs_le.mp hbound).1])
      have hq := mul_le_mul_of_nonneg_left hc.2 hB0
      nlinarith only [hp, hq]
    have hd : A h - D * h ^ 2 ≤ d := by
      have hb := (abs_le.mp (hcusp h hh (by linarith : h ≤ r / 2))).1
      change -(D * h ^ 2) ≤ d - h / s * (Real.log (1 / h) + Real.log r - 2 * c) at hb
      dsimp [A]
      linarith only [hb]
    have hcoshD := mul_le_mul_of_nonneg_left hd hcosh0
    have hDprod := mul_le_mul_of_nonneg_right hcosh2
      (show 0 ≤ D * h ^ 2 by positivity)
    have ho : |o| ≤ O * h := by
      have hb := odd_root_increment hRH hr hh.le
      change |o| ≤ 2 * (r - 1) * firstLiMass * h / s at hb
      simpa only [O, div_mul_eq_mul_div] using hb
    have hsinhO : Real.sinh (s * h) * o ≤ O * h ^ 2 := by
      calc
        _ ≤ |Real.sinh (s * h) * o| := le_abs_self _
        _ = |Real.sinh (s * h)| * |o| := abs_mul _ _
        _ ≤ h * (O * h) := mul_le_mul (sinh_small hs.le hs' hh.le (by linarith))
          ho (abs_nonneg _) hh.le
        _ = _ := by ring
    have hpair : weightedPair f s 0 h = Real.cosh (s * h) * d - Real.sinh (s * h) * o := by
      simp only [weightedPair, zero_add, zero_sub, d, o, Real.cosh_eq, Real.sinh_eq]
      ring
    change A h - V * h ^ 2 ≤ weightedPair f s 0 h
    rw [hpair]
    dsimp only [V]
    nlinarith only [hcoshD, hAprod, hDprod, hsinhO]
  refine ⟨U + V + B + 1, by positivity, fun L hL hL' => ?_⟩
  let W := ∫ h in (0 : ℝ)..(L / 2), 2 * Real.cosh (s * h)
  let N := fun u : ℝ => ∫ h in (0 : ℝ)..(L / 2), weightedPair (rootSignal r) s u h
  have hM (u : ℝ) := weighted_average_pair hS s u L hL
  change
    (∀ u, |(∫ t in (0 : ℝ)..L, Real.exp (-s * t) * rootSignal r (u + t)) /
        (∫ t in (0 : ℝ)..L, Real.exp (-s * t)) - rootSignal r (u + L / 2)| ≤
          G L + (U + V + B + 1) * L ^ 2) ∧
    G L - (U + V + B + 1) * L ^ 2 ≤
      (∫ t in (0 : ℝ)..L, Real.exp (-s * t) * rootSignal r (-L / 2 + t)) /
        (∫ t in (0 : ℝ)..L, Real.exp (-s * t)) - rootSignal r (-L / 2 + L / 2)
  simp_rw [hM]
  change (∀ u, |N (u + L / 2) / W| ≤ G L + (U + V + B + 1) * L ^ 2) ∧
    G L - (U + V + B + 1) * L ^ 2 ≤ N (-L / 2 + L / 2) / W
  rw [show -L / 2 + L / 2 = (0 : ℝ) by ring]
  have hhalf : 0 ≤ L / 2 := by positivity
  have hWc : Continuous (fun h => 2 * Real.cosh (s * h)) := by fun_prop
  have hWlow : L ≤ W := by
    calc
      _ = ∫ _ in (0 : ℝ)..(L / 2), (2 : ℝ) := by simp [smul_eq_mul]
      _ ≤ W := intervalIntegral.integral_mono_on hhalf
        (continuous_const.intervalIntegrable _ _) (hWc.intervalIntegrable _ _)
        (fun h _ => by linarith only [Real.one_le_cosh (s * h)])
  have hWhigh : W ≤ L + L ^ 3 := by
    calc
      W ≤ ∫ _ in (0 : ℝ)..(L / 2), 2 * (1 + L ^ 2) := by
        apply intervalIntegral.integral_mono_on hhalf
          (hWc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
        intro h hh
        have hc := (cosh_small hs.le hs' hh.1 (by linarith [hh.2])).2
        have hq := (sq_le_sq₀ hh.1 hL.le).2 (by linarith [hh.2])
        linarith only [hc, hq]
      _ = _ := by simp [smul_eq_mul]; ring
  have hW : 0 < W := hL.trans_le hWlow
  have hAc : (∫ h in (0 : ℝ)..(L / 2), A h) = L * G L := by
    dsimp [A, G]
    rw [integral_cusp_profile hL, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hr0.ne']
    ring
  have hGnorm : |G L| ≤ B := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (f := A)
      (a := 0) (b := L / 2) (C := B) (fun h hh => by
        rw [uIoc_of_le hhalf] at hh
        exact hB ⟨h, ⟨hh.1.le, by linarith [hh.2]⟩, Real.norm_eq_abs _ ▸ rfl⟩)
    rw [Real.norm_eq_abs, hAc, abs_mul, abs_of_pos hL, sub_zero, abs_of_nonneg hhalf] at hi
    exact (le_of_mul_le_mul_left (by nlinarith only [hi, mul_nonneg hB0 hL.le]) hL)
  have hNc (u : ℝ) : Continuous (weightedPair (rootSignal r) s u) := by
    unfold weightedPair
    fun_prop
  have hNupper (u : ℝ) : |N u| ≤ L * G L + (L / 2) * (U * L ^ 2) := by
    have hi := intervalIntegral.norm_integral_le_integral_norm
      (f := weightedPair (rootSignal r) s u) (μ := volume) hhalf
    simp only [Real.norm_eq_abs] at hi
    apply hi.trans
    calc
      _ ≤ ∫ h in (0 : ℝ)..(L / 2), A h + U * L ^ 2 := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hhalf
          ((hNc u).abs.intervalIntegrable _ _) ((hA.add continuous_const).intervalIntegrable _ _)
        intro h hh
        have hq := (sq_le_sq₀ hh.1.le hL.le).2 (by linarith [hh.2])
        exact (hpupper u h hh.1 (by linarith [hh.2])).trans
          (add_le_add_right (mul_le_mul_of_nonneg_left hq hU) _)
      _ = _ := by
        rw [intervalIntegral.integral_add (hA.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _), hAc, intervalIntegral.integral_const,
          sub_zero, smul_eq_mul]
  have hNlower : L * G L - (L / 2) * (V * L ^ 2) ≤ N 0 := by
    calc
      _ = ∫ h in (0 : ℝ)..(L / 2), A h - V * L ^ 2 := by
        rw [intervalIntegral.integral_sub (hA.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _), hAc, intervalIntegral.integral_const,
          sub_zero, smul_eq_mul]
      _ ≤ N 0 := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hhalf
          ((hA.sub continuous_const).intervalIntegrable _ _) ((hNc 0).intervalIntegrable _ _)
        intro h hh
        have hq := (sq_le_sq₀ hh.1.le hL.le).2 (by linarith [hh.2])
        exact (sub_le_sub_left (mul_le_mul_of_nonneg_left hq hV) _).trans
          (hplower h hh.1 (by linarith [hh.2]))
  have hupper (u : ℝ) : |N u / W| ≤ G L + U * L ^ 2 := by
    rw [abs_div, abs_of_pos hW]
    calc
      _ ≤ |N u| / L := div_le_div_of_nonneg_left (abs_nonneg _) hL hWlow
      _ ≤ _ := (div_le_iff₀ hL).2 (by
        nlinarith only [hNupper u, mul_nonneg hL.le (mul_nonneg hU (sq_nonneg L))])
  have hlower : G L - (V + B) * L ^ 2 ≤ N 0 / W := by
    apply (le_div_iff₀ hW).2
    have hnorm : G L * (W - L) ≤ B * L ^ 3 :=
      mul_le_mul ((le_abs_self _).trans hGnorm) (by linarith only [hWhigh])
        (sub_nonneg.mpr hWlow) hB0
    have hscale := mul_le_mul_of_nonneg_left hWlow
      (show 0 ≤ (V + B) * L ^ 2 by positivity)
    nlinarith only [hNlower, hnorm, hscale,
      mul_nonneg hL.le (mul_nonneg hV (sq_nonneg L))]
  exact ⟨fun u => (hupper _).trans (by
    nlinarith only [mul_nonneg (show 0 ≤ V + B + 1 by positivity) (sq_nonneg L)]),
    (show G L - (U + V + B + 1) * L ^ 2 ≤ G L - (V + B) * L ^ 2 by
      nlinarith only [mul_nonneg (show 0 ≤ U + 1 by positivity) (sq_nonneg L)]).trans hlower⟩

#print axioms root_signal_exponential_midpoint_quadratic

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
