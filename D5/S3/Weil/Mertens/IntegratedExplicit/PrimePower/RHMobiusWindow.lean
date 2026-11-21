/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusWindow
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform all-orders prime-only window expansion under RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootSpectrum
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.MobiusCutoff

/-! Möbius truncation, actual root spectra and one common threshold for the prime window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Chebyshev Real ArithmeticFunction MeasureTheory Set
open scoped ArithmeticFunction.Moebius
open Finset (sum_congr sum_le_sum)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.Mertens.IntegratedExplicit
open RHSharpActualEnvelope (G abs_G_sub_normalized_actualH_le)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

private theorem qError_continuous_from_one : ContinuousOn qError (Ici 1) := by
  have hQ : ContinuousOn Q (Ici 1) :=
    chebyshev_error_kernel_integrable.continuousOn_Ici_primitive_Ioi
  have hlog : ContinuousOn Real.log (Ici (1 : ℝ)) :=
    Real.continuousOn_log.mono fun x hx => ne_of_gt (zero_lt_one.trans_le hx)
  exact hQ.add (Complex.continuous_re.comp_continuousOn
    (zeroTail_continuous.comp_continuousOn hlog))

private theorem qError_bounded_from_one :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x → |qError x| ≤ D * x ^ (-1 : ℝ) := by
  let f (x : ℝ) := |qError x| * x
  have hf : ContinuousOn f (Icc 1 2) :=
    (qError_continuous_from_one.mono fun _ hx => hx.1).abs.mul continuousOn_id
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨1, left_mem_Icc.mpr one_le_two⟩ hf
  have hC : 0 ≤ C := abs_nonneg _
  have hf0 : 0 ≤ f y := mul_nonneg (abs_nonneg _) (zero_le_one.trans hy.1)
  let D := C + f y + 1
  have hD : C ≤ D := by dsimp [D]; linarith
  refine ⟨D, by dsimp [D]; linarith, fun x hx => ?_⟩
  rw [Real.rpow_neg_one]
  by_cases hx2 : 2 ≤ x
  · have hb := qError_bound hx2
    rw [Real.rpow_neg_one] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hD (inv_nonneg.mpr (zero_le_one.trans hx)))
  · have hb : f x ≤ f y := hmax ⟨hx, le_of_not_ge hx2⟩
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    rw [← div_eq_mul_inv, le_div_iff₀ hx0]
    change f x ≤ D
    exact hb.trans (by dsimp [D]; linarith)

private theorem weighted_bound_from_one {f : ℝ → ℝ} {y b d D : ℝ} (hy : 1 ≤ y) (hbd : 1 < b + d)
    (hc : ContinuousOn f (Ici 1))
    (hb : ∀ s, 1 ≤ s → |f s| ≤ D * s ^ (-d)) :
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
          («μ» := volume.restrict (Ioi y)))
    _ ≤ ∫ s in Ioi y, D * s ^ (-(b + d)) :=
      setIntegral_mono_on hf.norm hmajor measurableSet_Ioi hcomp
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hy0,
        show -(b + d) + 1 = 1 - (b + d) by ring,
        show 1 - (b + d) = -(b + d - 1) by ring]
      rw [neg_div, div_neg, neg_neg]
      ring

private theorem root_centered_error_from_one {D r : ℝ} (hr : 1 < r)
    (hD : ∀ x : ℝ, 1 ≤ x → |qError x| ≤ D * x ^ (-1 : ℝ))
    {v : ℝ} (hv : 0 ≤ v) :
    |centered r (Real.exp (r * v)) - rootDensity r (r * v)| ≤
      (2 * r - 1) * D * Real.exp (-(r * v) / 2) := by
  let y := Real.exp v
  let x := Real.exp (r * v)
  let s := Real.exp ((1 - r / 2) * v)
  let w := Real.exp ((r - 1) * v)
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : 1 ≤ x := (Real.exp_zero : Real.exp (0 : ℝ) = 1) ▸
    Real.exp_le_exp.mpr (mul_nonneg hr0.le hv)
  have hy : 1 ≤ y := Real.one_le_exp_iff.mpr hv
  have hy0 : 0 < y := Real.exp_pos _
  have hroot : x ^ r⁻¹ = y := by
    dsimp only [x, y]
    rw [← Real.exp_mul]
    congr 1
    field_simp
  have hscale₁ : Real.sqrt x * y ^ (1 - r) = s := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [x, y, s]
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hscale₂ : s * w = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [s, w, x]
    rw [← Real.exp_add, ← Real.exp_mul]
    congr 1
    ring
  have hdecay : s * y⁻¹ = Real.exp (-(r * v) / 2) := by
    dsimp only [s, y]
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have hcut := centered_root_tail (r := r) hr.le (zero_lt_one.trans_le hx1)
  dsimp only at hcut
  change centered r x = _ at hcut
  rw [hroot] at hcut
  have h := root_spectral_transform hr v
  dsimp only at h
  change r * s * (-(zeroTail (Real.log y)).re + (r - 1) * w *
      (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re)) = _ at h
  obtain ⟨he, hb⟩ := weighted_bound_from_one (f := qError) (b := r) (d := 1) hy (by linarith)
    qError_continuous_from_one hD
  have hZ := (weighted_zero_tail hr v).1
  have hz : IntegrableOn (fun t => t ^ (-r) * (zeroTail (Real.log t)).re) (Ioi y) := by
    have hRe := hZ.re
    change IntegrableOn (fun t : ℝ => ((t ^ (-r)) • zeroTail (Real.log t)).re) (Ioi y) at hRe
    simpa only [Complex.real_smul, Complex.re_ofReal_mul] using hRe
  have hsplit : (∫ t in Ioi y, t ^ (-r) * Q t) =
      (∫ t in Ioi y, t ^ (-r) * qError t) -
        (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re) := by
    rw [← integral_sub (f := fun t => t ^ (-r) * qError t)
      (g := fun t => t ^ (-r) * (zeroTail (Real.log t)).re) he hz]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by unfold qError; ring)
  have hdiff : centered r x - rootDensity r (r * v) =
      r * s * (qError y - (r - 1) * w * (∫ t in Ioi y, t ^ (-r) * qError t)) := by
    rw [hcut, ← h, hsplit]
    change _ = r * s * (Q y + (zeroTail (Real.log y)).re - (r - 1) * w *
      (∫ t in Ioi y, t ^ (-r) * qError t))
    linear_combination r * Q y * hscale₁ + r * (r - 1) *
      ((∫ t in Ioi y, t ^ (-r) * qError t) -
        (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re)) * hscale₂
  have hs0 : 0 < s := Real.exp_pos _
  have hw0 : 0 < w := Real.exp_pos _
  have hweight : w * y ^ (-r) = y⁻¹ := by
    dsimp only [w, y]
    rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  have hb' : |∫ t in Ioi y, t ^ (-r) * qError t| ≤ D / r * y ^ (-r) := by
    simpa only [show r + 1 - 1 = r by ring, show 1 - (r + 1) = -r by ring] using hb
  change |centered r x - rootDensity r (r * v)| ≤ _
  rw [hdiff, abs_mul, abs_of_nonneg (mul_nonneg hr0.le hs0.le)]
  calc
    _ ≤ r * s * (|qError y| + (r - 1) * w * |∫ t in Ioi y, t ^ (-r) * qError t|) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hr0.le hs0.le)
      exact (abs_sub _ _).trans_eq (by rw [abs_mul,
        abs_of_nonneg (mul_nonneg (by linarith) hw0.le)])
    _ ≤ r * s * (D * y⁻¹ + (r - 1) * w * (D / r * y ^ (-r))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hr0.le hs0.le)
      rw [← Real.rpow_neg_one]
      exact add_le_add (hD _ hy) (mul_le_mul_of_nonneg_left hb'
        (mul_nonneg (by linarith) hw0.le))
    _ = _ := by
      rw [show (r - 1) * w * (D / r * y ^ (-r)) = (r - 1) * (D / r) *
        (w * y ^ (-r)) by ring, hweight, ← hdecay]
      field_simp
      ring


private theorem root_density_rh_majorant (hRH : RiemannHypothesis) {r u : ℝ}
    (hr : 1 < r) :
    |rootDensity r u| ≤ r * firstLiMass * Real.exp (((2 * r)⁻¹ - 1 / 2) * u) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  let weight := Real.exp (((2 * r)⁻¹ - 1 / 2) * u)
  have hMode (k : ℕ) : ‖rootMode r u k‖ ≤ (r * ‖actualCoeff k‖) * weight := by
    have hRe : (actualZero k / (r : ℂ)).re = (2 * r)⁻¹ := by
      simp [Complex.div_re, Complex.normSq_ofReal, RHSharpActualEnvelope.on_line hRH k]
      field_simp
    rw [rootMode, norm_mul, Complex.norm_exp, mul_comm _ (u : ℂ), Complex.re_ofReal_mul,
      Complex.sub_re, hRe]
    have hhalf : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num
    rw [hhalf, mul_comm u]
    exact mul_le_mul_of_nonneg_right (rootCoeff_bound hr k) (Real.exp_nonneg _)
  change |(∑' k, rootMode r u k).re| ≤ (r * firstLiMass) * weight
  have hsum := ((RHSharpActualEnvelope.coeff_norm_hasSum hRH).mul_left r).mul_right weight
  exact (Complex.abs_re_le_norm _).trans (tsum_of_norm_bounded hsum hMode)

private def orderRate (m : ℕ) : ℝ := 1 / 2 - (m + 1 : ℝ)⁻¹

private def capturedSpectrum (m n : ℕ) (u : ℝ) : ℝ :=
  if 2 * n < m + 1 then rootDensity (n : ℝ) u else 0

private theorem centered_after_spectrum (hRH : RiemannHypothesis)
    {D : ℝ} (hD0 : 0 < D) (hD : ∀ x : ℝ, 1 ≤ x → |qError x| ≤ D * x ^ (-1 : ℝ))
    {m n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 ≤ u) :
    |centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u| ≤
      (n : ℝ) * (2 * D + firstLiMass) * Real.exp (-(orderRate m) * u) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hn1
  have hu' : 0 ≤ u / (n : ℝ) := div_nonneg hu hn0.le
  have hc := root_centered_error_from_one hn1 hD hu'
  rw [mul_div_cancel₀ _ hn0.ne'] at hc
  have hrate : orderRate m ≤ 1 / 2 := by
    unfold orderRate
    have hp : 0 ≤ ((m + 1 : ℝ))⁻¹ := by positivity
    linarith
  have hexp : Real.exp (-u / 2) ≤ Real.exp (-(orderRate m) * u) := by
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hrate) hu])
  have hcenter : |centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u| ≤
      (n : ℝ) * (2 * D) * Real.exp (-(orderRate m) * u) := by
    refine hc.trans (mul_le_mul ?_ hexp (Real.exp_nonneg _) (by positivity))
    nlinarith
  have hMass : 0 ≤ firstLiMass := mass_nonneg hRH
  unfold capturedSpectrum
  split_ifs with hsmall
  · exact hcenter.trans (mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hn0.le hMass])
      (Real.exp_nonneg _))
  · have hidx : (m + 1 : ℝ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast (le_of_not_gt hsmall)
    have hm₀ : 0 < (m + 1 : ℝ) := by positivity
    have hinv := inv_anti₀ hm₀ hidx
    have hdecay :
        Real.exp (((2 * (n : ℝ))⁻¹ - 1 / 2) * u) ≤ Real.exp (-(orderRate m) * u) := by
      exact Real.exp_le_exp.mpr (by
        unfold orderRate
        nlinarith [mul_nonneg (sub_nonneg.mpr hinv) hu])
    have h := root_density_rh_majorant hRH (u := u) hn1
    rw [sub_zero, ← sub_add_cancel (centered _ _) (rootDensity _ _)]
    calc
      _ ≤ |centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u| +
          |rootDensity (n : ℝ) u| := abs_add_le _ _
      _ ≤ (n : ℝ) * (2 * D) * Real.exp (-(orderRate m) * u) +
          (n : ℝ) * firstLiMass * Real.exp (-(orderRate m) * u) :=
        add_le_add hcenter (h.trans (mul_le_mul_of_nonneg_left hdecay (by positivity)))
      _ = _ := by ring

private def arithmeticRate (n : ℕ) : ℝ := 1 / 2 - (n : ℝ)⁻¹

private def retainedDensity (m n : ℕ) (u : ℝ) : ℝ :=
  -(μ n : ℝ) * ((n : ℝ) / ((n : ℝ) - 1) *
    Real.exp (-(arithmeticRate n) * u) + capturedSpectrum m n u)

private theorem integrated_mobius_linear {m : ℕ} (hm : 2 ≤ m) {u : ℝ}
    (hx : 2 ≤ Real.exp u) :
    |Real.sqrt (Real.exp u) * (primeTail (Real.exp u) - Q (Real.exp u)) -
      ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * (Real.sqrt (Real.exp u) *
        (∫ t in Ioi (Real.exp u), psi (t ^ (n : ℝ)⁻¹) / t ^ 2))| ≤
      (Real.log 4 + 4) * 4 * (1 + 2 / Real.log 2) * (m : ℝ) *
        Real.exp (-(orderRate m) * u) := by
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c := (Real.log 4 + 4) * 2
  let p := (m + 1 : ℝ)⁻¹
  have hp₀ : 0 ≤ p := by positivity
  have hp₃ : p ≤ 1 / 3 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by linarith)
  have hcoef : c * (1 + (m + 1 : ℝ) / Real.log 2) / (1 - p) ≤
      (Real.log 4 + 4) * 4 * (1 + 2 / Real.log 2) * (m : ℝ) := by
    have hc : 0 ≤ c * (1 + (m + 1 : ℝ) / Real.log 2) := by positivity
    have hlinear : 1 + (m + 1 : ℝ) / Real.log 2 ≤ (1 + 2 / Real.log 2) * (m : ℝ) := by
      have hdiv := div_le_div_of_nonneg_right (show (m : ℝ) + 1 ≤ 2 * m by linarith) hlog.le
      rw [mul_div_right_comm] at hdiv
      nlinarith [hdiv]
    calc
      _ ≤ c * (1 + (m + 1 : ℝ) / Real.log 2) * 2 := by
        apply (div_le_iff₀ (by linarith : 0 < 1 - p)).mpr
        nlinarith only [mul_nonneg hc (show 0 ≤ 2 * (1 - p) - 1 by linarith)]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hlinear (show 0 ≤ c * 2 by positivity)
        dsimp [c]
        nlinarith only [h]
  have H := integrated_mobius_truncation hm hx
  rw [← Real.exp_mul] at H
  have heq : u * (1 / (m + 1 : ℝ) - 1 / 2) = -(orderRate m) * u := by
    unfold orderRate
    rw [one_div]
    ring
  rw [heq] at H
  rw [mul_sub, Finset.mul_sum] at H
  simp_rw [one_div] at H
  have he :
      Real.sqrt (Real.exp u) * (primeTail (Real.exp u) - Q (Real.exp u)) -
        ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * (Real.sqrt (Real.exp u) *
          (∫ t in Ioi (Real.exp u), psi (t ^ (n : ℝ)⁻¹) / t ^ 2)) =
      Real.sqrt (Real.exp u) * (primeTail (Real.exp u) - Q (Real.exp u)) -
        ∑ n ∈ Finset.Icc 2 m, Real.sqrt (Real.exp u) * ((μ n : ℝ) *
          (∫ t in Ioi (Real.exp u), psi (t ^ (n : ℝ)⁻¹) / t ^ 2)) := by
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [he]
  exact H.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _))

private theorem all_orders_density_bound (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, Real.log 2 ≤ u →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
        K * (m : ℝ)^2 * Real.exp (-(orderRate m) * u) := by
  obtain ⟨D, hD0, hD⟩ := qError_bounded_from_one
  let A := (Real.log 4 + 4) * 4 * (1 + 2 / Real.log 2)
  let L := 2 * D + firstLiMass
  have hA : 0 < A := by dsimp [A]; positivity
  have hL : 0 < L := by dsimp [L]; linarith [mass_nonneg hRH]
  have hC : 0 ≤ C := abs_nonneg _
  refine ⟨A + L + C, by linarith, fun m hm u hu => ?_⟩
  let x := Real.exp u
  let W := Real.exp (-(orderRate m) * u)
  let T (n : ℕ) := Real.sqrt x * (∫ t in Ioi x, psi (t ^ (n : ℝ)⁻¹) / t ^ 2)
  let e (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) x - capturedSpectrum m n u)
  let R := Real.sqrt x * (primeTail x - Q x) - ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * T n
  let E := G u - Real.exp (-u / 2) * (actualH u).re
  have hx : 2 ≤ x := by
    have hexp : Real.exp (Real.log 2) ≤ Real.exp u := Real.exp_le_exp.mpr hu
    simpa only [x, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hexp
  have hx0 : 0 < x := by linarith
  have hu0 : 0 ≤ u := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hu
  have hW : 0 < W := Real.exp_pos _
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hR : |R| ≤ A * (m : ℝ) * W := integrated_mobius_linear hm hx
  have hE : |E| ≤ C * W := by
    refine (abs_G_sub_normalized_actualH_le hu0).le.trans ?_
    dsimp only [W]
    rw [mul_comm (Real.exp _)]
    apply mul_le_mul (le_abs_self _) _ (Real.exp_nonneg _) hC
    apply Real.exp_le_exp.mpr
    unfold orderRate
    nlinarith [mul_nonneg (show 0 ≤ (m + 1 : ℝ)⁻¹ by positivity) hu0]
  have he (n : ℕ) (hn : n ∈ Finset.Icc 2 m) : |e n| ≤ (m : ℝ) * L * W := by
    have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := n)
    have hnM : (n : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    dsimp only [e]
    rw [abs_mul, abs_neg]
    exact (mul_le_of_le_one_left (abs_nonneg _) hμ).trans
      ((centered_after_spectrum hRH hD0 hD (Finset.mem_Icc.mp hn).1 hu0).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnM hL.le) hW.le))
  have hsum : |∑ n ∈ Finset.Icc 2 m, e n| ≤ L * (m : ℝ)^2 * W := by
    have hcard : ((Finset.Icc 2 m).card : ℝ) ≤ m := by
      exact_mod_cast (show (Finset.Icc 2 m).card ≤ m by rw [Nat.card_Icc]; omega)
    calc
      _ ≤ ∑ n ∈ Finset.Icc 2 m, |e n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.Icc 2 m, (m : ℝ) * L * W := Finset.sum_le_sum he
      _ = ((Finset.Icc 2 m).card : ℝ) * ((m : ℝ) * L * W) := by simp
      _ ≤ _ := (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq (by ring)
  have hterms (n : ℕ) (hn : n ∈ Finset.Icc 2 m) :
      (μ n : ℝ) * T n + retainedDensity m n u + e n = 0 := by
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by have := (Finset.mem_Icc.mp hn).1; omega)
    have ht := root_tail_main (r := (n : ℝ)) hn1 hx0
    change T n = (n : ℝ) / ((n : ℝ) - 1) * x ^ ((n : ℝ)⁻¹ - 1 / 2) + centered (n : ℝ) x at ht
    have hpow : x ^ ((n : ℝ)⁻¹ - 1 / 2) = Real.exp (-(arithmeticRate n) * u) := by
      dsimp only [x, arithmeticRate]
      rw [← Real.exp_mul]
      congr 1
      ring
    rw [ht, hpow]
    unfold retainedDensity e
    ring
  have hs : (∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * T n) +
      (∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) +
      (∑ n ∈ Finset.Icc 2 m, e n) = 0 := by
    simp_rw [← Finset.sum_add_distrib]
    exact (Finset.sum_congr rfl hterms).trans Finset.sum_const_zero
  have hsplit : rootWindowDensity u - ∑ n ∈ Finset.Icc 2 m, retainedDensity m n u =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E - 2 := by
    dsimp only [R, E, rootWindowDensity, x]
    linear_combination -hs
  rw [show rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2) =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E by linarith only [hsplit]]
  have hm₁ : (1 : ℝ) ≤ m := by linarith
  have hms : (m : ℝ) ≤ (m : ℝ)^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hm₁) (show 0 ≤ (m : ℝ) by positivity)]
  have hms₁ : (1 : ℝ) ≤ (m : ℝ)^2 := hm₁.trans hms
  calc
    _ ≤ |R| + |∑ n ∈ Finset.Icc 2 m, e n| + |E| := by
      calc
        _ ≤ |-R + ∑ n ∈ Finset.Icc 2 m, e n| + |E| := abs_add_le _ _
        _ ≤ (|-R| + |∑ n ∈ Finset.Icc 2 m, e n|) + |E| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ = _ := by rw [abs_neg]
    _ ≤ A * (m : ℝ)^2 * W + L * (m : ℝ)^2 * W + C * (m : ℝ)^2 * W :=
      add_le_add (add_le_add (hR.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hms hA.le) hW.le)) hsum)
        (hE.trans (mul_le_mul_of_nonneg_right
          (by simpa using mul_le_mul_of_nonneg_left hms₁ hC) hW.le))
    _ = _ := by ring

private def powerGap (s a B : ℝ) : ℝ := a ^ (-s) - B ^ (-s)

private def arithmeticPrimitive (n : ℕ) (a B : ℝ) : ℝ :=
  -(μ n : ℝ) * (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
    powerGap (arithmeticRate n) a B

private def capturedPrimitive (m n : ℕ) (a B : ℝ) : ℝ :=
  if 2 * n < m + 1 then -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a) else 0

private theorem root_rate_positive {n : ℕ} (hn : 3 ≤ n) : 0 < arithmeticRate n := by
  have hn₀ : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have hi := inv_strictAnti₀ (show (0 : ℝ) < 2 by norm_num) hn₀
  exact sub_pos.mpr (by simpa only [one_div] using hi)

private theorem retainedDensity_integral {m n : ℕ} (hn : 2 ≤ n) {a B : ℝ}
    (ha : 0 < a) (hB : 0 < B) :
    IntervalIntegrable (retainedDensity m n) volume (Real.log a) (Real.log B) ∧
      (∫ u in Real.log a..Real.log B, retainedDensity m n u) =
        (if n = 2 then 2 * (Real.log B - Real.log a) else arithmeticPrimitive n a B) +
          capturedPrimitive m n a B := by
  have hn₁ : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hi : IntervalIntegrable (fun u : ℝ => (n : ℝ) / ((n : ℝ) - 1) *
      Real.exp (-(arithmeticRate n) * u)) volume (Real.log a) (Real.log B) :=
    (by fun_prop : Continuous (fun u : ℝ => (n : ℝ) / ((n : ℝ) - 1) *
      Real.exp (-(arithmeticRate n) * u))).intervalIntegrable _ _
  have hs : IntervalIntegrable (capturedSpectrum m n) volume (Real.log a) (Real.log B) ∧
      -(μ n : ℝ) * (∫ u in Real.log a..Real.log B, capturedSpectrum m n u) =
        capturedPrimitive m n a B := by
    by_cases h : 2 * n < m + 1
    · have heq : capturedSpectrum m n = rootDensity (n : ℝ) := by
        funext u
        simp [capturedSpectrum, h]
      obtain ⟨hi', he⟩ := root_density_integral hn₁ (Real.log a) (Real.log B)
      rw [heq, he, Real.exp_log hB, Real.exp_log ha, capturedPrimitive, ite_eq_left h]
      exact ⟨hi', rfl⟩
    · have heq : capturedSpectrum m n = fun _ => 0 := by
        funext u
        simp [capturedSpectrum, h]
      rw [heq, capturedPrimitive, ite_eq_right h]
      exact ⟨intervalIntegrable_const, by simp⟩
  refine ⟨(hi.add hs.1).const_mul _, ?_⟩
  unfold retainedDensity
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi hs.1, mul_add, hs.2]
  congr 1
  by_cases he : n = 2
  · subst n
    have hμ : μ 2 = -1 := moebius_apply_prime Nat.prime_two
    simp [arithmeticRate, hμ, intervalIntegral.integral_const, smul_eq_mul]
    ring
  · rw [ite_eq_right he, intervalIntegral.integral_const_mul, exp_decay_integral (root_rate_positive (by omega))]
    have hrpow {x : ℝ} (hx : 0 < x) (r : ℝ) : Real.exp (-r * Real.log x) = x ^ (-r) := by
      rw [Real.rpow_def_of_pos hx, mul_comm]
    rw [hrpow ha, hrpow hB]
    unfold arithmeticPrimitive powerGap
    have hn₂ : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
    have hn₀ : (0 : ℝ) < n := zero_lt_two.trans hn₂
    have hrate : arithmeticRate n = ((n : ℝ) - 2) / (2 * (n : ℝ)) := by
      unfold arithmeticRate
      field_simp
    rw [hrate]
    have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (n : ℝ) - 2 ≠ 0 := by linarith
    field_simp

open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean
  (windowError normalizedMass normalizedZeroSeries)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (prime_window_remainder_of_rh spectralPrimitive windowDiscrepancy)

/-- Under RH the same left threshold and quadratic error constant work at every truncation degree. -/
theorem prime_window_mobius_of_rh (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        K * (m : ℝ)^2 *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (late_strict_prime_tail hRH)
  obtain ⟨K, hK, hD⟩ := all_orders_density_bound hRH
  refine ⟨max T 2, 6 * K, le_max_right _ _, by positivity, ?_⟩
  intro m hm a B ha hab
  have h_arithmetic (n : ℕ) : -(arithmeticRate n) = (n : ℝ)⁻¹ - 1 / 2 := by
    unfold arithmeticRate
    ring
  have h_order : -(orderRate m) = (m + 1 : ℝ)⁻¹ - 1 / 2 := by
    unfold orderRate
    ring
  simp_rw [← h_order, ← h_arithmetic]
  change |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
      spectralPrimitive (phaseOrbit (Real.log a)) -
      (∑ n ∈ Finset.Icc 3 m, arithmeticPrimitive n a B) -
      (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
        -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
      6 * K * (m : ℝ)^2 * powerGap (orderRate m) a B
  have ha₂ := (le_max_right T (2 : ℝ)).trans ha
  have ha₀ : 0 < a := by linarith
  have hB₀ := ha₀.trans_le hab
  have hlog := Real.log_le_log ha₀ hab
  have hlog₂ := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ha₂
  have hr : 1 / 6 ≤ orderRate m := by
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have h := inv_anti₀ (show (0 : ℝ) < 3 by norm_num)
      (show (3 : ℝ) ≤ (m + 1 : ℝ) by linarith)
    unfold orderRate
    norm_num at h
    linarith
  have hr₀ : 0 < orderRate m := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hr
  have Hwin : (∫ u in Real.log a..Real.log B, windowError u) =
      ∫ u in Real.log a..Real.log B, rootWindowDensity u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hlog] at hu
    have hx : a ≤ Real.exp u := by simpa only [Real.exp_log ha₀] using Real.exp_le_exp.mpr hu.1
    have hpos := hT _ ((le_max_left T 2).trans (ha.trans hx))
    have hscaled := complete_scaled (x := Real.exp u) (ha₂.trans hx)
    rw [Real.log_exp] at hscaled
    rw [windowError, normalizedMass, normalizedZeroSeries, max_eq_left hpos.le,
      rootWindowDensity, Complex.re_ofReal_mul, hscaled]
    ring
  let f (u : ℝ) := ∑ n ∈ Finset.Icc 2 m, retainedDensity m n u
  let e (u : ℝ) := rootWindowDensity u - (f u - 2)
  let w (u : ℝ) := K * (m : ℝ)^2 * Real.exp (-(orderRate m) * u)
  have hi : IntervalIntegrable rootWindowDensity volume (Real.log a) (Real.log B) :=
    (rootWindowDensity_continuousOn.mono (by
      rw [uIcc_of_le hlog]
      exact fun _ hu => hlog₂.trans hu.1)).intervalIntegrable
  have hfi : IntervalIntegrable f volume (Real.log a) (Real.log B) := by
    have hf : f = ∑ n ∈ Finset.Icc 2 m, retainedDensity m n := by
      funext u
      simp [f, Finset.sum_apply]
    rw [hf]
    exact IntervalIntegrable.sum (f := retainedDensity m) (Finset.Icc 2 m) (fun n hn =>
      (retainedDensity_integral (Finset.mem_Icc.mp hn).1 ha₀ hB₀).1)
  have hc : IntervalIntegrable (fun _ : ℝ => (2 : ℝ)) volume (Real.log a) (Real.log B) :=
    intervalIntegrable_const
  have hei : IntervalIntegrable e volume (Real.log a) (Real.log B) := hi.sub (hfi.sub hc)
  have hwi : IntervalIntegrable w volume (Real.log a) (Real.log B) :=
    (by unfold w; fun_prop : Continuous w).intervalIntegrable _ _
  have hmono : |∫ u in Real.log a..Real.log B, e u| ≤ ∫ u in Real.log a..Real.log B, w u :=
    (intervalIntegral.abs_integral_le_integral_abs hlog).trans
      (intervalIntegral.integral_mono_on hlog hei.abs hwi (fun u hu => hD m hm u (hlog₂.trans hu.1)))
  have Hf : (∫ u in Real.log a..Real.log B, f u) =
      2 * (Real.log B - Real.log a) +
        (∑ n ∈ Finset.Icc 3 m, arithmeticPrimitive n a B) +
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a)) := by
    unfold f
    rw [intervalIntegral.integral_finsetSum fun n hn =>
      (retainedDensity_integral (Finset.mem_Icc.mp hn).1 ha₀ hB₀).1]
    calc
      _ = ∑ n ∈ Finset.Icc 2 m,
          ((if n = 2 then 2 * (Real.log B - Real.log a) else arithmeticPrimitive n a B) +
            capturedPrimitive m n a B) :=
        Finset.sum_congr rfl fun _ hn => (retainedDensity_integral (Finset.mem_Icc.mp hn).1 ha₀ hB₀).2
      _ = _ := by
        rw [Finset.sum_add_distrib]
        have hs : Finset.Icc 2 m = insert 2 (Finset.Icc 3 m) := by
          ext n
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hmain :
            (∑ n ∈ Finset.Icc 2 m,
              if n = 2 then 2 * (Real.log B - Real.log a) else arithmeticPrimitive n a B) =
              2 * (Real.log B - Real.log a) + ∑ n ∈ Finset.Icc 3 m, arithmeticPrimitive n a B := by
          rw [hs, Finset.sum_insert (by simp)]
          congr 1
          exact Finset.sum_congr rfl fun n hn => ite_eq_right (by have := (Finset.mem_Icc.mp hn).1; omega)
        rw [hmain, Finset.sum_filter]
        rfl
  have hw : (∫ u in Real.log a..Real.log B, w u) =
      K * (m : ℝ)^2 * (powerGap (orderRate m) a B / orderRate m) := by
    unfold w
    rw [intervalIntegral.integral_const_mul, exp_decay_integral hr₀]
    have hrpow {x : ℝ} (hx : 0 < x) (r : ℝ) : Real.exp (-r * Real.log x) = x ^ (-r) := by
      rw [Real.rpow_def_of_pos hx, mul_comm]
    rw [hrpow ha₀, hrpow hB₀]
    rfl
  have hgap : 0 ≤ powerGap (orderRate m) a B :=
    sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos ha₀ hab (neg_nonpos.mpr hr₀.le))
  have hdiv : powerGap (orderRate m) a B / orderRate m ≤ 6 * powerGap (orderRate m) a B := by
    apply (div_le_iff₀ hr₀).mpr
    nlinarith only [mul_nonneg hgap (show 0 ≤ 6 * orderRate m - 1 by linarith)]
  rw [(prime_window_remainder_of_rh hRH).2.2 a B ha₂ hab, Hwin]
  have hle : (∫ u in Real.log a..Real.log B, w u) ≤
      6 * K * (m : ℝ)^2 * powerGap (orderRate m) a B := by
    rw [hw]
    exact (mul_le_mul_of_nonneg_left hdiv (by positivity)).trans_eq (by ring)
  refine (?_ : _ ≤ ∫ u in Real.log a..Real.log B, w u).trans hle
  dsimp only [e] at hmono
  rw [intervalIntegral.integral_sub hi (hfi.sub hc), intervalIntegral.integral_sub hfi hc, Hf,
    intervalIntegral.integral_const, smul_eq_mul] at hmono
  convert hmono using 1
  congr 1
  ring

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
