/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed square-cutoff transform has an exact occurrence-wise primitive. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

/-! The integrated zero tail is transported through the square cutoff before taking its
real part. Its primitive uses the half-log phase of the same actual zero occurrences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
  (actualZero actualData actualOccurrenceEquiv actual_height_gt_ten firstLiMass)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (normalizedH_bound)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

private def exponent (k : ℕ) : ℂ := actualZero k - 1

private def mode (c u : ℝ) (k : ℕ) : ℂ :=
  actualCoeff k * Complex.exp ((actualZero k - (c : ℂ)) * (u : ℂ))

/-- Complete occurrence-indexed spectral term of the centered tail at log cutoff `u`. -/
def zeroTail (u : ℝ) : ℂ := ∑' k : ℕ, mode 1 u k

private lemma zero_re_pos (k : ℕ) : 0 < (actualZero k).re :=
  (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.1

private lemma zero_re_lt_one (k : ℕ) : (actualZero k).re < 1 :=
  (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2

private lemma norm_mode (c u : ℝ) (k : ℕ) :
    ‖mode c u k‖ = ‖actualCoeff k‖ * Real.exp (((actualZero k).re - c) * u) := by
  simp only [mode, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, mul_zero, sub_zero]

private lemma mode_summable (c u : ℝ) : Summable (mode c u) := by
  apply (actualCoeff_hasSum.summable.norm.mul_right (Real.exp (|u| + |c * u|))).of_norm_bounded
  intro k
  rw [norm_mode]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  calc
    _ = (actualZero k).re * u + -(c * u) := by ring
    _ ≤ (actualZero k).re * |u| + |c * u| :=
      add_le_add (mul_le_mul_of_nonneg_left (le_abs_self u) (zero_re_pos k).le) (neg_le_abs _)
    _ ≤ |u| + |c * u| :=
      add_le_add_left (mul_le_of_le_one_left (abs_nonneg _) (zero_re_lt_one k).le) _

theorem zeroTail_eq (u : ℝ) :
    zeroTail u = (Real.exp (-u) : ℂ) * actualH u := by
  rw [zeroTail, actualH, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [mode, mul_left_comm, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The RH bound for the complete spectral tail with its signed normalization. -/
theorem norm_zeroTail_le (hRH : RiemannHypothesis) (u : ℝ) :
    ‖zeroTail u‖ ≤ firstLiMass * Real.exp (-u / 2) := by
  have h := normalizedH_bound hRH u
  change ‖(Real.exp (-u / 2) : ℂ) * actualH u‖ ≤ firstLiMass at h
  have he : Real.exp (-u) = Real.exp (-u / 2) * Real.exp (-u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [zeroTail_eq, he, Complex.ofReal_mul, mul_assoc, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm firstLiMass]
  exact mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)

private lemma zeroTail_continuous : Continuous zeroTail := by
  convert (show Continuous (fun u : ℝ => (Real.exp (-u) : ℂ)) by fun_prop).mul
    actualH_continuous using 1
  exact funext zeroTail_eq

private lemma gap_norm (k : ℕ) : 1 ≤ ‖2 - actualZero k‖ := by
  have h := Complex.abs_re_le_norm (2 - actualZero k)
  rw [Complex.sub_re, Complex.re_ofNat, abs_of_pos (by linarith [zero_re_lt_one k])] at h
  linarith [zero_re_lt_one k]

private lemma one_sub_zero_ne (k : ℕ) : 1 - actualZero k ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hh
  linarith [zero_re_lt_one k]

private lemma weighted_zero_mode (u : ℝ) (k : ℕ) :
    (Real.exp (-u) : ℂ) * mode 1 u k = mode 2 u k := by
  rw [mode, mode, mul_left_comm, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma weighted_zero_tail (v : ℝ) :
    let f := fun s : ℝ => (s ^ (-2 : ℝ)) • zeroTail (Real.log s)
    IntegrableOn f (Ioi (Real.exp v)) ∧
      HasSum (fun k : ℕ => mode 2 v k / (2 - actualZero k))
        (∫ s in Ioi (Real.exp v), f s) := by
  dsimp only
  let f (s : ℝ) := (s ^ (-2 : ℝ)) • zeroTail (Real.log s)
  have he (u : ℝ) : Real.exp u • f (Real.exp u) = ∑' k : ℕ, mode 2 u k := by
    change Real.exp u • ((Real.exp u ^ (-2 : ℝ)) • zeroTail (Real.log (Real.exp u))) = _
    simp only [Real.log_exp, smul_smul, ← Real.exp_mul, ← Real.exp_add]
    rw [show u + u * (-2) = -u by ring, Complex.real_smul, zeroTail, ← tsum_mul_left]
    exact tsum_congr (weighted_zero_mode u)
  let weight (u : ℝ) := Real.exp (max 0 (-v)) * Real.exp (-u)
  let mass := ∑' k : ℕ, ‖actualCoeff k‖
  have hweight : IntegrableOn weight (Ioi v) := by
    have h : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi v) := by
      convert integrableOn_exp_mul_Ioi (a := -1) (by norm_num) v using 1
      simp only [neg_one_mul]
    exact h.const_mul (Real.exp (max 0 (-v)))
  have hbound (u : ℝ) (hu : v < u) (k : ℕ) :
      ‖mode 2 u k‖ ≤ ‖actualCoeff k‖ * weight u := by
    rw [norm_mode]
    dsimp only [weight]
    rw [← Real.exp_add]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    by_cases hu0 : 0 ≤ u
    · nlinarith [mul_nonneg (sub_nonneg.mpr (zero_re_lt_one k).le) hu0, le_max_left 0 (-v)]
    · have h := mul_nonpos_of_nonneg_of_nonpos (zero_re_pos k).le (le_of_not_ge hu0)
      linarith [le_max_right 0 (-v)]
  have hae : ∀ᵐ u ∂volume.restrict (Ioi v), v < u :=
    ae_restrict_mem measurableSet_Ioi
  have hintegrable : IntegrableOn (fun u => Real.exp u • f (Real.exp u)) (Ioi v) := by
    apply (hweight.const_mul mass).mono'
    · have heq : (fun u => Real.exp u • f (Real.exp u)) =
          fun u => Real.exp (-u) • zeroTail u := by
        funext u
        change Real.exp u • ((Real.exp u ^ (-2 : ℝ)) • zeroTail (Real.log (Real.exp u))) = _
        simp only [Real.log_exp, smul_smul, ← Real.exp_mul, ← Real.exp_add]
        rw [show u + u * (-2) = -u by ring]
      rw [heq]
      exact ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-u))).smul
        zeroTail_continuous).aestronglyMeasurable
    · filter_upwards [hae] with u hu
      rw [he]
      exact tsum_of_norm_bounded ((actualCoeff_hasSum.summable.norm.hasSum).mul_right _)
        (hbound u hu)
  refine ⟨(integrableOn_comp_exp_Ioi f v).mp hintegrable, ?_⟩
  rw [← integral_comp_exp_Ioi f v]
  have hsum : HasSum (fun k : ℕ => ∫ u in Ioi v, mode 2 u k)
      (∫ u in Ioi v, Real.exp u • f (Real.exp u)) := by
    apply hasSum_integral_of_dominated_convergence
      (fun k u => ‖actualCoeff k‖ * weight u)
    · intro k
      exact (show Continuous (fun u => mode 2 u k) by unfold mode; fun_prop).aestronglyMeasurable
    · intro k
      filter_upwards [hae] with u hu using hbound u hu k
    · exact ae_of_all _ fun u => actualCoeff_hasSum.summable.norm.mul_right _
    · simpa only [tsum_mul_right] using hweight.const_mul mass
    · exact ae_of_all _ fun u => (he u).symm ▸ (mode_summable 2 u).hasSum
  convert hsum using 1
  funext k
  have hneg : (actualZero k - 2).re < 0 := by
    simp only [Complex.sub_re, Complex.re_ofNat]
    linarith [zero_re_lt_one k]
  simp only [mode, Complex.ofReal_ofNat, integral_const_mul,
    integral_exp_mul_complex_Ioi hneg]
  rw [show 2 - actualZero k = -(actualZero k - 2) by ring, div_neg]
  ring

private def squareCoeff (k : ℕ) : ℂ :=
  -2 / (actualZero k * (2 - actualZero k))

private lemma squareCoeff_eq (k : ℕ) :
    squareCoeff k = -2 * (actualCoeff k - actualCoeff k / (2 - actualZero k)) := by
  have h0 : actualZero k ≠ 0 := by
    intro h
    simpa [h] using zero_re_pos k
  have h1 := one_sub_zero_ne k
  have h2 : 2 - actualZero k ≠ 0 :=
    norm_pos_iff.mp (zero_lt_one.trans_le (gap_norm k))
  unfold squareCoeff actualCoeff
  field_simp
  ring

/-- The exact log-density from the square-cutoff zero modes. -/
def squareDensity (u : ℝ) : ℝ :=
  (∑' k : ℕ, squareCoeff k * Complex.exp (exponent k * ((u : ℂ) / 2))).re

/-- The square-cutoff transform of the spectral tail, with the sign of the Chebyshev error. -/
theorem square_spectral_transform (u : ℝ) :
    let y := Real.exp (u / 2)
    2 * (-(zeroTail (Real.log y)).re +
      y * (∫ s in Ioi y, s ^ (-2 : ℝ) * (zeroTail (Real.log s)).re)) = squareDensity u := by
  dsimp only
  let v := u / 2
  let y := Real.exp v
  obtain ⟨hi, hs⟩ := weighted_zero_tail v
  have hre : (∫ s in Ioi y, s ^ (-2 : ℝ) * (zeroTail (Real.log s)).re) =
      (∫ s in Ioi y, (s ^ (-2 : ℝ)) • zeroTail (Real.log s)).re := by
    have h := integral_re hi
    change (∫ s in Ioi (Real.exp v), ((s ^ (-2 : ℝ)) • zeroTail (Real.log s)).re) =
      (∫ s in Ioi (Real.exp v), (s ^ (-2 : ℝ)) • zeroTail (Real.log s)).re at h
    simpa only [Complex.real_smul, Complex.re_ofReal_mul] using h
  change 2 * (-(zeroTail (Real.log y)).re +
    y * (∫ s in Ioi y, s ^ (-2 : ℝ) * (zeroTail (Real.log s)).re)) = _
  rw [hre, show Real.log y = v from Real.log_exp v]
  have hterms := ((mode_summable 1 v).hasSum.sub (hs.mul_left (y : ℂ))).mul_left (-2)
  have he (k : ℕ) : (y : ℂ) * mode 2 v k = mode 1 v k := by
    rw [mode, mode, mul_left_comm, show ((y : ℝ) : ℂ) = Complex.exp (v : ℂ) by
      rw [← Complex.ofReal_exp], ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hmatch (k : ℕ) : -2 * (mode 1 v k - (y : ℂ) * (mode 2 v k / (2 - actualZero k))) =
      squareCoeff k * Complex.exp (exponent k * ((u : ℂ) / 2)) := by
    rw [← mul_div_assoc, he, squareCoeff_eq]
    simp only [mode, exponent, v, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
    ring
  have hts := congrArg Complex.re hterms.tsum_eq
  simp only [hmatch] at hts
  change squareDensity u =
    (-2 * (zeroTail v - (y : ℂ) * (∫ s in Ioi y, (s ^ (-2 : ℝ)) • zeroTail (Real.log s)))).re at hts
  rw [show (-2 : ℂ) = ((-2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul,
    Complex.sub_re, Complex.re_ofReal_mul] at hts
  linarith only [hts]

/-- The endpoint primitive uses ordinary complex powers at positive cutoffs. -/
def squarePrimitive (x : ℝ) : ℝ :=
  4 * (∑' k : ℕ, (x : ℂ) ^ (exponent k / 2) /
    (actualZero k * (1 - actualZero k) * (2 - actualZero k))).re

private lemma squareCoeff_bound (k : ℕ) :
    ‖squareCoeff k‖ ≤ 4 * ‖actualCoeff k‖ := by
  rw [squareCoeff_eq, norm_mul]
  have hratio : ‖actualCoeff k / (2 - actualZero k)‖ ≤ ‖actualCoeff k‖ := by
    rw [norm_div]
    exact div_le_self (norm_nonneg _) (gap_norm k)
  calc
    _ ≤ ‖(-2 : ℂ)‖ * (‖actualCoeff k‖ + ‖actualCoeff k‖) :=
      mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add le_rfl hratio)) (norm_nonneg _)
    _ = 4 * ‖actualCoeff k‖ := by rw [norm_neg, Complex.norm_two]; ring

private def squareMode (k : ℕ) (u : ℝ) : ℂ :=
  squareCoeff k * Complex.exp (exponent k * ((u : ℂ) / 2))

private lemma exponent_re (k : ℕ) :
    -(1 / 2 : ℝ) < (exponent k / 2).re ∧ (exponent k / 2).re < 0 := by
  norm_num [exponent, Complex.div_re, Complex.sub_re]
  constructor <;> linarith [zero_re_pos k, zero_re_lt_one k]

private lemma exponent_norm (k : ℕ) : 1 ≤ ‖exponent k / 2‖ := by
  have hh : 10 < |(actualZero k).im| :=
    actual_height_gt_ten _ (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
  have hi := Complex.abs_im_le_norm (exponent k / 2)
  norm_num [exponent, norm_div, Complex.div_im, Complex.sub_im, abs_div] at hi ⊢
  linarith

private lemma squareMode_bound {a u : ℝ} (ha : a ≤ u) (k : ℕ) :
    ‖squareMode k u‖ ≤ (4 * ‖actualCoeff k‖) * Real.exp (max 0 (-a) / 2) := by
  rw [squareMode, show exponent k * ((u : ℂ) / 2) = (u : ℂ) * (exponent k / 2) by ring,
    norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
  refine mul_le_mul (squareCoeff_bound k) (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _)
    (by positivity)
  obtain ⟨hlo, hhi⟩ := exponent_re k
  by_cases hu : 0 ≤ u
  · exact (mul_nonpos_of_nonneg_of_nonpos hu hhi.le).trans (by positivity)
  · calc
      _ ≤ u * (-(1 / 2 : ℝ)) := mul_le_mul_of_nonpos_left hlo.le (le_of_not_ge hu)
      _ ≤ _ := by linarith [le_max_right 0 (-a)]

private lemma squareMode_summable (u : ℝ) : Summable (fun k => squareMode k u) :=
  ((actualCoeff_hasSum.summable.norm.mul_left 4).mul_right
    (Real.exp (max 0 (-u) / 2))).of_norm_bounded (squareMode_bound le_rfl)

private lemma squareSeries_continuousOn (a : ℝ) :
    ContinuousOn (fun u => ∑' k, squareMode k u) (Ici a) := by
  apply continuousOn_tsum
    (fun k => (show Continuous (squareMode k) by unfold squareMode; fun_prop).continuousOn)
    ((actualCoeff_hasSum.summable.norm.mul_left 4).mul_right (Real.exp (max 0 (-a) / 2)))
  intro k u hu
  exact squareMode_bound hu k

private lemma primitiveMode_eq (u : ℝ) (k : ℕ) :
    squareMode k u / (exponent k / 2) =
      4 * ((Real.exp u : ℂ) ^ (exponent k / 2) /
        (actualZero k * (1 - actualZero k) * (2 - actualZero k))) := by
  have hpow : (Real.exp u : ℂ) ^ (exponent k / 2) =
      Complex.exp (exponent k * ((u : ℂ) / 2)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    congr 1
    ring
  rw [squareMode, hpow, squareCoeff, exponent]
  rw [show actualZero k - 1 = -(1 - actualZero k) by ring]
  field_simp [one_sub_zero_ne]
  ring

private lemma primitiveMode_summable (u : ℝ) :
    Summable (fun k => squareMode k u / (exponent k / 2)) := by
  apply ((actualCoeff_hasSum.summable.norm.mul_left 4).mul_right
    (Real.exp (max 0 (-u) / 2))).of_norm_bounded
  intro k
  rw [norm_div]
  exact (div_le_self (norm_nonneg _) (exponent_norm k)).trans (squareMode_bound le_rfl k)

private lemma primitiveMode_tsum_re (u : ℝ) :
    (∑' k, squareMode k u / (exponent k / 2)).re = squarePrimitive (Real.exp u) := by
  simp_rw [primitiveMode_eq, tsum_mul_left, squarePrimitive]
  norm_num [Complex.mul_re]

/-- Absolute termwise integration gives the same primitive at both log cutoffs. -/
theorem square_density_integral (a b : ℝ) :
    IntervalIntegrable squareDensity volume a b ∧
      (∫ u in a..b, squareDensity u) =
        squarePrimitive (Real.exp b) - squarePrimitive (Real.exp a) := by
  let series (u : ℝ) := ∑' k, squareMode k u
  have hcont : ContinuousOn series (uIcc a b) := by
    exact (squareSeries_continuousOn (min a b)).mono fun _ hu => hu.1
  refine ⟨(Complex.continuous_re.comp_continuousOn hcont).intervalIntegrable, ?_⟩
  have hre : (∫ u in a..b, squareDensity u) = (∫ u in a..b, series u).re := by
    change (∫ u in a..b, (series u).re) = _
    exact intervalIntegral.intervalIntegral_re hcont.intervalIntegrable
  have hi : HasSum (fun k => ∫ u in a..b, squareMode k u) (∫ u in a..b, series u) := by
    let bound (k : ℕ) := (4 * ‖actualCoeff k‖) * Real.exp (max 0 (-(min a b)) / 2)
    have hs : Summable bound :=
      (actualCoeff_hasSum.summable.norm.mul_left 4).mul_right _
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => bound k)
    · intro k
      exact (show Continuous (squareMode k) by unfold squareMode; fun_prop).aestronglyMeasurable
    · intro k
      exact ae_of_all _ fun u hu => squareMode_bound hu.1.le k
    · exact ae_of_all _ fun _ _ => hs
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun u _ => (squareMode_summable u).hasSum
  have hmode (k : ℕ) : (∫ u in a..b, squareMode k u) =
      squareMode k b / (exponent k / 2) - squareMode k a / (exponent k / 2) := by
    have hn : exponent k / 2 ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le (exponent_norm k))
    simp only [squareMode, show ∀ u : ℝ, exponent k * ((u : ℂ) / 2) =
        (exponent k / 2) * (u : ℂ) by intro; ring,
      intervalIntegral.integral_const_mul, integral_exp_mul_complex hn]
    ring
  rw [hre, ← hi.tsum_eq, tsum_congr hmode, (primitiveMode_summable b).tsum_sub
    (primitiveMode_summable a), Complex.sub_re, primitiveMode_tsum_re,
    primitiveMode_tsum_re]

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
