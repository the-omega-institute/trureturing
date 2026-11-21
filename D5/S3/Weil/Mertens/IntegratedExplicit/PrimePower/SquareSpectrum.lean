/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed square-cutoff transform has an exact occurrence-wise primitive. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster

/-! The integrated zero tail is transported through the square cutoff before taking its
real part. Its primitive uses the half-log phase of the same actual zero occurrences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualZero firstLiMass)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (on_line coeff_norm_hasSum)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

private def exponent (k : ℕ) : ℂ := actualZero k - 1

private def mode (c u : ℝ) (k : ℕ) : ℂ :=
  actualCoeff k * Complex.exp ((actualZero k - (c : ℂ)) * (u : ℂ))

/-- Complete occurrence-indexed spectral term of the centered tail at log cutoff `u`. -/
def zeroTail (u : ℝ) : ℂ := ∑' k : ℕ, mode 1 u k

private lemma norm_mode (hRH : RiemannHypothesis) (c u : ℝ) (k : ℕ) :
    ‖mode c u k‖ = ‖actualCoeff k‖ * Real.exp ((1 / 2 - c) * u) := by
  simp only [mode, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, on_line hRH k, mul_zero, sub_zero]

private lemma mode_summable (hRH : RiemannHypothesis) (c u : ℝ) :
    Summable (mode c u) :=
  (actualCoeff_hasSum.summable.norm.mul_right _).of_norm_bounded
    (fun k => (norm_mode hRH c u k).le)

/-- The RH bound for the complete spectral tail with its signed normalization. -/
theorem norm_zeroTail_le (hRH : RiemannHypothesis) (u : ℝ) :
    ‖zeroTail u‖ ≤ firstLiMass * Real.exp (-u / 2) := by
  unfold zeroTail
  apply tsum_of_norm_bounded ((coeff_norm_hasSum hRH).mul_right _)
  intro k
  rw [norm_mode hRH]
  rw [show (1 / 2 - 1) * u = -u / 2 by ring]

theorem zeroTail_eq (u : ℝ) :
    zeroTail u = (Real.exp (-u) : ℂ) * actualH u := by
  rw [zeroTail, actualH, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [mode, mul_left_comm, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma zeroTail_continuous : Continuous zeroTail := by
  convert (show Continuous (fun u : ℝ => (Real.exp (-u) : ℂ)) by fun_prop).mul
    actualH_continuous using 1
  exact funext zeroTail_eq

private lemma gap_re (hRH : RiemannHypothesis) (c : ℝ) (k : ℕ) :
    (actualZero k - (c : ℂ)).re = 1 / 2 - c := by simp [on_line hRH k]

private lemma gap_norm (hRH : RiemannHypothesis) (k : ℕ) :
    1 ≤ ‖actualZero k - 2‖ := by
  have h := Complex.abs_re_le_norm (actualZero k - 2)
  rw [Complex.sub_re, on_line hRH k] at h
  norm_num at h
  linarith

private lemma gap_ne (hRH : RiemannHypothesis) (k : ℕ) : actualZero k - 2 ≠ 0 := by
  exact norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1).trans_le (gap_norm hRH k))

private lemma weighted_zero_mode (u : ℝ) (k : ℕ) :
    (Real.exp (-u) : ℂ) * mode 1 u k = mode 2 u k := by
  rw [mode, mode, mul_left_comm, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma weighted_zero_tail (hRH : RiemannHypothesis) (v : ℝ) :
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
  have hintegrable : IntegrableOn (fun u => Real.exp u • f (Real.exp u)) (Ioi v) := by
    have h := (integrableOn_exp_mul_Ioi (a := -(3 / 2 : ℝ)) (by norm_num) v).const_mul
      firstLiMass
    apply h.mono'
    · have heq : (fun u => Real.exp u • f (Real.exp u)) =
          fun u => Real.exp (-u) • zeroTail u := by
        funext u
        change Real.exp u • ((Real.exp u ^ (-2 : ℝ)) • zeroTail (Real.log (Real.exp u))) = _
        simp only [Real.log_exp, smul_smul, ← Real.exp_mul, ← Real.exp_add]
        rw [show u + u * (-2) = -u by ring]
      rw [heq]
      exact ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-u))).smul
        zeroTail_continuous).aestronglyMeasurable
    · filter_upwards with u
      rw [he]
      apply tsum_of_norm_bounded ((coeff_norm_hasSum hRH).mul_right _)
      intro k
      rw [norm_mode hRH]
      rw [show (1 / 2 - 2 : ℝ) = -(3 / 2) by norm_num]
  refine ⟨(integrableOn_comp_exp_Ioi f v).mp hintegrable, ?_⟩
  rw [← integral_comp_exp_Ioi f v]
  have hweight : IntegrableOn (fun u => Real.exp (-(3 / 2 : ℝ) * u)) (Ioi v) :=
    integrableOn_exp_mul_Ioi (by norm_num) _
  have hsum : HasSum (fun k : ℕ => ∫ u in Ioi v, mode 2 u k)
      (∫ u in Ioi v, Real.exp u • f (Real.exp u)) := by
    apply hasSum_integral_of_dominated_convergence
      (fun k u => ‖actualCoeff k‖ * Real.exp (-(3 / 2 : ℝ) * u))
    · intro k
      exact (show Continuous (fun u => mode 2 u k) by unfold mode; fun_prop).aestronglyMeasurable
    · intro k
      exact ae_of_all _ fun u => by rw [norm_mode hRH]; norm_num
    · exact ae_of_all _ fun u => actualCoeff_hasSum.summable.norm.mul_right _
    · simpa only [tsum_mul_right, (coeff_norm_hasSum hRH).tsum_eq]
        using hweight.const_mul firstLiMass
    · exact ae_of_all _ fun u => (he u).symm ▸ (mode_summable hRH 2 u).hasSum
  convert hsum using 1
  funext k
  have hneg : (actualZero k - 2).re < 0 := by
    norm_num [Complex.sub_re, on_line hRH k]
  simp only [mode, Complex.ofReal_ofNat, integral_const_mul,
    integral_exp_mul_complex_Ioi hneg]
  rw [show 2 - actualZero k = -(actualZero k - 2) by ring, div_neg]
  ring

private def squareCoeff (k : ℕ) : ℂ :=
  -2 / (actualZero k * (2 - actualZero k))

private lemma squareCoeff_eq (hRH : RiemannHypothesis) (k : ℕ) :
    squareCoeff k = -2 * (actualCoeff k - actualCoeff k / (2 - actualZero k)) := by
  have h0 : actualZero k ≠ 0 := by
    intro h
    have := on_line hRH k
    rw [h, Complex.zero_re] at this
    norm_num at this
  have h1 : 1 - actualZero k ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.sub_re, on_line hRH k] at hh
  have h2 : 2 - actualZero k ≠ 0 := by
    rw [show 2 - actualZero k = -(actualZero k - 2) by ring, neg_ne_zero]
    exact gap_ne hRH k
  unfold squareCoeff actualCoeff
  field_simp
  ring

/-- The exact log-density from the square-cutoff zero modes. -/
def squareDensity (u : ℝ) : ℝ :=
  (∑' k : ℕ, squareCoeff k * Complex.exp (exponent k * ((u : ℂ) / 2))).re

/-- The square-cutoff transform of the spectral tail, with the sign of the Chebyshev error. -/
theorem square_spectral_transform (hRH : RiemannHypothesis) (u : ℝ) :
    let y := Real.exp (u / 2)
    2 * (-(zeroTail (Real.log y)).re +
      y * (∫ s in Ioi y, s ^ (-2 : ℝ) * (zeroTail (Real.log s)).re)) = squareDensity u := by
  dsimp only
  let v := u / 2
  let y := Real.exp v
  obtain ⟨hi, hs⟩ := weighted_zero_tail hRH v
  have hre : (∫ s in Ioi y, s ^ (-2 : ℝ) * (zeroTail (Real.log s)).re) =
      (∫ s in Ioi y, (s ^ (-2 : ℝ)) • zeroTail (Real.log s)).re := by
    have h := integral_re hi
    change (∫ s in Ioi (Real.exp v), ((s ^ (-2 : ℝ)) • zeroTail (Real.log s)).re) =
      (∫ s in Ioi (Real.exp v), (s ^ (-2 : ℝ)) • zeroTail (Real.log s)).re at h
    simpa only [Complex.real_smul, Complex.re_ofReal_mul] using h
  change 2 * (-(zeroTail (Real.log y)).re +
    y * (∫ s in Ioi y, s ^ (-2 : ℝ) * (zeroTail (Real.log s)).re)) = _
  rw [hre, show Real.log y = v from Real.log_exp v]
  have hterms := ((mode_summable hRH 1 v).hasSum.sub (hs.mul_left (y : ℂ))).mul_left (-2)
  have he (k : ℕ) : (y : ℂ) * mode 2 v k = mode 1 v k := by
    rw [mode, mode, mul_left_comm, show ((y : ℝ) : ℂ) = Complex.exp (v : ℂ) by
      rw [← Complex.ofReal_exp], ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hmatch (k : ℕ) : -2 * (mode 1 v k - (y : ℂ) * (mode 2 v k / (2 - actualZero k))) =
      squareCoeff k * Complex.exp (exponent k * ((u : ℂ) / 2)) := by
    rw [← mul_div_assoc, he, squareCoeff_eq hRH]
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

/-- The power in the primitive retains the actual half phase, whose square gives the
ordinary phase at the same cutoff. -/
theorem square_power_half_phase (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (x : ℂ) ^ ((actualZero k - 1) / 2) =
      (x ^ (-(1 / 4 : ℝ)) : ℝ) * (phaseOrbit (Real.log x / 2) k : ℂ) ∧
    (phaseOrbit (Real.log x / 2) k : ℂ) ^ 2 = (phaseOrbit (Real.log x) k : ℂ) := by
  constructor
  · rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      ← Complex.ofReal_log hx.le, Real.rpow_def_of_pos hx, Complex.ofReal_exp,
      phaseOrbit, Circle.coe_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, on_line hRH k] <;> ring
  · simp only [phaseOrbit, Circle.coe_exp, sq, ← Complex.exp_add]
    congr 1
    push_cast
    ring


private lemma squareCoeff_bound (hRH : RiemannHypothesis) (k : ℕ) :
    ‖squareCoeff k‖ ≤ 4 * ‖actualCoeff k‖ := by
  rw [squareCoeff_eq hRH, norm_mul]
  have hgap : 1 ≤ ‖2 - actualZero k‖ := by
    rw [show 2 - actualZero k = -(actualZero k - 2) by ring, norm_neg]
    exact gap_norm hRH k
  have hratio : ‖actualCoeff k / (2 - actualZero k)‖ ≤ ‖actualCoeff k‖ := by
    rw [norm_div]
    exact div_le_self (norm_nonneg _) hgap
  calc
    _ ≤ ‖(-2 : ℂ)‖ * (‖actualCoeff k‖ + ‖actualCoeff k‖) :=
      mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add le_rfl hratio)) (norm_nonneg _)
    _ = 4 * ‖actualCoeff k‖ := by rw [norm_neg, Complex.norm_two]; ring

private def squareMode (k : ℕ) (u : ℝ) : ℂ :=
  squareCoeff k * Complex.exp (exponent k * ((u : ℂ) / 2))

private lemma exponent_re (hRH : RiemannHypothesis) (k : ℕ) :
    (exponent k / 2).re = -(1 / 4 : ℝ) := by
  norm_num [exponent, Complex.div_re, Complex.sub_re, on_line hRH k]

private lemma squareMode_norm (hRH : RiemannHypothesis) (k : ℕ) (u : ℝ) :
    ‖squareMode k u‖ = ‖squareCoeff k‖ * Real.exp (-(1 / 4 : ℝ) * u) := by
  rw [squareMode, show exponent k * ((u : ℂ) / 2) = (u : ℂ) * (exponent k / 2) by ring,
    norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, exponent_re hRH, mul_comm u]

private lemma squareMode_summable (hRH : RiemannHypothesis) (u : ℝ) :
    Summable (fun k => squareMode k u) := by
  apply ((actualCoeff_hasSum.summable.norm.mul_left 4).mul_right
      (Real.exp (-(1 / 4 : ℝ) * u))).of_norm_bounded
  intro k
  rw [squareMode_norm hRH]
  exact mul_le_mul_of_nonneg_right (squareCoeff_bound hRH k) (Real.exp_nonneg _)

private lemma squareSeries_continuousOn (hRH : RiemannHypothesis) (a : ℝ) :
    ContinuousOn (fun u => ∑' k, squareMode k u) (Ici a) := by
  apply continuousOn_tsum
    (fun k => (show Continuous (squareMode k) by unfold squareMode; fun_prop).continuousOn)
    ((actualCoeff_hasSum.summable.norm.mul_left 4).mul_right (Real.exp (-(1 / 4 : ℝ) * a)))
  intro k u hu
  rw [squareMode_norm hRH]
  exact mul_le_mul (squareCoeff_bound hRH k)
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hu (by norm_num)))
    (Real.exp_nonneg _) (by positivity)

private lemma primitiveMode_eq (hRH : RiemannHypothesis) (u : ℝ) (k : ℕ) :
    squareMode k u / (exponent k / 2) =
      4 * ((Real.exp u : ℂ) ^ (exponent k / 2) /
        (actualZero k * (1 - actualZero k) * (2 - actualZero k))) := by
  have hpow : (Real.exp u : ℂ) ^ (exponent k / 2) =
      Complex.exp (exponent k * ((u : ℂ) / 2)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    congr 1
    ring
  have hn : 1 - actualZero k ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.sub_re, on_line hRH k] at hh
  rw [squareMode, hpow, squareCoeff, exponent]
  rw [show actualZero k - 1 = -(1 - actualZero k) by ring]
  field_simp [hn] <;> ring

private lemma primitiveMode_summable (hRH : RiemannHypothesis) (u : ℝ) :
    Summable (fun k => squareMode k u / (exponent k / 2)) := by
  apply (((actualCoeff_hasSum.summable.norm.mul_left 4).mul_right
      (Real.exp (-(1 / 4 : ℝ) * u))).div_const (1 / 4)).of_norm_bounded
  intro k
  have hn : 1 / 4 ≤ ‖exponent k / 2‖ := by
    simpa [exponent_re hRH] using Complex.abs_re_le_norm (exponent k / 2)
  rw [norm_div, squareMode_norm hRH]
  exact (div_le_div_of_nonneg_left (by positivity) (by norm_num) hn).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (squareCoeff_bound hRH k)
      (Real.exp_nonneg _)) (by norm_num))

private lemma primitiveMode_tsum_re (hRH : RiemannHypothesis) (u : ℝ) :
    (∑' k, squareMode k u / (exponent k / 2)).re = squarePrimitive (Real.exp u) := by
  simp_rw [primitiveMode_eq hRH, tsum_mul_left, squarePrimitive]
  norm_num [Complex.mul_re]

/-- Absolute termwise integration gives the same primitive at both log cutoffs. -/
theorem square_density_integral (hRH : RiemannHypothesis) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable squareDensity volume a b ∧
      (∫ u in a..b, squareDensity u) =
        squarePrimitive (Real.exp b) - squarePrimitive (Real.exp a) := by
  let series (u : ℝ) := ∑' k, squareMode k u
  have hcont : ContinuousOn series (uIcc a b) := by
    apply (squareSeries_continuousOn hRH a).mono
    rw [uIcc_of_le hab]
    exact Icc_subset_Ici_self
  refine ⟨(Complex.continuous_re.comp_continuousOn hcont).intervalIntegrable, ?_⟩
  have hre : (∫ u in a..b, squareDensity u) = (∫ u in a..b, series u).re := by
    change (∫ u in a..b, (series u).re) = _
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    exact integral_re hcont.intervalIntegrable.1
  have hi : HasSum (fun k => ∫ u in a..b, squareMode k u) (∫ u in a..b, series u) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k u => (4 * ‖actualCoeff k‖) * Real.exp (-(1 / 4 : ℝ) * u))
    · intro k
      exact (show Continuous (squareMode k) by unfold squareMode; fun_prop).aestronglyMeasurable
    · intro k
      exact ae_of_all _ fun u _ => by
        rw [squareMode_norm hRH]
        exact mul_le_mul_of_nonneg_right (squareCoeff_bound hRH k) (Real.exp_nonneg _)
    · exact ae_of_all _ fun u _ =>
        (actualCoeff_hasSum.summable.norm.mul_left 4).mul_right _
    · simp_rw [tsum_mul_right, tsum_mul_left]
      exact (show Continuous (fun u : ℝ =>
        (4 * (∑' k, ‖actualCoeff k‖)) * Real.exp (-(1 / 4 : ℝ) * u)) by fun_prop).intervalIntegrable
        _ _
    · exact ae_of_all _ fun u _ => (squareMode_summable hRH u).hasSum
  have hmode (k : ℕ) : (∫ u in a..b, squareMode k u) =
      squareMode k b / (exponent k / 2) - squareMode k a / (exponent k / 2) := by
    have hn : exponent k / 2 ≠ 0 := by
      intro he
      have := exponent_re hRH k
      rw [he, Complex.zero_re] at this
      norm_num at this
    simp only [squareMode, show ∀ u : ℝ, exponent k * ((u : ℂ) / 2) =
        (exponent k / 2) * (u : ℂ) by intro; ring,
      intervalIntegral.integral_const_mul, integral_exp_mul_complex hn]
    ring
  rw [hre, ← hi.tsum_eq, tsum_congr hmode, (primitiveMode_summable hRH b).tsum_sub
    (primitiveMode_summable hRH a), Complex.sub_re, primitiveMode_tsum_re hRH,
    primitiveMode_tsum_re hRH]

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
