/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootPrimitiveFourier
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootPrimitiveFourier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized root primitives and quantitative extraction of exponential-series frequency fibers. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootSpectrum
import D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency)
open MeasureTheory
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

/-- The integrated mode gains at most one factor of the root degree from its primitive. -/
theorem root_primitive_coefficient_norm_le {r : ℝ} (hr : 1 < r) (k : ℕ) :
    ‖rootCoeff r k / rootExponent r k‖ ≤ (r * ‖actualCoeff k‖) * r := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  rw [norm_div]
  calc
    _ ≤ ‖rootCoeff r k‖ / r⁻¹ :=
      div_le_div_of_nonneg_left (norm_nonneg _) (inv_pos.mpr hr0) (rootExponent_norm hr k)
    _ ≤ _ := by rw [div_inv_eq_mul]; gcongr; exact rootCoeff_bound hr k

/-- Removing the common real decay rate expresses the primitive as a centered zero series. -/
theorem normalized_root_primitive_series {r : ℝ} (hr : 1 < r) (u : ℝ) :
    let s : ℝ := 1/2-(2*r)⁻¹
    Real.exp (s*u)*rootPrimitive r (Real.exp u) =
      (∑' k, (rootCoeff r k / rootExponent r k) *
        Complex.exp ((frequency k/(r : ℂ))*(u : ℂ))).re := by
  let s : ℝ := 1/2-(2*r)⁻¹
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hshift (k : ℕ) : rootExponent r k + (s : ℂ) = frequency k/(r : ℂ) := by
    simp only [rootExponent, frequency, s]
    push_cast
    field_simp
    ring
  change Real.exp (s*u)*rootPrimitive r (Real.exp u) = _
  unfold rootPrimitive
  rw [← Complex.re_ofReal_mul, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  rw [← rootPrimitiveMode_eq hr]
  change (Real.exp (s*u) : ℂ) *
    (rootCoeff r k * Complex.exp (rootExponent r k * (u : ℂ))/rootExponent r k) = _
  rw [Complex.ofReal_exp]
  push_cast
  rw [show Complex.exp ((s : ℂ)*(u : ℂ)) *
      (rootCoeff r k * Complex.exp (rootExponent r k * (u : ℂ))/rootExponent r k) =
      (rootCoeff r k / rootExponent r k) * (Complex.exp (rootExponent r k * (u : ℂ)) *
        Complex.exp ((s : ℂ)*(u : ℂ))) by ring,
    ← Complex.exp_add, ← add_mul, hshift]

theorem bounded_exponential_integral {c : ℂ} (hc : c.re = 0)
    {gap : ℝ} (hgap : 0 < gap) (hgapc : gap ≤ ‖c‖) (a b : ℝ) :
    ‖∫ u in a..b, Complex.exp (c * (u : ℂ))‖ ≤ 2 / gap := by
  have hc_ne : c ≠ 0 := norm_pos_iff.mp (hgap.trans_le hgapc)
  have hexp (u : ℝ) : ‖Complex.exp (c * (u : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, hc]
  rw [integral_exp_mul_complex hc_ne, norm_div]
  have hnum : ‖Complex.exp (c * (b : ℂ)) - Complex.exp (c * (a : ℂ))‖ ≤ 2 := by
    simpa only [hexp, one_add_one_eq_two] using
      norm_sub_le (Complex.exp (c * (b : ℂ))) (Complex.exp (c * (a : ℂ)))
  exact div_le_div_of_nonneg_right hnum (norm_nonneg _) |>.trans
    (div_le_div_of_nonneg_left (by norm_num) hgap hgapc)

theorem bounded_exponential_series_integral
    (coeff mode : ℕ → ℂ) (hcoeff : Summable (fun k => ‖coeff k‖))
    (hmode : ∀ k, (mode k).re = 0) {gap : ℝ} (hgap : 0 < gap)
    (hmode_gap : ∀ k, gap ≤ ‖mode k‖) (a b : ℝ) :
    let signal := fun u : ℝ => ∑' k, coeff k * Complex.exp (mode k * (u : ℂ))
    IntervalIntegrable signal volume a b ∧
      ‖∫ u in a..b, signal u‖ ≤ (∑' k, ‖coeff k‖) * (2 / gap) := by
  let term (k : ℕ) (u : ℝ) := coeff k * Complex.exp (mode k * (u : ℂ))
  have hterm (k : ℕ) : Continuous (term k) := by unfold term; fun_prop
  have hnorm (k : ℕ) (u : ℝ) : ‖term k u‖ = ‖coeff k‖ := by
    simp [term, Complex.norm_exp, Complex.mul_re, hmode k]
  have hsignal : Continuous (fun u : ℝ => ∑' k, term k u) :=
    continuous_tsum hterm hcoeff fun k u => (hnorm k u).le
  have hsum (u : ℝ) : Summable (fun k => term k u) :=
    hcoeff.of_norm_bounded fun k => (hnorm k u).le
  have hi : HasSum (fun k : ℕ => ∫ u in a..b, term k u)
      (∫ u in a..b, ∑' k, term k u) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun k (_ : ℝ) => ‖coeff k‖)
    · exact fun k => (hterm k).aestronglyMeasurable
    · exact fun k => ae_of_all _ fun u _ => (hnorm k u).le
    · exact ae_of_all _ fun _ _ => hcoeff
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun u _ => (hsum u).hasSum
  refine ⟨hsignal.intervalIntegrable _ _, ?_⟩
  change ‖∫ u in a..b, ∑' k, term k u‖ ≤ _
  rw [← hi.tsum_eq]
  apply tsum_of_norm_bounded (hcoeff.hasSum.mul_right (2 / gap))
  intro k
  unfold term
  rw [intervalIntegral.integral_const_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (bounded_exponential_integral (hmode k) hgap (hmode_gap k) a b) (norm_nonneg _)

/-- Testing a summable exponential series by a character recovers the full matching fiber.
A gap from the other modes bounds the error uniformly in the averaging start. -/
theorem spectral_fiber_average
    (coeff mode : ℕ → ℂ) (hcoeff : Summable (fun k => ‖coeff k‖))
    (hmode : ∀ k, (mode k).re = 0) {w : ℂ} (hw : w.re = 0)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ k, mode k ≠ w → δ ≤ ‖mode k - w‖)
    (U : ℝ) {T : ℝ} (hT : 0 < T) :
    let f := fun u : ℝ => (∑' k, coeff k * Complex.exp (mode k*(u : ℂ))) *
      Complex.exp (-w*(u : ℂ))
    let target := ∑' k, if mode k = w then coeff k else 0
    IntervalIntegrable f volume U (U+T) ∧
      ‖(∫ u in U..U+T, f u)/(T : ℂ) - target‖ ≤
        (∑' k, ‖coeff k‖) * (2/δ) / T := by
  let matchCoeff (k : ℕ) := if mode k = w then coeff k else 0
  let offCoeff (k : ℕ) := if mode k = w then 0 else coeff k
  let offMode (k : ℕ) := if mode k = w then (δ : ℂ)*Complex.I else mode k-w
  let off (u : ℝ) := ∑' k, offCoeff k * Complex.exp (offMode k*(u : ℂ))
  let target := ∑' k, matchCoeff k
  have hmatch (k : ℕ) : ‖matchCoeff k‖ ≤ ‖coeff k‖ := by
    by_cases hk : mode k = w <;> simp [matchCoeff, hk]
  have hoff (k : ℕ) : ‖offCoeff k‖ ≤ ‖coeff k‖ := by
    by_cases hk : mode k = w <;> simp [offCoeff, hk]
  have hOffCoeff : Summable (fun k => ‖offCoeff k‖) :=
    hcoeff.of_nonneg_of_le (fun _ => norm_nonneg _) hoff
  have hmatchSummable : Summable matchCoeff := hcoeff.of_norm_bounded hmatch
  have hOffMode (k : ℕ) : (offMode k).re = 0 := by
    by_cases hk : mode k = w <;> simp [offMode, hk, hmode k, hw]
  have hOffGap (k : ℕ) : δ ≤ ‖offMode k‖ := by
    by_cases hk : mode k = w
    · simp [offMode, hk, abs_of_pos hδ]
    · simpa only [offMode, ite_eq_right hk] using hgap k hk
  have hOffSummable (u : ℝ) : Summable (fun k => offCoeff k * Complex.exp (offMode k*(u : ℂ))) := by
    apply hOffCoeff.of_norm_bounded
    intro k
    simp [Complex.norm_exp, Complex.mul_re, hOffMode k]
  have hfun :
      (fun u : ℝ => (∑' k, coeff k * Complex.exp (mode k*(u : ℂ))) *
          Complex.exp (-w*(u : ℂ))) = fun u => target+off u := by
    funext u
    unfold target off
    rw [← tsum_mul_right, ← hmatchSummable.tsum_add (hOffSummable u)]
    apply tsum_congr
    intro k
    rw [mul_assoc, ← Complex.exp_add, ← add_mul, ← sub_eq_add_neg]
    by_cases hk : mode k = w <;> simp [matchCoeff, offCoeff, offMode, hk]
  obtain ⟨hi, hb⟩ := bounded_exponential_series_integral offCoeff offMode hOffCoeff
    hOffMode hδ hOffGap U (U+T)
  change IntervalIntegrable _ volume U (U+T) ∧ _
  dsimp only
  rw [hfun]
  refine ⟨intervalIntegrable_const.add hi, ?_⟩
  have hx : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  rw [intervalIntegral.integral_add intervalIntegrable_const hi, intervalIntegral.integral_const,
    show U+T-U = T by ring, Complex.real_smul]
  rw [show ((T : ℂ)*target + ∫ u in U..U+T, off u)/(T : ℂ)-target =
      (∫ u in U..U+T, off u)/(T : ℂ) by field_simp [hx]; ring]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  apply div_le_div_of_nonneg_right _ hT.le
  exact hb.trans (mul_le_mul_of_nonneg_right
    (hOffCoeff.tsum_le_tsum hoff hcoeff) (by positivity))

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
