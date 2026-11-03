/- GID: D5/S3/Fourier/Asymptotics/GaussianComplexMoments
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/GaussianComplexMoments
   mirror-E: none(waiver:analytic-identities-without-numeric-projection)
   anchors: []
   utility: none
   digest: Integrable complex Gaussian density moments of orders zero, one and two for arbitrary real mean and positive real variance. -/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
The Gaussian moment identities use arbitrary real mean and positive variance,
with no cubic or LowH branch. The probability-to-Lebesgue transport and the
derivatives of the entire MGF are proved here. Pinned Mathlib:
56a005855ea17e0b0958f73ec801ae140b0a1679.

Escape registration remains unfinished under issue #23906; no `declared_validated`
status is asserted for the four public moment theorems.
-/

noncomputable section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ComplexConjugate NNReal

namespace D5.S3.Fourier.Asymptotics.GaussianComplexMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The literal normalized Lebesgue density, with real variance parameter. -/
def gaussianDensity (μ v y : ℝ) : ℝ :=
  Real.exp (-(y - μ) ^ 2 / (2 * v)) / Real.sqrt (2 * Real.pi * v)

def tiltedMean (μ v : ℝ) (z : ℂ) : ℂ := (μ : ℂ) + (v : ℂ) * z

def gaussianExponent (μ v : ℝ) (z : ℂ) : ℂ :=
  (v : ℂ) * z ^ 2 / 2 + (μ : ℂ) * z

def gaussianMGF (μ v : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (gaussianExponent μ v z)

def densityMonomial (μ v : ℝ) (n : ℕ) (z : ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ n * (gaussianDensity μ v y : ℂ) * Complex.exp (z * (y : ℂ))

private def variance (v : ℝ) (hv : 0 < v) : ℝ≥0 := ⟨v, hv.le⟩

@[simp] private theorem variance_coe (v : ℝ) (hv : 0 < v) :
    (variance v hv : ℝ) = v := rfl

private theorem variance_ne_zero (v : ℝ) (hv : 0 < v) : variance v hv ≠ 0 := by
  intro h
  have hcoe : (variance v hv : ℝ) = 0 := by rw [h]; rfl
  exact hv.ne' hcoe

private theorem gaussianDensity_eq_pdf (μ v : ℝ) (hv : 0 < v) (y : ℝ) :
    gaussianDensity μ v y = gaussianPDFReal μ (variance v hv) y := by
  change Real.exp (-(y - μ) ^ 2 / (2 * v)) / Real.sqrt (2 * Real.pi * v) =
    (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(y - μ) ^ 2 / (2 * v))
  rw [div_eq_mul_inv, mul_comm]

private theorem hasDerivAt_tiltedMean (μ v : ℝ) (z : ℂ) :
    HasDerivAt (tiltedMean μ v) (v : ℂ) z := by
  change HasDerivAt (fun w : ℂ => (μ : ℂ) + (v : ℂ) * w) _ z
  simpa only [mul_one, id_eq] using
    ((hasDerivAt_id z).const_mul (v : ℂ)).const_add (μ : ℂ)

private theorem hasDerivAt_gaussianExponent (μ v : ℝ) (z : ℂ) :
    HasDerivAt (gaussianExponent μ v) (tiltedMean μ v z) z := by
  have h := ((((hasDerivAt_id z).pow 2).const_mul (v : ℂ)).div_const 2).add
    ((hasDerivAt_id z).const_mul (μ : ℂ))
  change HasDerivAt (gaussianExponent μ v) _ z at h
  exact h.congr_deriv (by dsimp [tiltedMean]; ring)

private theorem hasDerivAt_gaussianMGF (μ v : ℝ) (z : ℂ) :
    HasDerivAt (gaussianMGF μ v) (tiltedMean μ v z * gaussianMGF μ v z) z := by
  have h := (hasDerivAt_gaussianExponent μ v z).cexp
  exact h.congr_deriv (by dsimp [gaussianMGF]; ring)

private theorem hasDerivAt_gaussianMGF_first (μ v : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => tiltedMean μ v w * gaussianMGF μ v w)
      ((tiltedMean μ v z ^ 2 + (v : ℂ)) * gaussianMGF μ v z) z := by
  have h := (hasDerivAt_tiltedMean μ v z).mul (hasDerivAt_gaussianMGF μ v z)
  exact h.congr_deriv (by ring)

private theorem deriv_gaussianMGF (μ v : ℝ) :
    deriv (gaussianMGF μ v) = fun z : ℂ => tiltedMean μ v z * gaussianMGF μ v z := by
  funext z
  exact (hasDerivAt_gaussianMGF μ v z).deriv

private theorem iteratedDeriv_two_gaussianMGF (μ v : ℝ) :
    iteratedDeriv 2 (gaussianMGF μ v) = fun z : ℂ =>
      (tiltedMean μ v z ^ 2 + (v : ℂ)) * gaussianMGF μ v z := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
    iteratedDeriv_one, deriv_gaussianMGF]
  funext z
  exact (hasDerivAt_gaussianMGF_first μ v z).deriv

private theorem complexMGF_id_eq (μ v : ℝ) (hv : 0 < v) :
    complexMGF id (gaussianReal μ (variance v hv)) = gaussianMGF μ v := by
  funext z
  rw [complexMGF_id_gaussianReal]
  unfold gaussianMGF gaussianExponent
  congr 1
  simp only [variance_coe]
  ring

/-- Every tilted monomial used in the 0/1/2 moments is integrable, with no
integrability or moment premise. The degree parameter also pays the common
probability-to-density transport once. -/
theorem density_monomial_integrable (μ v : ℝ) (hv : 0 < v) (n : ℕ) (z : ℂ) :
    Integrable (densityMonomial μ v n z) := by
  have hbase : Integrable (fun y : ℝ => (y : ℂ) ^ n * Complex.exp (z * (y : ℂ)))
      (gaussianReal μ (variance v hv)) := by
    simpa only [id_eq, Complex.ofReal_pow] using
      (integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
        (X := id) (μ := gaussianReal μ (variance v hv)) (z := z) (by simp) n)
  rw [gaussianReal_of_var_ne_zero _ (variance_ne_zero v hv)] at hbase
  have htransport :=
    (integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF μ (variance v hv))
      (ae_of_all volume fun _ => gaussianPDF_lt_top)).mp hbase
  refine htransport.congr (ae_of_all volume fun y => ?_)
  simp only [toReal_gaussianPDF, Complex.real_smul]
  rw [densityMonomial, gaussianDensity_eq_pdf μ v hv y]
  ring

private theorem density_moment_eq_iteratedDeriv
    (μ v : ℝ) (hv : 0 < v) (n : ℕ) (z : ℂ) :
    (∫ y : ℝ, densityMonomial μ v n z y) = iteratedDeriv n (gaussianMGF μ v) z := by
  have hmoment := iteratedDeriv_complexMGF
    (X := id) (μ := gaussianReal μ (variance v hv)) (z := z) (by simp) n
  rw [complexMGF_id_eq μ v hv] at hmoment
  calc
    _ = ∫ y : ℝ, (y : ℂ) ^ n * Complex.exp (z * (y : ℂ))
          ∂(gaussianReal μ (variance v hv)) := by
      rw [integral_gaussianReal_eq_integral_smul (variance_ne_zero v hv)]
      apply integral_congr_ae
      exact ae_of_all volume fun y => by
        simp only [Complex.real_smul]
        rw [densityMonomial, gaussianDensity_eq_pdf μ v hv y]
        ring
    _ = iteratedDeriv n (gaussianMGF μ v) z := by
      simpa only [id_eq, Complex.ofReal_pow] using hmoment.symm

theorem density_moment_zero (μ v : ℝ) (hv : 0 < v) (z : ℂ) :
    (∫ y : ℝ, densityMonomial μ v 0 z y) = gaussianMGF μ v z := by
  rw [density_moment_eq_iteratedDeriv μ v hv, iteratedDeriv_zero]

theorem density_moment_one (μ v : ℝ) (hv : 0 < v) (z : ℂ) :
    (∫ y : ℝ, densityMonomial μ v 1 z y) = tiltedMean μ v z * gaussianMGF μ v z := by
  rw [density_moment_eq_iteratedDeriv μ v hv, iteratedDeriv_one]
  exact (hasDerivAt_gaussianMGF μ v z).deriv

theorem density_moment_two (μ v : ℝ) (hv : 0 < v) (z : ℂ) :
    (∫ y : ℝ, densityMonomial μ v 2 z y) =
      (tiltedMean μ v z ^ 2 + (v : ℂ)) * gaussianMGF μ v z := by
  rw [density_moment_eq_iteratedDeriv μ v hv, iteratedDeriv_two_gaussianMGF]

end D5.S3.Fourier.Asymptotics.GaussianComplexMoments

end
