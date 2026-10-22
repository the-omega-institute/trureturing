/- GID: D5/S3/Arith/Robin/CompleteLowHGaussianMoment
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/CompleteLowHGaussianMoment
   mirror-E: none(waiver:analytic identity and bounds have no numeric evidence projection)
   anchors: []
   utility: none
   digest: The exact normalized cubic Gaussian moment for every complex parameter.

   For every real m > 0, real gamma and complex z, the normalized cubic
   Gaussian integral has center 16*m and variance 2*m. Its exact value is
     ((16*m+2*m*z+1)*(z^2+gamma^2+1+1/(2*m))+2*z)*exp(m*z^2+16*m*z).
   The source retains density transport, monomial integrability, derivatives
   of the entire complex MGF, and the complete +2*z covariance correction.
   Analytic inputs include Mathlib complexMGF_id_gaussianReal,
   integrableExpSet_id_gaussianReal, iteratedDeriv_complexMGF,
   integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet,
   integral_gaussianReal_eq_integral_smul and
   integrable_withDensity_iff_integrable_smul'.
   Pinned upstream: Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
   No strip, height, sign or finite-family hypothesis restricts this identity.




-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

noncomputable section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ComplexConjugate NNReal

namespace D5.S3.Arith.Robin.CompleteLowHGaussianMoment

set_option autoImplicit false

def centre (m : ℝ) : ℝ := 16 * m

/-- Construct the variance only after receiving the actual positivity hypothesis. -/
def variance (m : ℝ) (hm : 0 < m) : ℝ≥0 :=
  ⟨2 * m, le_of_lt (mul_pos (by norm_num) hm)⟩

@[simp] theorem variance_coe (m : ℝ) (hm : 0 < m) :
    (variance m hm : ℝ) = 2 * m := rfl

theorem variance_ne_zero (m : ℝ) (hm : 0 < m) : variance m hm ≠ 0 := by
  intro h
  have hcoe : (variance m hm : ℝ) = 0 := by rw [h]; rfl
  change 2 * m = 0 at hcoe
  exact (mul_ne_zero (by norm_num) hm.ne') hcoe

def gaussianDensity (m y : ℝ) : ℝ :=
  Real.exp (-(y - centre m) ^ 2 / (4 * m)) / Real.sqrt (4 * Real.pi * m)

def gaussianCoordinate (m y : ℝ) : ℝ := (y - centre m) / (2 * m)

def tiltedMean (m : ℝ) (z : ℂ) : ℂ :=
  (centre m : ℂ) + (2 * (m : ℂ)) * z

def gaussianExponent (m : ℝ) (z : ℂ) : ℂ :=
  (m : ℂ) * z ^ 2 + (centre m : ℂ) * z

def gaussianMGF (m : ℝ) (z : ℂ) : ℂ := Complex.exp (gaussianExponent m z)

def densityMonomial (m : ℝ) (n : ℕ) (z : ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ n * (gaussianDensity m y : ℂ) * Complex.exp (z * (y : ℂ))

def cubicPolynomial (m γ : ℝ) (z : ℂ) : ℂ :=
  (tiltedMean m z + 1) *
      (z ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * (m : ℂ))) + 2 * z

def cubicGaussianMoment (m γ : ℝ) (z : ℂ) : ℂ :=
  cubicPolynomial m γ z * gaussianMGF m z

def coefficient3 (m : ℝ) : ℂ := (4 * (m : ℂ) ^ 2)⁻¹

def coefficient2 (m : ℝ) : ℂ := (1 - 2 * (centre m : ℂ)) * coefficient3 m

def coefficient1 (m γ : ℝ) : ℂ :=
  ((centre m : ℂ) ^ 2 - 2 * (centre m : ℂ)) * coefficient3 m + (γ : ℂ) ^ 2 + 1

def coefficient0 (m γ : ℝ) : ℂ :=
  (centre m : ℂ) ^ 2 * coefficient3 m + (γ : ℂ) ^ 2 + 1

/-! Explicit derivatives of the entire Gaussian MGF. -/

private theorem hasDerivAt_tiltedMean (m : ℝ) (z : ℂ) :
    HasDerivAt (tiltedMean m) (2 * (m : ℂ)) z := by
  change HasDerivAt (fun w : ℂ => (centre m : ℂ) + (2 * (m : ℂ)) * w) _ z
  simpa only [mul_one, id_eq] using
    ((hasDerivAt_id z).const_mul (2 * (m : ℂ))).const_add (centre m : ℂ)

private theorem hasDerivAt_gaussianExponent (m : ℝ) (z : ℂ) :
    HasDerivAt (gaussianExponent m) (tiltedMean m z) z := by
  have h := (((hasDerivAt_id z).pow 2).const_mul (m : ℂ)).add
    ((hasDerivAt_id z).const_mul (centre m : ℂ))
  change HasDerivAt (gaussianExponent m) _ z at h
  exact h.congr_deriv (by dsimp [tiltedMean]; ring)

private theorem hasDerivAt_gaussianMGF (m : ℝ) (z : ℂ) :
    HasDerivAt (gaussianMGF m) (tiltedMean m z * gaussianMGF m z) z := by
  have h := (hasDerivAt_gaussianExponent m z).cexp
  exact h.congr_deriv (by dsimp [gaussianMGF]; ring)

private theorem hasDerivAt_gaussianMGF_first (m : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => tiltedMean m w * gaussianMGF m w)
      ((tiltedMean m z ^ 2 + 2 * (m : ℂ)) * gaussianMGF m z) z := by
  have h := (hasDerivAt_tiltedMean m z).mul (hasDerivAt_gaussianMGF m z)
  exact h.congr_deriv (by ring)

private theorem hasDerivAt_gaussianMGF_second (m : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ =>
        (tiltedMean m w ^ 2 + 2 * (m : ℂ)) * gaussianMGF m w)
      ((tiltedMean m z ^ 3 + 3 * (2 * (m : ℂ)) * tiltedMean m z) *
        gaussianMGF m z) z := by
  have hp := ((hasDerivAt_tiltedMean m z).pow 2).add
    (hasDerivAt_const z (2 * (m : ℂ)))
  have h := hp.mul (hasDerivAt_gaussianMGF m z)
  exact h.congr_deriv (by dsimp; ring)

private theorem deriv_gaussianMGF (m : ℝ) :
    deriv (gaussianMGF m) = fun z : ℂ => tiltedMean m z * gaussianMGF m z := by
  funext z
  exact (hasDerivAt_gaussianMGF m z).deriv

theorem iteratedDeriv_two_gaussianMGF (m : ℝ) :
    iteratedDeriv 2 (gaussianMGF m) = fun z : ℂ =>
      (tiltedMean m z ^ 2 + 2 * (m : ℂ)) * gaussianMGF m z := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
    iteratedDeriv_one, deriv_gaussianMGF]
  funext z
  exact (hasDerivAt_gaussianMGF_first m z).deriv

theorem iteratedDeriv_three_gaussianMGF (m : ℝ) :
    iteratedDeriv 3 (gaussianMGF m) = fun z : ℂ =>
      (tiltedMean m z ^ 3 + 3 * (2 * (m : ℂ)) * tiltedMean m z) *
        gaussianMGF m z := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
    iteratedDeriv_two_gaussianMGF]
  funext z
  exact (hasDerivAt_gaussianMGF_second m z).deriv

/-! The exact probability measure and its density, with all type side conditions paid. -/

theorem gaussianDensity_eq_pdf (m : ℝ) (hm : 0 < m) (y : ℝ) :
    gaussianDensity m y = gaussianPDFReal (centre m) (variance m hm) y := by
  change Real.exp (-(y - centre m) ^ 2 / (4 * m)) / Real.sqrt (4 * Real.pi * m) =
    (Real.sqrt (2 * Real.pi * (2 * m)))⁻¹ *
      Real.exp (-(y - centre m) ^ 2 / (2 * (2 * m)))
  rw [show 2 * Real.pi * (2 * m) = 4 * Real.pi * m by ring,
    show 2 * (2 * m) = 4 * m by ring]
  rw [div_eq_mul_inv, mul_comm]

theorem complexMGF_id_eq (m : ℝ) (hm : 0 < m) :
    complexMGF id (gaussianReal (centre m) (variance m hm)) = gaussianMGF m := by
  funext z
  rw [complexMGF_id_gaussianReal]
  unfold gaussianMGF gaussianExponent
  congr 1
  simp only [variance_coe, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- Every tilted polynomial moment is integrable for every complex parameter.
    No moment or integrability certificate is assumed. -/
theorem density_monomial_integrable (m : ℝ) (hm : 0 < m) (n : ℕ) (z : ℂ) :
    Integrable (densityMonomial m n z) := by
  have hbase : Integrable (fun y : ℝ => (y : ℂ) ^ n * Complex.exp (z * (y : ℂ)))
      (gaussianReal (centre m) (variance m hm)) := by
    simpa only [id_eq, Complex.ofReal_pow] using
      (integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
        (X := id) (μ := gaussianReal (centre m) (variance m hm))
        (z := z) (by simp) n)
  rw [gaussianReal_of_var_ne_zero _ (variance_ne_zero m hm)] at hbase
  have htransport :=
    (integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF (centre m) (variance m hm))
      (ae_of_all volume fun _ => gaussianPDF_lt_top)).mp hbase
  refine htransport.congr (ae_of_all volume fun y => ?_)
  simp only [toReal_gaussianPDF, Complex.real_smul]
  rw [densityMonomial, gaussianDensity_eq_pdf m hm y]
  ring

/-- Exact iterated-derivative identity after transport from the Gaussian measure
    to the stated, normalized Lebesgue density. -/
theorem density_moment_eq_iteratedDeriv
    (m : ℝ) (hm : 0 < m) (n : ℕ) (z : ℂ) :
    (∫ y : ℝ, densityMonomial m n z y) = iteratedDeriv n (gaussianMGF m) z := by
  have hmoment := iteratedDeriv_complexMGF
    (X := id) (μ := gaussianReal (centre m) (variance m hm)) (z := z) (by simp) n
  rw [complexMGF_id_eq m hm] at hmoment
  calc
    _ = ∫ y : ℝ, (y : ℂ) ^ n * Complex.exp (z * (y : ℂ))
          ∂(gaussianReal (centre m) (variance m hm)) := by
      rw [integral_gaussianReal_eq_integral_smul (variance_ne_zero m hm)]
      apply integral_congr_ae
      exact ae_of_all volume fun y => by
        simp only [Complex.real_smul]
        rw [densityMonomial, gaussianDensity_eq_pdf m hm y]
        ring
    _ = iteratedDeriv n (gaussianMGF m) z := by
      simpa only [id_eq, Complex.ofReal_pow] using hmoment.symm

theorem density_moment_zero (m : ℝ) (hm : 0 < m) (z : ℂ) :
    (∫ y : ℝ, densityMonomial m 0 z y) = gaussianMGF m z := by
  rw [density_moment_eq_iteratedDeriv m hm, iteratedDeriv_zero]

theorem density_moment_one (m : ℝ) (hm : 0 < m) (z : ℂ) :
    (∫ y : ℝ, densityMonomial m 1 z y) = tiltedMean m z * gaussianMGF m z := by
  rw [density_moment_eq_iteratedDeriv m hm, iteratedDeriv_one]
  exact (hasDerivAt_gaussianMGF m z).deriv

theorem density_moment_two (m : ℝ) (hm : 0 < m) (z : ℂ) :
    (∫ y : ℝ, densityMonomial m 2 z y) =
      (tiltedMean m z ^ 2 + 2 * (m : ℂ)) * gaussianMGF m z := by
  rw [density_moment_eq_iteratedDeriv m hm, iteratedDeriv_two_gaussianMGF]

theorem density_moment_three (m : ℝ) (hm : 0 < m) (z : ℂ) :
    (∫ y : ℝ, densityMonomial m 3 z y) =
      (tiltedMean m z ^ 3 + 3 * (2 * (m : ℂ)) * tiltedMean m z) *
        gaussianMGF m z := by
  rw [density_moment_eq_iteratedDeriv m hm, iteratedDeriv_three_gaussianMGF]

/-! Finite, justified linear combination of the four actual density moments. -/

private theorem cubic_integrand_expansion
    {m γ : ℝ} (hm : m ≠ 0) (z : ℂ) (y : ℝ) :
    ((y + 1 : ℝ) : ℂ) *
        ((gaussianCoordinate m y) ^ 2 + γ ^ 2 + 1 : ℝ) *
        (gaussianDensity m y : ℂ) * Complex.exp (z * (y : ℂ)) =
      coefficient3 m * densityMonomial m 3 z y +
        coefficient2 m * densityMonomial m 2 z y +
        coefficient1 m γ * densityMonomial m 1 z y +
        coefficient0 m γ * densityMonomial m 0 z y := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  dsimp [densityMonomial, gaussianCoordinate, coefficient3,
    coefficient2, coefficient1, coefficient0]
  push_cast
  field_simp [hmC] <;> ring

private theorem cubic_moment_polynomial {m γ : ℝ} (hm : m ≠ 0) (z : ℂ) :
    coefficient3 m *
        (tiltedMean m z ^ 3 + 3 * (2 * (m : ℂ)) * tiltedMean m z) +
      coefficient2 m * (tiltedMean m z ^ 2 + 2 * (m : ℂ)) +
      coefficient1 m γ * tiltedMean m z + coefficient0 m γ =
        cubicPolynomial m γ z := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  dsimp [coefficient3, coefficient2, coefficient1, coefficient0,
    cubicPolynomial, tiltedMean]
  field_simp [hmC] <;> ring

theorem cubic_gaussian_integrable (m γ : ℝ) (hm : 0 < m) (z : ℂ) :
    Integrable (fun y : ℝ =>
      ((y + 1 : ℝ) : ℂ) *
        ((gaussianCoordinate m y) ^ 2 + γ ^ 2 + 1 : ℝ) *
        (gaussianDensity m y : ℂ) * Complex.exp (z * (y : ℂ))) := by
  have hi0 := (density_monomial_integrable m hm 0 z).const_mul (coefficient0 m γ)
  have hi1 := (density_monomial_integrable m hm 1 z).const_mul (coefficient1 m γ)
  have hi2 := (density_monomial_integrable m hm 2 z).const_mul (coefficient2 m)
  have hi3 := (density_monomial_integrable m hm 3 z).const_mul (coefficient3 m)
  refine (((hi3.add hi2).add hi1).add hi0).congr (ae_of_all volume fun y => ?_)
  exact (cubic_integrand_expansion hm.ne' z y).symm

/-- The full-complex normalized cubic Gaussian identity.  The only mathematical
    hypothesis is m > 0; γ is any real and z is any complex number. -/
theorem cubic_gaussian_moment (m γ : ℝ) (hm : 0 < m) (z : ℂ) :
    (∫ y : ℝ,
      ((y + 1 : ℝ) : ℂ) *
        ((gaussianCoordinate m y) ^ 2 + γ ^ 2 + 1 : ℝ) *
        (gaussianDensity m y : ℂ) * Complex.exp (z * (y : ℂ))) =
      cubicGaussianMoment m γ z := by
  have hi0 := (density_monomial_integrable m hm 0 z).const_mul (coefficient0 m γ)
  have hi1 := (density_monomial_integrable m hm 1 z).const_mul (coefficient1 m γ)
  have hi2 := (density_monomial_integrable m hm 2 z).const_mul (coefficient2 m)
  have hi3 := (density_monomial_integrable m hm 3 z).const_mul (coefficient3 m)
  calc
    _ = ∫ y : ℝ,
        coefficient3 m * densityMonomial m 3 z y +
          coefficient2 m * densityMonomial m 2 z y +
          coefficient1 m γ * densityMonomial m 1 z y +
          coefficient0 m γ * densityMonomial m 0 z y := by
      apply integral_congr_ae
      exact ae_of_all volume fun y => cubic_integrand_expansion hm.ne' z y
    _ = coefficient3 m * (∫ y : ℝ, densityMonomial m 3 z y) +
        coefficient2 m * (∫ y : ℝ, densityMonomial m 2 z y) +
        coefficient1 m γ * (∫ y : ℝ, densityMonomial m 1 z y) +
        coefficient0 m γ * (∫ y : ℝ, densityMonomial m 0 z y) := by
      have h32 := integral_add hi3 hi2
      have h321 := integral_add (hi3.add hi2) hi1
      have h3210 := integral_add ((hi3.add hi2).add hi1) hi0
      simp only [Pi.add_apply] at h32 h321 h3210
      rw [h3210, h321, h32]
      simp only [integral_const_mul]
    _ = cubicGaussianMoment m γ z := by
      rw [density_moment_zero m hm, density_moment_one m hm,
        density_moment_two m hm, density_moment_three m hm]
      calc
        _ = (coefficient3 m *
                (tiltedMean m z ^ 3 + 3 * (2 * (m : ℂ)) * tiltedMean m z) +
              coefficient2 m * (tiltedMean m z ^ 2 + 2 * (m : ℂ)) +
              coefficient1 m γ * tiltedMean m z + coefficient0 m γ) *
                gaussianMGF m z := by ring
        _ = cubicGaussianMoment m γ z := by
          rw [cubic_moment_polynomial hm.ne' z]
          rfl

/-- Expanded public endpoint: the literal real density and the complete +2*z
    covariance correction, with no certificate parameter. -/
theorem cubic_gaussian_moment_explicit (m γ : ℝ) (hm : 0 < m) (z : ℂ) :
    (∫ y : ℝ,
      (((y + 1) * (((y - 16 * m) / (2 * m)) ^ 2 + γ ^ 2 + 1) *
        Real.exp (-(y - 16 * m) ^ 2 / (4 * m)) /
        Real.sqrt (4 * Real.pi * m) : ℝ) : ℂ) * Complex.exp (z * (y : ℂ))) =
      (((16 : ℂ) * (m : ℂ) + 2 * (m : ℂ) * z + 1) *
        (z ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * (m : ℂ))) + 2 * z) *
          Complex.exp ((m : ℂ) * z ^ 2 + 16 * (m : ℂ) * z) := by
  calc
    _ = ∫ y : ℝ,
        ((y + 1 : ℝ) : ℂ) *
          ((gaussianCoordinate m y) ^ 2 + γ ^ 2 + 1 : ℝ) *
          (gaussianDensity m y : ℂ) * Complex.exp (z * (y : ℂ)) := by
      apply integral_congr_ae
      exact ae_of_all volume fun y => by
        dsimp [gaussianCoordinate, gaussianDensity, centre]
        push_cast
        ring
    _ = cubicGaussianMoment m γ z := cubic_gaussian_moment m γ hm z
    _ = _ := by
      simp only [cubicGaussianMoment, cubicPolynomial, tiltedMean,
        gaussianMGF, gaussianExponent, centre, Complex.ofReal_mul,
        Complex.ofReal_ofNat]

end D5.S3.Arith.Robin.CompleteLowHGaussianMoment
