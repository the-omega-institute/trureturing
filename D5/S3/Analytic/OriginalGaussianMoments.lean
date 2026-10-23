/- SOURCE ONLY. Density transport and even-moment bodies use the pinned
   countable Gaussian fourth-moment supplier, which attributes the scalar
   even-moment proof to RemyDegenne/brownian-motion (Apache 2.0).
   New estimates use Lebesgue integrability before integral comparison. -/
import D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange
import D5.S3.Fourier.Asymptotics.GaussianComplexMoments
import D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange

namespace D5.S3.Analytic.OriginalGaussianMoments

/- Local NNReal view of the current natural Gaussian's variance 2*m.  This
   adapter is deliberately private and does not recreate the retired module. -/
private def variance (m : ℝ) (hm : 0 < m) : ℝ≥0 := ⟨2 * m, by positivity⟩

@[simp] private theorem variance_coe (m : ℝ) (hm : 0 < m) :
    (variance m hm : ℝ) = 2 * m := rfl

private theorem variance_ne_zero (m : ℝ) (hm : 0 < m) : variance m hm ≠ 0 := by
  intro h
  have hcoe : (variance m hm : ℝ) = 0 := by rw [h]; rfl
  have hm2 : 0 < 2 * m := by positivity
  exact hm2.ne' (by simpa only [variance_coe] using hcoe)

theorem pdf_power_integrable
    (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (n : ℕ) :
    Integrable (fun y : ℝ => ProbabilityTheory.gaussianPDFReal μ v y * (y - μ) ^ n) := by
  have hLp : MemLp (fun y : ℝ => y - μ) n (ProbabilityTheory.gaussianReal μ v) := by
    simpa only [Pi.sub_def, id_eq, ENNReal.coe_natCast] using
      (ProbabilityTheory.memLp_id_gaussianReal (μ := μ) (v := v) (n : ℝ≥0)).sub
        (memLp_const μ)
  have hpow : Integrable (fun y : ℝ => (y - μ) ^ n)
      (ProbabilityTheory.gaussianReal μ v) := by
    apply hLp.integrable_norm_pow'.mono' (hLp.aestronglyMeasurable.pow n)
    exact ae_of_all _ fun y => (norm_pow (y - μ) n).le
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero _ hv] at hpow
  have htransport := (integrable_withDensity_iff_integrable_smul'
    (ProbabilityTheory.measurable_gaussianPDF μ v)
    (ae_of_all volume fun _ => ProbabilityTheory.gaussianPDF_lt_top)).mp hpow
  simpa only [ProbabilityTheory.toReal_gaussianPDF, smul_eq_mul] using htransport

/-- The project supplier already contains the scalar even-moment proof and
its RemyDegenne/brownian-motion attribution.  Only n=1 and n=2 are used here. -/
theorem pdf_moments
    (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ y : ℝ, ProbabilityTheory.gaussianPDFReal μ v y * (y - μ) ^ 2) = (v : ℝ) ∧
    (∫ y : ℝ, ProbabilityTheory.gaussianPDFReal μ v y * (y - μ) ^ 4) = 3 * (v : ℝ) ^ 2 := by
  have hs : (NNReal.sqrt v : ℝ) ^ 2 = (v : ℝ) := by
    exact_mod_cast NNReal.sq_sqrt v
  have hs4 : (NNReal.sqrt v : ℝ) ^ 4 = (v : ℝ) ^ 2 := by
    calc
      _ = ((NNReal.sqrt v : ℝ) ^ 2) ^ 2 := by ring
      _ = (v : ℝ) ^ 2 := by rw [hs]
  have h2 := D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment.centralMoment_two_mul
    μ (NNReal.sqrt v) 1
  have h4 := D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment.centralMoment_two_mul
    μ (NNReal.sqrt v) 2
  have h2' : (∫ y : ℝ, (y - μ) ^ 2 ∂ProbabilityTheory.gaussianReal μ v) = (v : ℝ) := by
    simpa only [ProbabilityTheory.centralMoment, id_eq,
      ProbabilityTheory.integral_id_gaussianReal, Pi.pow_apply, Pi.sub_apply,
      show (2 * 1 : ℕ) = 2 by rfl, show (2 * 1 - 1 : ℕ) = 1 by rfl,
      NNReal.sq_sqrt, show Nat.doubleFactorial 1 = 1 by decide,
      Nat.cast_one, mul_one, hs] using h2
  have h4' : (∫ y : ℝ, (y - μ) ^ 4 ∂ProbabilityTheory.gaussianReal μ v) =
      3 * (v : ℝ) ^ 2 := by
    simpa only [ProbabilityTheory.centralMoment, id_eq,
      ProbabilityTheory.integral_id_gaussianReal, Pi.pow_apply, Pi.sub_apply,
      show (2 * 2 : ℕ) = 4 by rfl, show (2 * 2 - 1 : ℕ) = 3 by rfl,
      NNReal.sq_sqrt, show Nat.doubleFactorial 3 = 3 by decide,
      Nat.cast_ofNat, hs4, mul_comm] using h4
  constructor
  · rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv] at h2'
    simpa only [smul_eq_mul] using h2'
  · rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv] at h4'
    simpa only [smul_eq_mul] using h4'

/-- Mean M, variance 2m, with its literal normalization. -/
def g (m M y : ℝ) : ℝ :=
  Real.exp (-(y - M) ^ 2 / (4 * m)) / Real.sqrt (4 * Real.pi * m)

theorem g_nonneg (m M y : ℝ) : 0 ≤ g m M y := by
  unfold g
  positivity

theorem g_eq_pdf (m M : ℝ) (hm : 0 < m) (y : ℝ) :
    g m M y = gaussianPDFReal M (variance m hm) y := by
  change Real.exp (-(y - M) ^ 2 / (4 * m)) / Real.sqrt (4 * Real.pi * m) =
    (Real.sqrt (2 * Real.pi * (2 * m)))⁻¹ *
      Real.exp (-(y - M) ^ 2 / (2 * (2 * m)))
  rw [show 2 * Real.pi * (2 * m) = 4 * Real.pi * m by ring,
    show 2 * (2 * m) = 4 * m by ring]
  ring

theorem g_power_integrable (m M : ℝ) (hm : 0 < m) (n : ℕ) :
    Integrable (fun y : ℝ => (y - M) ^ n * g m M y) := by
  have hi := pdf_power_integrable M (variance m hm) (variance_ne_zero m hm) n
  simpa only [← g_eq_pdf m M hm, mul_comm] using hi

theorem g_integrable (m M : ℝ) (hm : 0 < m) : Integrable (g m M) := by
  simpa only [pow_zero, one_mul] using g_power_integrable m M hm 0

theorem g_integral (m M : ℝ) (hm : 0 < m) : (∫ y : ℝ, g m M y) = 1 := by
  have h0 : (∫ y : ℝ, (1 : ℝ) ∂gaussianReal M (variance m hm)) = 1 := by simp
  rw [integral_gaussianReal_eq_integral_smul (variance_ne_zero m hm)] at h0
  simpa only [smul_eq_mul, mul_one, ← g_eq_pdf m M hm] using h0

theorem g_second_fourth (m M : ℝ) (hm : 0 < m) :
    (∫ y : ℝ, (y - M) ^ 2 * g m M y) = 2 * m ∧
    (∫ y : ℝ, (y - M) ^ 4 * g m M y) = 12 * m ^ 2 := by
  obtain ⟨h2, h4⟩ := pdf_moments M (variance m hm) (variance_ne_zero m hm)
  constructor
  · simpa only [← g_eq_pdf m M hm, variance_coe, mul_comm] using h2
  · have h4' : (∫ y : ℝ, (y - M) ^ 4 * g m M y) = 3 * (2 * m) ^ 2 := by
      simpa only [← g_eq_pdf m M hm, variance_coe, mul_comm] using h4
    calc
      _ = 3 * (2 * m) ^ 2 := h4'
      _ = 12 * m ^ 2 := by ring

theorem polynomial_integrable (m M A B C : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ =>
      (A + B * (y - M) ^ 2 + C * (y - M) ^ 4) * g m M y) := by
  have h0 := (g_integrable m M hm).const_mul A
  have h2 := (g_power_integrable m M hm 2).const_mul B
  have h4 := (g_power_integrable m M hm 4).const_mul C
  refine ((h0.add h2).add h4).congr (ae_of_all volume fun y => ?_)
  simp only [Pi.add_apply]
  ring

theorem polynomial_integral (m M A B C : ℝ) (hm : 0 < m) :
    (∫ y : ℝ, (A + B * (y - M) ^ 2 + C * (y - M) ^ 4) * g m M y) =
      A + B * (2 * m) + C * (12 * m ^ 2) := by
  have h0 := (g_integrable m M hm).const_mul A
  have h2 := (g_power_integrable m M hm 2).const_mul B
  have h4 := (g_power_integrable m M hm 4).const_mul C
  calc
    (∫ y : ℝ, (A + B * (y - M) ^ 2 + C * (y - M) ^ 4) * g m M y) =
        ∫ y : ℝ, A * g m M y + B * ((y - M) ^ 2 * g m M y) +
          C * ((y - M) ^ 4 * g m M y) := by
      apply integral_congr_ae
      exact ae_of_all volume fun y => by ring
    _ = ((∫ y : ℝ, A * g m M y) +
        ∫ y : ℝ, B * ((y - M) ^ 2 * g m M y)) +
          ∫ y : ℝ, C * ((y - M) ^ 4 * g m M y) := by
      have hadd2 : (∫ y : ℝ, A * g m M y + B * ((y - M) ^ 2 * g m M y)) =
          (∫ y : ℝ, A * g m M y) + ∫ y : ℝ, B * ((y - M) ^ 2 * g m M y) := by
        simpa only [Pi.add_apply] using integral_add h0 h2
      have hadd3 : (∫ y : ℝ, A * g m M y + B * ((y - M) ^ 2 * g m M y) +
          C * ((y - M) ^ 4 * g m M y)) =
          (∫ y : ℝ, A * g m M y + B * ((y - M) ^ 2 * g m M y)) +
            ∫ y : ℝ, C * ((y - M) ^ 4 * g m M y) := by
        simpa only [Pi.add_apply] using integral_add (h0.add h2) h4
      exact hadd3.trans (congrArg
        (fun z => z + ∫ y : ℝ, C * ((y - M) ^ 4 * g m M y)) hadd2)
    _ = _ := by
      have h0eq : (∫ y : ℝ, A * g m M y) = A := by
        rw [integral_const_mul, g_integral m M hm, mul_one]
      have h2eq : (∫ y : ℝ, B * ((y - M) ^ 2 * g m M y)) = B * (2 * m) := by
        rw [integral_const_mul, (g_second_fourth m M hm).1]
      have h4eq : (∫ y : ℝ, C * ((y - M) ^ 4 * g m M y)) = C * (12 * m ^ 2) := by
        rw [integral_const_mul, (g_second_fourth m M hm).2]
      calc
        _ = A + (∫ y : ℝ, B * ((y - M) ^ 2 * g m M y)) +
            ∫ y : ℝ, C * ((y - M) ^ 4 * g m M y) := by rw [h0eq]
        _ = A + B * (2 * m) +
            ∫ y : ℝ, C * ((y - M) ^ 4 * g m M y) := by rw [h2eq]
        _ = _ := by rw [h4eq]

/-- Exact Gaussian tilt, before taking a whole-line or half-line integral. -/
theorem gaussian_tilt (m t y : ℝ) (hm : 0 < m) :
    Real.exp (t * y) * gaussianDensity m y =
      Real.exp (m * t ^ 2 + 16 * m * t) * g m (16 * m + 2 * m * t) y := by
  have he : t * y + -(y - 16 * m) ^ 2 / (4 * m) =
      (m * t ^ 2 + 16 * m * t) +
        -(y - (16 * m + 2 * m * t)) ^ 2 / (4 * m) := by
    field_simp [hm.ne'] <;> ring
  dsimp [gaussianDensity, g]
  calc
    _ = Real.exp (t * y + -(y - 16 * m) ^ 2 / (4 * m)) /
        Real.sqrt (4 * Real.pi * m) := by rw [Real.exp_add]; ring
    _ = _ := by rw [he, Real.exp_add]; ring

/-- Splitting a normalized Gaussian into two equal exponent factors.
The sqrt(2) normalization is paid explicitly. -/
theorem gaussian_split (m M y : ℝ) (hm : 0 < m) :
    g m M y = Real.sqrt 2 * Real.exp (-(y - M) ^ 2 / (8 * m)) * g (2 * m) M y := by
  have hs : Real.sqrt (4 * Real.pi * (2 * m)) =
      Real.sqrt 2 * Real.sqrt (4 * Real.pi * m) := by
    rw [show 4 * Real.pi * (2 * m) = 2 * (4 * Real.pi * m) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have he : -(y - M) ^ 2 / (4 * m) =
      -(y - M) ^ 2 / (8 * m) + -(y - M) ^ 2 / (8 * m) := by
    field_simp [hm.ne'] <;> ring
  unfold g
  rw [hs, he, Real.exp_add, show 4 * (2 * m) = 8 * m by ring]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne',
    (Real.sqrt_pos.mpr (by positivity : 0 < 4 * Real.pi * m)).ne'] <;> ring

theorem sqrt_two_le : Real.sqrt 2 ≤ (3 : ℝ) / 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- A pointwise exterior estimate for the exact normalized density. -/
theorem gaussian_split_le (m M y c : ℝ) (hm : 0 < m)
    (hd : 8 * c * m ^ 2 ≤ (y - M) ^ 2) :
    g m M y ≤ (3 / 2 : ℝ) * Real.exp (-c * m) * g (2 * m) M y := by
  rw [gaussian_split m M y hm]
  have he : Real.exp (-(y - M) ^ 2 / (8 * m)) ≤ Real.exp (-c * m) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * m)).2
    nlinarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul sqrt_two_le he (Real.exp_nonneg _) (by norm_num)) (g_nonneg _ _ _)

/-- Set-integral comparison retains the exact domain and pays positive
integrability, rather than relying on totalized Bochner integrals. -/
theorem set_integral_le_full {f G : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hf : IntegrableOn f s) (hG : Integrable G)
    (hGn : ∀ y, 0 ≤ G y) (hle : ∀ y ∈ s, f y ≤ G y) :
    (∫ y in s, f y) ≤ ∫ y : ℝ, G y := by
  have hp : ∀ᵐ y ∂volume.restrict s, f y ≤ G y := by
    filter_upwards [ae_restrict_mem hs] with y hy
    exact hle y hy
  exact (integral_mono_ae hf hG.integrableOn hp).trans
    (setIntegral_le_integral hG (ae_of_all volume hGn))

end D5.S3.Analytic.OriginalGaussianMoments

