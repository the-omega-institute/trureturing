/- GID: D5/S3/Arith/Robin/OriginalGaussianIntegralBudgets
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/OriginalGaussianIntegralBudgets
   mirror-E: none(waiver:analytic-proof-without-numeric-projection)
   anchors: []
   utility: none
   digest: Quantitative complete Gaussian localization for the original positive-U theorem. -/
/- SOURCE IMPLEMENTATION ONLY. Original F5: whole Hv, positive central
   response, complete nonnegative exterior, and the entire negative axis.
   No integral is used without a preceding integrability proof. -/
import D5.S3.Arith.Robin.ActualGaussianEnvelopeMassBudget
import D5.S3.Fourier.Asymptotics.GaussianComplexMoments
import D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange
open D5.S3.Weil.ZeroData.ActualGaussianZeroSum
open D5.S3.Arith.Robin.ActualGaussianEnvelopeMassBudget

namespace D5.S3.Arith.Robin.OriginalGaussianIntegralBudgets

/- Consumed density and moment support; scalar even moments are reused from
RemyDegenne/brownian-motion (Apache-2.0), commit
0d5b6eb928e616d3b1f774ad7d233c167d9f42c9, through the attributed supplier. -/
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

/-- The project supplier already contains the scalar even-moment proof and
its RemyDegenne/brownian-motion attribution.  Only n=1 and n=2 are used here. -/
private theorem pdf_moments
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
private def g (m M y : ℝ) : ℝ :=
  Real.exp (-(y - M) ^ 2 / (4 * m)) / Real.sqrt (4 * Real.pi * m)

private theorem g_nonneg (m M y : ℝ) : 0 ≤ g m M y := by
  unfold g
  positivity

private theorem g_eq_pdf (m M : ℝ) (hm : 0 < m) (y : ℝ) :
    g m M y = gaussianPDFReal M (variance m hm) y := by
  change Real.exp (-(y - M) ^ 2 / (4 * m)) / Real.sqrt (4 * Real.pi * m) =
    (Real.sqrt (2 * Real.pi * (2 * m)))⁻¹ *
      Real.exp (-(y - M) ^ 2 / (2 * (2 * m)))
  rw [show 2 * Real.pi * (2 * m) = 4 * Real.pi * m by ring,
    show 2 * (2 * m) = 4 * m by ring]
  ring

private theorem g_power_integrable (m M : ℝ) (hm : 0 < m) (n : ℕ) :
    Integrable (fun y : ℝ => (y - M) ^ n * g m M y) := by
  have hc := D5.S3.Fourier.Asymptotics.GaussianComplexMoments.density_monomial_integrable
    0 (2 * m) (by positivity) n 0
  have hr : Integrable (fun y : ℝ => y ^ n *
      D5.S3.Fourier.Asymptotics.GaussianComplexMoments.gaussianDensity 0 (2 * m) y) := by
    convert hc.re using 1
    funext y
    simp only [D5.S3.Fourier.Asymptotics.GaussianComplexMoments.densityMonomial,
      zero_mul, Complex.exp_zero, mul_one]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  simpa only [D5.S3.Fourier.Asymptotics.GaussianComplexMoments.gaussianDensity,
    g, sub_zero, show 2 * (2 * m) = 4 * m by ring,
    show 2 * Real.pi * (2 * m) = 4 * Real.pi * m by ring] using hr.comp_sub_right M

private theorem g_integrable (m M : ℝ) (hm : 0 < m) : Integrable (g m M) := by
  simpa only [pow_zero, one_mul] using g_power_integrable m M hm 0

private theorem g_integral (m M : ℝ) (hm : 0 < m) : (∫ y : ℝ, g m M y) = 1 := by
  have h0 : (∫ y : ℝ, (1 : ℝ) ∂gaussianReal M (variance m hm)) = 1 := by simp
  rw [integral_gaussianReal_eq_integral_smul (variance_ne_zero m hm)] at h0
  simpa only [smul_eq_mul, mul_one, ← g_eq_pdf m M hm] using h0

private theorem g_second_fourth (m M : ℝ) (hm : 0 < m) :
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

private theorem polynomial_integrable (m M A B C : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ =>
      (A + B * (y - M) ^ 2 + C * (y - M) ^ 4) * g m M y) := by
  have h0 := (g_integrable m M hm).const_mul A
  have h2 := (g_power_integrable m M hm 2).const_mul B
  have h4 := (g_power_integrable m M hm 4).const_mul C
  refine ((h0.add h2).add h4).congr (ae_of_all volume fun y => ?_)
  simp only [Pi.add_apply]
  ring

private theorem polynomial_integral (m M A B C : ℝ) (hm : 0 < m) :
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
private theorem gaussian_tilt (m t y : ℝ) (hm : 0 < m) :
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
private theorem gaussian_split (m M y : ℝ) (hm : 0 < m) :
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

/-- A pointwise exterior estimate for the exact normalized density. -/
private theorem gaussian_split_le (m M y c : ℝ) (hm : 0 < m)
    (hd : 8 * c * m ^ 2 ≤ (y - M) ^ 2) :
    g m M y ≤ (3 / 2 : ℝ) * Real.exp (-c * m) * g (2 * m) M y := by
  have hsqrt : Real.sqrt 2 ≤ (3 : ℝ) / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  rw [gaussian_split m M y hm]
  have he : Real.exp (-(y - M) ^ 2 / (8 * m)) ≤ Real.exp (-c * m) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * m)).2
    nlinarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hsqrt he (Real.exp_nonneg _) (by norm_num)) (g_nonneg _ _ _)

/-- Set-integral comparison retains the exact domain and pays positive
integrability, rather than relying on totalized Bochner integrals. -/
private theorem set_integral_le_full {f G : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hf : IntegrableOn f s) (hG : Integrable G)
    (hGn : ∀ y, 0 ≤ G y) (hle : ∀ y ∈ s, f y ≤ G y) :
    (∫ y in s, f y) ≤ ∫ y : ℝ, G y := by
  have hp : ∀ᵐ y ∂volume.restrict s, f y ≤ G y := by
    filter_upwards [ae_restrict_mem hs] with y hy
    exact hle y hy
  exact (integral_mono_ae hf hG.integrableOn hp).trans
    (setIntegral_le_integral hG (ae_of_all volume hGn))

def b (y : ℝ) : ℝ := (4 * y + 11) * Real.exp (y / 2)

theorem V_nonneg (m γ y : ℝ) : 0 ≤ gaussianV m γ y := by
  dsimp [gaussianV, gaussianDensity]
  positivity

/-- Global polynomial-Gaussian integrability includes the sign change of b
on the negative axis; positive-axis bounds will be taken on the exact set. -/
theorem bv_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => b y * gaussianV m γ y) := by
  -- The literal degree-three product is paid locally from ordinary natural
  -- Gaussian polynomial integrability; no retired cubic supplier is imported.
  let M : ℝ := 17 * m
  let L : ℝ := 68 * m + 11
  let c₀ : ℝ := L * (γ ^ 2 + 5 / 4)
  let c₁ : ℝ := L / (2 * m) + 4 * γ ^ 2 + 5
  let c₂ : ℝ := L / (4 * m ^ 2) + 2 / m
  let c₃ : ℝ := 1 / m ^ 2
  have h₀ := (g_power_integrable m M hm 0).const_mul c₀
  have h₁ := (g_power_integrable m M hm 1).const_mul c₁
  have h₂ := (g_power_integrable m M hm 2).const_mul c₂
  have h₃ := (g_power_integrable m M hm 3).const_mul c₃
  have hpoly := (((h₀.add h₁).add h₂).add h₃).const_mul
    (2 * Real.exp (33 * m / 4))
  refine hpoly.congr (ae_of_all volume fun y => ?_)
  dsimp only [Pi.add_apply]
  have htilt : Real.exp (y / 2) * gaussianDensity m y =
      Real.exp (33 * m / 4) * g m M y := by
    have harg₁ : (1 / 2 : ℝ) * y = y / 2 := by ring
    have harg₂ : m * (1 / 2 : ℝ) ^ 2 + 16 * m * (1 / 2) = 33 * m / 4 := by ring
    have harg₃ : 16 * m + 2 * m * (1 / 2 : ℝ) = 17 * m := by ring
    simpa only [harg₁, harg₂, harg₃, M] using gaussian_tilt m (1 / 2) y hm
  have he : b y * gaussianV m γ y =
      2 * ((4 * y + 11) * (gaussianU m y ^ 2 + γ ^ 2 + 1)) *
        (Real.exp (y / 2) * gaussianDensity m y) := by
    dsimp [b, gaussianV]
    ring
  rw [he, htilt]
  dsimp [M, L, c₀, c₁, c₂, c₃, gaussianU]
  field_simp [hm.ne']
  <;> ring

/-- This pays absolute-product integrability on the WHOLE real axis,
and hence on both exterior domains. Positivity of v is used explicitly. -/
theorem abs_Hv_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => |(H y).re| * gaussianV m γ y) := by
  have hi := (H_real_V_product_integrable m γ hm).norm
  refine hi.congr (ae_of_all volume fun y => ?_)
  dsimp
  rw [abs_mul, abs_of_nonneg (V_nonneg m γ y)]

private def centralMajorant (m γ y : ℝ) : ℝ :=
  2 * Real.exp (33 * m / 4) *
    ((81 * m + 2 * (y - 17 * m) ^ 2) *
      (γ ^ 2 + 2 + (y - 17 * m) ^ 2 / (2 * m ^ 2)) * g m (17 * m) y)

private theorem central_expansion (m γ y : ℝ) (hm : 0 < m) :
    centralMajorant m γ y = 2 * Real.exp (33 * m / 4) *
      ((81 * m * (γ ^ 2 + 2) +
        (2 * (γ ^ 2 + 2) + 81 / (2 * m)) * (y - 17 * m) ^ 2 +
        (1 / m ^ 2) * (y - 17 * m) ^ 4) * g m (17 * m) y) := by
  dsimp [centralMajorant]
  field_simp [hm.ne'] <;> ring

private theorem central_majorant_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (centralMajorant m γ) := by
  have hi := (polynomial_integrable m (17 * m) (81 * m * (γ ^ 2 + 2))
    (2 * (γ ^ 2 + 2) + 81 / (2 * m)) (1 / m ^ 2) hm).const_mul
      (2 * Real.exp (33 * m / 4))
  exact hi.congr (ae_of_all volume fun y => (central_expansion m γ y hm).symm)

private theorem central_majorant_integral (m γ : ℝ) (hm : 0 < m) :
    (∫ y : ℝ, centralMajorant m γ y) =
      2 * Real.exp (33 * m / 4) * (85 * m * (γ ^ 2 + 2) + 93) := by
  simp_rw [central_expansion m γ _ hm]
  rw [integral_const_mul, polynomial_integral m (17 * m)
    (81 * m * (γ ^ 2 + 2)) (2 * (γ ^ 2 + 2) + 81 / (2 * m)) (1 / m ^ 2) hm]
  field_simp [hm.ne'] <;> ring

private theorem central_pointwise (m γ y : ℝ) (hm : 1 ≤ m) (hy : 0 < y) :
    b y * gaussianV m γ y ≤ centralMajorant m γ y := by
  have hmpos : 0 < m := by linarith
  let z := y - 17 * m
  have hlin : 4 * y + 11 ≤ 81 * m + 2 * z ^ 2 := by
    dsimp only [z]
    nlinarith [sq_nonneg (y - 17 * m - 1)]
  have hu : gaussianU m y = z / (2 * m) + 1 / 2 := by
    dsimp [gaussianU, z]
    field_simp [hmpos.ne'] <;> ring
  have hz : z ^ 2 / (2 * m ^ 2) = 2 * (z / (2 * m)) ^ 2 := by
    field_simp [hmpos.ne'] <;> ring
  have hpoly : gaussianU m y ^ 2 + γ ^ 2 + 1 ≤
      γ ^ 2 + 2 + z ^ 2 / (2 * m ^ 2) := by
    rw [hu, hz]
    nlinarith [sq_nonneg (z / (2 * m) - 1 / 2)]
  have ht := gaussian_tilt m (1 / 2) y hmpos
  have ht' : Real.exp (y / 2) * gaussianDensity m y =
      Real.exp (33 * m / 4) * g m (17 * m) y := by
    convert ht using 1 <;> ring
  have hg : 0 ≤ g m (17 * m) y := g_nonneg _ _ _
  have hmul : (4 * y + 11) * (gaussianU m y ^ 2 + γ ^ 2 + 1) ≤
      (81 * m + 2 * z ^ 2) * (γ ^ 2 + 2 + z ^ 2 / (2 * m ^ 2)) :=
    mul_le_mul hlin hpoly (by positivity) (by positivity)
  calc
    _ = 2 * ((4 * y + 11) * (gaussianU m y ^ 2 + γ ^ 2 + 1)) *
        (Real.exp (y / 2) * gaussianDensity m y) := by dsimp [b, gaussianV]; ring
    _ = 2 * ((4 * y + 11) * (gaussianU m y ^ 2 + γ ^ 2 + 1)) *
        (Real.exp (33 * m / 4) * g m (17 * m) y) := by rw [ht']
    _ ≤ 2 * ((81 * m + 2 * z ^ 2) * (γ ^ 2 + 2 + z ^ 2 / (2 * m ^ 2))) *
        (Real.exp (33 * m / 4) * g m (17 * m) y) := by
      gcongr
    _ = _ := by dsimp [centralMajorant, z]; ring

theorem central_original (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    (∫ y in Ioi 0, b y * gaussianV m γ y) ≤
      300 * m * (γ + 10) ^ 2 * Real.exp (33 * m / 4) := by
  have hmpos : 0 < m := by linarith
  have hle := set_integral_le_full measurableSet_Ioi
    (bv_integrable m γ hmpos).integrableOn (central_majorant_integrable m γ hmpos)
    (fun y => by dsimp [centralMajorant, g]; positivity)
    (fun y hy => central_pointwise m γ y hm hy)
  rw [central_majorant_integral m γ hmpos] at hle
  have hconst : 2 * (85 * m * (γ ^ 2 + 2) + 93) ≤ 300 * m * (γ + 10) ^ 2 := by
    have hg : 0 ≤ γ := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg γ),
      mul_nonneg (sub_nonneg.mpr hm) hg, sq_nonneg γ]
  exact hle.trans (by
    nlinarith [mul_le_mul_of_nonneg_right hconst (Real.exp_nonneg (33 * m / 4))])

private def positiveMajorant (m γ y : ℝ) : ℝ :=
  6 * Real.exp (9 * m / 2) *
    (((γ + 10) ^ 2 + (y - 18 * m) ^ 2 / (2 * m ^ 2)) * g (2 * m) (18 * m) y)

private def negativeMajorant (m γ y : ℝ) : ℝ :=
  6 * Real.exp (-32 * m) *
    (((γ + 10) ^ 2 + (y - 16 * m) ^ 2 / (4 * m ^ 2)) * g (2 * m) (16 * m) y)

private theorem quadratic_integrable (m M A B : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => (A + B * (y - M) ^ 2) * g m M y) := by
  simpa only [zero_mul, add_zero] using polynomial_integrable m M A B 0 hm

private theorem quadratic_integral (m M A B : ℝ) (hm : 0 < m) :
    (∫ y : ℝ, (A + B * (y - M) ^ 2) * g m M y) = A + B * (2 * m) := by
  simpa only [zero_mul, add_zero] using polynomial_integral m M A B 0 hm

private theorem positive_majorant_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (positiveMajorant m γ) := by
  refine ((quadratic_integrable (2 * m) (18 * m) ((γ + 10) ^ 2) ((2 * m ^ 2)⁻¹)
      (by positivity)).const_mul (6 * Real.exp (9 * m / 2))).congr
    (ae_of_all volume fun y => ?_)
  dsimp [positiveMajorant]
  field_simp [hm.ne']

private theorem negative_majorant_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (negativeMajorant m γ) := by
  refine ((quadratic_integrable (2 * m) (16 * m) ((γ + 10) ^ 2) ((4 * m ^ 2)⁻¹)
      (by positivity)).const_mul (6 * Real.exp (-32 * m))).congr
    (ae_of_all volume fun y => ?_)
  dsimp [negativeMajorant]
  field_simp [hm.ne']

private theorem positive_majorant_integral (m γ : ℝ) (hm : 0 < m) :
    (∫ y : ℝ, positiveMajorant m γ y) =
      6 * Real.exp (9 * m / 2) * ((γ + 10) ^ 2 + 2 / m) := by
  have he : positiveMajorant m γ = fun y => 6 * Real.exp (9 * m / 2) *
      (((γ + 10) ^ 2 + (2 * m ^ 2)⁻¹ * (y - 18 * m) ^ 2) * g (2 * m) (18 * m) y) := by
    funext y
    dsimp [positiveMajorant]
    ring
  rw [he, integral_const_mul, quadratic_integral _ _ _ _ (by positivity : 0 < 2 * m)]
  field_simp [hm.ne'] <;> ring

private theorem negative_majorant_integral (m γ : ℝ) (hm : 0 < m) :
    (∫ y : ℝ, negativeMajorant m γ y) =
      6 * Real.exp (-32 * m) * ((γ + 10) ^ 2 + 1 / m) := by
  have he : negativeMajorant m γ = fun y => 6 * Real.exp (-32 * m) *
      (((γ + 10) ^ 2 + (4 * m ^ 2)⁻¹ * (y - 16 * m) ^ 2) * g (2 * m) (16 * m) y) := by
    funext y
    dsimp [negativeMajorant]
    ring
  rw [he, integral_const_mul, quadratic_integral _ _ _ _ (by positivity : 0 < 2 * m)]
  field_simp [hm.ne'] <;> ring

private theorem positive_exterior_pointwise (m γ y : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (hy : y ∈ Ici 0 \ Icc (4 * m) (28 * m)) :
    |(H y).re| * gaussianV m γ y ≤ positiveMajorant m γ y := by
  have hmpos : 0 < m := by linarith
  have hy0 : 0 ≤ y := hy.1
  have hyout : y < 4 * m ∨ 28 * m < y := by
    simpa only [mem_Icc, not_and_or, not_le] using hy.2
  have hzsq : 100 * m ^ 2 ≤ (y - 18 * m) ^ 2 := by
    rcases hyout with hylo | hyhi
    · nlinarith [mul_nonneg (by linarith : 0 ≤ 8 * m - y)
        (by linarith : 0 ≤ 28 * m - y)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ y - 8 * m)
        (by linarith : 0 ≤ y - 28 * m)]
  have hsplit := gaussian_split_le m (18 * m) y (25 / 2) hmpos (by nlinarith)
  have hu : gaussianU m y = (y - 18 * m) / (2 * m) + 1 := by
    dsimp [gaussianU]
    field_simp [hmpos.ne'] <;> ring
  have hz : (y - 18 * m) ^ 2 / (2 * m ^ 2) =
      2 * ((y - 18 * m) / (2 * m)) ^ 2 := by field_simp [hmpos.ne'] <;> ring
  have hp : gaussianU m y ^ 2 + γ ^ 2 + 1 ≤
      (γ + 10) ^ 2 + (y - 18 * m) ^ 2 / (2 * m ^ 2) := by
    rw [hu, hz]
    nlinarith [sq_nonneg ((y - 18 * m) / (2 * m) - 1)]
  have hH : |(H y).re| ≤ 2 * Real.exp y := by
    simpa only [max_eq_left hy0] using H_re_abs_le y
  have ht : Real.exp y * gaussianDensity m y = Real.exp (17 * m) * g m (18 * m) y := by
    convert gaussian_tilt m 1 y hmpos using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_right hH (V_nonneg m γ y)
  calc
    _ ≤ 2 * Real.exp y * gaussianV m γ y := hmul
    _ = 4 * (gaussianU m y ^ 2 + γ ^ 2 + 1) *
        (Real.exp y * gaussianDensity m y) := by dsimp [gaussianV]; ring
    _ = 4 * (gaussianU m y ^ 2 + γ ^ 2 + 1) * Real.exp (17 * m) *
        g m (18 * m) y := by rw [ht]; ring
    _ ≤ 4 * ((γ + 10) ^ 2 + (y - 18 * m) ^ 2 / (2 * m ^ 2)) *
        Real.exp (17 * m) *
        ((3 / 2) * Real.exp (-(25 / 2) * m) * g (2 * m) (18 * m) y) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num))
          (Real.exp_nonneg _)) hsplit (g_nonneg _ _ _) (by positivity)
    _ = _ := by
      have he : Real.exp (17 * m) * Real.exp (-(25 / 2) * m) = Real.exp (9 * m / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      dsimp [positiveMajorant]
      calc
        _ = 6 * (Real.exp (17 * m) * Real.exp (-(25 / 2) * m)) *
            (((γ + 10) ^ 2 + (y - 18 * m) ^ 2 / (2 * m ^ 2)) *
              g (2 * m) (18 * m) y) := by ring
        _ = _ := by rw [he]

private theorem negative_exterior_pointwise (m γ y : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (hy : y < 0) : |(H y).re| * gaussianV m γ y ≤ negativeMajorant m γ y := by
  have hmpos : 0 < m := by linarith
  have hzsq : 256 * m ^ 2 ≤ (y - 16 * m) ^ 2 := by
    nlinarith [mul_nonneg (neg_nonneg.mpr hy.le) (by linarith : 0 ≤ 32 * m - y)]
  have hs := gaussian_split_le m (16 * m) y 32 hmpos (by nlinarith)
  have hH : |(H y).re| ≤ 2 := by
    simpa only [max_eq_right hy.le, Real.exp_zero, mul_one] using H_re_abs_le y
  have hu : gaussianU m y ^ 2 = (y - 16 * m) ^ 2 / (4 * m ^ 2) := by
    dsimp [gaussianU]
    field_simp [hmpos.ne'] <;> ring
  have hp : gaussianU m y ^ 2 + γ ^ 2 + 1 ≤
      (γ + 10) ^ 2 + (y - 16 * m) ^ 2 / (4 * m ^ 2) := by
    rw [hu]
    nlinarith
  have hd : gaussianDensity m y = g m (16 * m) y := rfl
  calc
    _ ≤ 2 * gaussianV m γ y := mul_le_mul_of_nonneg_right hH (V_nonneg m γ y)
    _ = 4 * (gaussianU m y ^ 2 + γ ^ 2 + 1) * g m (16 * m) y := by
      dsimp [gaussianV]
      rw [hd]
      ring
    _ ≤ 4 * ((γ + 10) ^ 2 + (y - 16 * m) ^ 2 / (4 * m ^ 2)) *
        ((3 / 2) * Real.exp (-32 * m) * g (2 * m) (16 * m) y) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) hs
        (g_nonneg _ _ _) (by positivity)
    _ = _ := by dsimp [negativeMajorant]; ring

theorem nonnegative_exterior_original (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    (∫ y in Ici 0 \ Icc (4 * m) (28 * m), |(H y).re| * gaussianV m γ y) ≤
      12 * (γ + 10) ^ 2 * Real.exp (9 * m / 2) := by
  have hmpos : 0 < m := by linarith
  have hle := set_integral_le_full (measurableSet_Ici.diff measurableSet_Icc)
    (abs_Hv_integrable m γ hmpos).integrableOn (positive_majorant_integrable m γ hmpos)
    (fun y => by dsimp [positiveMajorant, g]; positivity)
    (fun y hy => positive_exterior_pointwise m γ y hm hγ hy)
  rw [positive_majorant_integral m γ hmpos] at hle
  have hinv : 1 / m ≤ (1 : ℝ) := (div_le_one hmpos).2 hm
  have hDsq : 400 < (γ + 10) ^ 2 := by nlinarith [hγ]
  have hinv0 : 0 ≤ 1 / m := by positivity
  have htwo : 2 / m ≤ (2 : ℝ) := by
    calc
      2 / m = 2 * (1 / m) := by ring
      _ ≤ 2 := by nlinarith
  have hconst : 6 * ((γ + 10) ^ 2 + 2 / m) ≤ 12 * (γ + 10) ^ 2 := by
    nlinarith [hDsq, htwo]
  exact hle.trans (by
    nlinarith [mul_le_mul_of_nonneg_right hconst (Real.exp_nonneg (9 * m / 2))])

theorem negative_exterior_original (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    (∫ y in Iio 0, |(H y).re| * gaussianV m γ y) ≤
      8 * (γ + 10) ^ 2 * Real.exp (-32 * m) := by
  have hmpos : 0 < m := by linarith
  have hle := set_integral_le_full measurableSet_Iio
    (abs_Hv_integrable m γ hmpos).integrableOn (negative_majorant_integrable m γ hmpos)
    (fun y => by dsimp [negativeMajorant, g]; positivity)
    (fun y hy => negative_exterior_pointwise m γ y hm hγ hy)
  rw [negative_majorant_integral m γ hmpos] at hle
  have hinv : 1 / m ≤ (1 : ℝ) := (div_le_one hmpos).2 hm
  have hDsq : 400 < (γ + 10) ^ 2 := by nlinarith [hγ]
  have hconst : 6 * ((γ + 10) ^ 2 + 1 / m) ≤ 8 * (γ + 10) ^ 2 := by
    nlinarith [hDsq, hinv]
  exact hle.trans (by
    nlinarith [mul_le_mul_of_nonneg_right hconst (Real.exp_nonneg (-32 * m))])

/-- Exact set decomposition for localization; 0 goes to the nonnegative
exterior, and both closed interval endpoints remain in the central set. -/
theorem exterior_decomposition (m : ℝ) (hm : 1 ≤ m) :
    (Icc (4 * m) (28 * m))ᶜ =
      (Ici 0 \ Icc (4 * m) (28 * m)) ∪ Iio 0 := by
  ext y
  simp only [mem_compl_iff, mem_Icc, mem_union, mem_diff, mem_Ici, mem_Iio]
  constructor
  · intro hy
    rcases le_or_gt 0 y with hy0 | hy0
    · exact Or.inl ⟨hy0, hy⟩
    · exact Or.inr hy0
  · rintro (⟨_, hy⟩ | hy)
    · exact hy
    · rintro ⟨hy4, _⟩
      linarith

theorem exterior_disjoint (m : ℝ) :
    Disjoint (Ici 0 \ Icc (4 * m) (28 * m)) (Iio (0 : ℝ)) := by
  apply disjoint_left.mpr
  intro y hy hy'
  change y < 0 at hy'
  exact (not_lt_of_ge hy.1) hy'

/-- Ordinary Lebesgue endpoint transport, justified by nonatomic volume. -/
theorem central_zero_endpoint (m γ : ℝ) :
    (∫ y in Ici 0, b y * gaussianV m γ y) =
      ∫ y in Ioi 0, b y * gaussianV m γ y := by
  exact integral_Ici_eq_integral_Ioi

end D5.S3.Arith.Robin.OriginalGaussianIntegralBudgets
