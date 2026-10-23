/- SOURCE IMPLEMENTATION ONLY. Original F5: whole Hv, positive central
   response, complete nonnegative exterior, and the entire negative axis.
   No integral is used without a preceding integrability proof. -/
import D5.S3.Arith.Robin.ActualGaussianEnvelopeMassBudget
import D5.S3.Analytic.OriginalGaussianMoments
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange
open D5.S3.Weil.ZeroData.ActualGaussianMass
open D5.S3.Analytic.OriginalGaussianMoments
open D5.S3.Arith.Robin.ActualGaussianEnvelopeMassBudget

namespace D5.S3.Arith.Robin.OriginalGaussianIntegralBudgets

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
