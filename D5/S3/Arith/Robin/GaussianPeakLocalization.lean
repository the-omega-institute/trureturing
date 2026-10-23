/- GID: D5/S3/Arith/Robin/GaussianPeakLocalization
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/GaussianPeakLocalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed Gaussian localization bounds a response when no positive peak occurs. -/

import D5.S3.Arith.Robin.FullZeroGaussianResponse
import D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment

/-! The signed response retains all three regions and the full envelope integral. -/

namespace D5.S3.Arith.Robin.GaussianPeakLocalization

open MeasureTheory ProbabilityTheory Set Real
open FullZeroGaussianResponse
open scoped NNReal ENNReal

noncomputable section

private theorem density_moments (m M : ℝ) (hm : 0 < m) :
    (∀ n : ℕ, Integrable (fun y : ℝ => (y - M) ^ n * density m M y)) ∧
    (∫ y : ℝ, density m M y) = 1 ∧
    (∫ y : ℝ, (y - M) ^ 2 * density m M y) = 2 * m ∧
    (∫ y : ℝ, (y - M) ^ 4 * density m M y) = 12 * m ^ 2 := by
  let v : ℝ≥0 := ⟨2 * m, by positivity⟩
  let σ : ℝ≥0 := ⟨sqrt (2 * m), sqrt_nonneg _⟩
  have hv : v ≠ 0 := by
    intro h
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    change 2 * m = 0 at this
    linarith
  have hσ : σ ^ 2 = v := by
    ext
    exact sq_sqrt (by positivity)
  have hd (y : ℝ) : gaussianPDFReal M v y = density m M y := by
    change (sqrt (2 * Real.pi * (2 * m)))⁻¹ *
      exp (-(y - M)^2 / (2 * (2*m))) = _
    unfold density
    rw [show 2 * Real.pi * (2 * m) = 4 * Real.pi * m by ring,
      show 2 * (2 * m) = 4 * m by ring]
    ring
  have hi (n : ℕ) : Integrable (fun y : ℝ => (y - M) ^ n) (gaussianReal M v) := by
    have hLp : MemLp (fun y : ℝ => y - M) n (gaussianReal M v) :=
      (memLp_id_gaussianReal' (n : ℝ≥0∞) (by simp)).sub (memLp_const M)
    exact hLp.integrable_norm_pow'.mono' (by fun_prop)
      (Filter.Eventually.of_forall fun y => by simp [norm_pow])
  have htransfer (n : ℕ) :
      (∫ y, (y - M) ^ n ∂gaussianReal M v) =
        ∫ y : ℝ, (y - M) ^ n * density m M y := by
    rw [integral_gaussianReal_eq_integral_smul hv]
    simp only [hd, smul_eq_mul, mul_comm]
  have heven (n : ℕ) :=
    D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment.centralMoment_two_mul
      M σ n
  simp only [centralMoment, id_eq, integral_id_gaussianReal, Pi.pow_apply, Pi.sub_apply,
    hσ] at heven
  have h2 := heven 1
  have h4 := heven 2
  simp only [htransfer] at h2 h4
  have hs2 : (σ : ℝ) ^ 2 = 2 * m := sq_sqrt (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have h := hi n
    rw [gaussianReal_of_var_ne_zero M hv] at h
    have h' := (integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF M v) (ae_of_all _ fun _ => gaussianPDF_lt_top)).mp h
    simpa only [toReal_gaussianPDF, hd, smul_eq_mul, mul_comm] using h'
  · simpa only [hd] using integral_gaussianPDFReal_eq_one M hv
  · norm_num [Nat.doubleFactorial] at h2
    simpa only [hs2, mul_one] using h2
  · norm_num [Nat.doubleFactorial] at h4
    rw [show (σ : ℝ) ^ 4 = ((σ : ℝ) ^ 2) ^ 2 by ring, hs2] at h4
    nlinarith only [h4]

private theorem polynomial_integral (m M A B C : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ =>
      (A + B * (y - M) ^ 2 + C * (y - M) ^ 4) * density m M y) ∧
    (∫ y : ℝ, (A + B * (y - M) ^ 2 + C * (y - M) ^ 4) * density m M y) =
      A + B * (2 * m) + C * (12 * m ^ 2) := by
  obtain ⟨hi, h0, h2, h4⟩ := density_moments m M hm
  have hi0 : Integrable (density m M) := by simpa using hi 0
  have heq (y : ℝ) :
      (A + B * (y - M) ^ 2 + C * (y - M) ^ 4) * density m M y =
        A * density m M y + B * ((y - M) ^ 2 * density m M y) +
          C * ((y - M) ^ 4 * density m M y) := by ring
  simp_rw [heq]
  exact ⟨((hi0.const_mul A).add ((hi 2).const_mul B)).add ((hi 4).const_mul C), by
    rw [integral_add (f := fun y => A * density m M y + B * ((y-M)^2 * density m M y))
      ((hi0.const_mul A).add ((hi 2).const_mul B)) ((hi 4).const_mul C),
      integral_add (hi0.const_mul A) ((hi 2).const_mul B), integral_const_mul,
      integral_const_mul, integral_const_mul, h0, h2, h4, mul_one]⟩

private theorem tilted_density (m M t y : ℝ) (hm : 0 < m) :
    exp (t * y) * density m M y =
      exp (m * t ^ 2 + M * t) * density m (M + 2 * m * t) y := by
  simp only [density, ← mul_div_assoc, ← exp_add]
  congr 2
  field_simp
  <;> ring

private theorem tail_density (m M y c : ℝ) (hm : 0 < m)
    (htail : 8 * m * c ≤ (y - M) ^ 2) :
    density m M y ≤ 2 * exp (-c) * density (2 * m) M y := by
  have hs : 0 < sqrt (4 * Real.pi * m) := sqrt_pos.2 (by positivity)
  have hs' : 0 < sqrt (4 * Real.pi * (2 * m)) := sqrt_pos.2 (by positivity)
  have hsle : sqrt (4 * Real.pi * (2 * m)) ≤ 2 * sqrt (4 * Real.pi * m) := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    rw [sq_sqrt (by positivity), mul_pow, sq_sqrt (by positivity)]
    nlinarith [Real.pi_pos]
  have hexp : exp (-(y - M) ^ 2 / (4 * m)) ≤
      exp (-c) * exp (-(y - M) ^ 2 / (4 * (2 * m))) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 8 * m)).mp
    field_simp
    nlinarith only [htail]
  unfold density
  apply (div_le_iff₀ hs).2
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply (le_div_iff₀ hs').2
  nlinarith [mul_le_mul_of_nonneg_left hsle (exp_pos (-(y - M) ^ 2 / (4 * m))).le,
    mul_le_mul_of_nonneg_right hexp (by positivity : 0 ≤ 2 * sqrt (4 * Real.pi * m))]

private def peakMajorant (m γ y : ℝ) : ℝ :=
  4 * exp (33 * m / 4) *
    ((81 * m + 2 * (y - 17 * m) ^ 2) *
      (γ ^ 2 + 3 / 2 + (y - 17 * m) ^ 2 / (2 * m ^ 2))) * density m (17 * m) y

private def rightMajorant (m γ y : ℝ) : ℝ :=
  16 * exp (9 * m / 2) * ((γ + 10) ^ 2 + (y - 18 * m) ^ 2 / (2 * m ^ 2)) *
    density (2 * m) (18 * m) y

private def leftMajorant (m γ y : ℝ) : ℝ :=
  16 * exp (-32 * m) * (γ ^ 2 + 1 + (y - 16 * m) ^ 2 / (4 * m ^ 2)) *
    density (2 * m) (16 * m) y

private theorem majorant_integrals {m γ : ℝ} (hm : 1 ≤ m) (hγ : 10 < γ) :
    Integrable (peakMajorant m γ) ∧ Integrable (rightMajorant m γ) ∧
    Integrable (leftMajorant m γ) ∧
    (∫ y, peakMajorant m γ y) ≤ 600 * m * (γ + 10) ^ 2 * exp (33 * m / 4) ∧
    (∫ y, rightMajorant m γ y) ≤ 24 * (γ + 10) ^ 2 * exp (9 * m / 2) ∧
    (∫ y, leftMajorant m γ y) ≤ 16 * (γ + 10) ^ 2 * exp (-32 * m) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < 2 * m := by positivity
  obtain ⟨hiP, hP⟩ := polynomial_integral m (17 * m)
    (81 * m * (γ ^ 2 + 3 / 2)) (81 / (2 * m) + 2 * (γ ^ 2 + 3 / 2))
    (1 / m ^ 2) hm0
  obtain ⟨hiR, hR⟩ := polynomial_integral (2 * m) (18 * m)
    ((γ + 10) ^ 2) (1 / (2 * m ^ 2)) 0 hm2
  obtain ⟨hiL, hL⟩ := polynomial_integral (2 * m) (16 * m)
    (γ ^ 2 + 1) (1 / (4 * m ^ 2)) 0 hm2
  have heP (y : ℝ) : peakMajorant m γ y = 4 * exp (33 * m / 4) *
      ((81 * m * (γ ^ 2 + 3 / 2) +
        (81 / (2 * m) + 2 * (γ ^ 2 + 3 / 2)) * (y - 17 * m) ^ 2 +
        (1 / m ^ 2) * (y - 17 * m) ^ 4) * density m (17 * m) y) := by
    unfold peakMajorant
    field_simp
    <;> ring
  have heR (y : ℝ) : rightMajorant m γ y = 16 * exp (9 * m / 2) *
      (((γ + 10) ^ 2 + (1 / (2 * m ^ 2)) * (y - 18 * m) ^ 2 +
        0 * (y - 18 * m) ^ 4) * density (2 * m) (18 * m) y) := by
    unfold rightMajorant
    ring
  have heL (y : ℝ) : leftMajorant m γ y = 16 * exp (-32 * m) *
      ((γ ^ 2 + 1 + (1 / (4 * m ^ 2)) * (y - 16 * m) ^ 2 +
        0 * (y - 16 * m) ^ 4) * density (2 * m) (16 * m) y) := by
    unfold leftMajorant
    ring
  have hPeval : (∫ y, peakMajorant m γ y) =
      4 * exp (33 * m / 4) * (85 * m * (γ ^ 2 + 3 / 2) + 93) := by
    simp_rw [heP]
    rw [integral_const_mul, hP]
    congr 1
    field_simp
    <;> ring
  have hReval : (∫ y, rightMajorant m γ y) =
      16 * exp (9 * m / 2) * ((γ + 10) ^ 2 + 2 / m) := by
    simp_rw [heR]
    rw [integral_const_mul, hR]
    congr 1
    field_simp
    <;> ring
  have hLeval : (∫ y, leftMajorant m γ y) =
      16 * exp (-32 * m) * (γ ^ 2 + 1 + 1 / m) := by
    simp_rw [heL]
    rw [integral_const_mul, hL]
    congr 1
    field_simp
    <;> ring
  have hinv : 1 / m ≤ 1 := (div_le_iff₀ hm0).2 (by linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Integrable (fun y => peakMajorant m γ y)
    simp_rw [heP]; exact hiP.const_mul _
  · change Integrable (fun y => rightMajorant m γ y)
    simp_rw [heR]; exact hiR.const_mul _
  · change Integrable (fun y => leftMajorant m γ y)
    simp_rw [heL]; exact hiL.const_mul _
  · rw [hPeval]
    have hc : 85 * m * (γ ^ 2 + 3 / 2) + 93 ≤ 150 * m * (γ + 10) ^ 2 := by
      nlinarith [mul_nonneg hm0.le (sq_nonneg γ), mul_nonneg hm0.le (by linarith : 0 ≤ γ)]
    nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 4 * exp (33 * m / 4))]
  · rw [hReval]
    have hc : (γ + 10) ^ 2 + 2 / m ≤ (3 / 2) * (γ + 10) ^ 2 := by
      simp only [div_eq_mul_inv] at hinv ⊢
      nlinarith [sq_nonneg γ]
    nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 16 * exp (9 * m / 2))]
  · rw [hLeval]
    have hc : γ ^ 2 + 1 + 1 / m ≤ (γ + 10) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 16 * exp (-32 * m))]

private theorem response_majorant (H : ℝ → ℝ) {m γ : ℝ} (hm : 1 ≤ m) (hγ : 10 < γ)
    (hgrowth : ∀ y, |H y| ≤ 2 * exp (max y 0))
    (hkernel : ∀ y, 0 ≤ envelope m (16 * m) γ y ∧
      |kernel m (16 * m) γ y| ≤ envelope m (16 * m) γ y)
    (hnopeak : ∀ y ∈ Icc (4 * m) (28 * m), H y ≤ (4 * y + 11) * exp (y / 2))
    (y : ℝ) :
    H y * (kernel m (16 * m) γ y + envelope m (16 * m) γ y) ≤
      peakMajorant m γ y + rightMajorant m γ y + leftMajorant m γ y := by
  have hm0 : 0 < m := by linarith
  have hd (p q : ℝ) : 0 ≤ density p q y := by unfold density; positivity
  have hP : 0 ≤ peakMajorant m γ y := by unfold peakMajorant density; positivity
  have hR : 0 ≤ rightMajorant m γ y := by unfold rightMajorant density; positivity
  have hL : 0 ≤ leftMajorant m γ y := by unfold leftMajorant density; positivity
  have hv := hkernel y
  have hk0 : 0 ≤ kernel m (16 * m) γ y + envelope m (16 * m) γ y := by
    linarith [(abs_le.mp hv.2).1]
  have hk2 : kernel m (16 * m) γ y + envelope m (16 * m) γ y ≤
      2 * envelope m (16 * m) γ y := by linarith [(abs_le.mp hv.2).2]
  have habs : H y * (kernel m (16 * m) γ y + envelope m (16 * m) γ y) ≤
      4 * exp (max y 0) * envelope m (16 * m) γ y := by
    calc
      _ ≤ |H y| * (kernel m (16 * m) γ y + envelope m (16 * m) γ y) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hk0
      _ ≤ (2 * exp (max y 0)) * (2 * envelope m (16 * m) γ y) :=
        mul_le_mul (hgrowth y) hk2 hk0 (by positivity)
      _ = _ := by ring
  by_cases hyJ : y ∈ Icc (4 * m) (28 * m)
  · have hy0 : 0 ≤ y := by linarith [hyJ.1]
    have hb0 : 0 ≤ (4 * y + 11) * exp (y / 2) := by positivity
    have hb : 4 * y + 11 ≤ 81 * m + 2 * (y - 17 * m) ^ 2 := by
      nlinarith [sq_nonneg (y - 17 * m - 1)]
    have hu : coordinate m (16 * m) y ^ 2 ≤
        1 / 2 + (y - 17 * m) ^ 2 / (2 * m ^ 2) := by
      have he : coordinate m (16 * m) y = (y - 17 * m) / (2 * m) + 1 / 2 := by
        unfold coordinate
        field_simp
        <;> ring
      have he2 : (y - 17 * m) ^ 2 / (2 * m ^ 2) =
          2 * ((y - 17 * m) / (2 * m)) ^ 2 := by field_simp <;> ring
      rw [he, he2]
      nlinarith [sq_nonneg ((y - 17 * m) / (2 * m) - 1 / 2)]
    have ht : exp (y / 2) * density m (16 * m) y =
        exp (33 * m / 4) * density m (17 * m) y := by
      convert tilted_density m (16 * m) (1 / 2) y hm0 using 1 <;> congr 1 <;> ring
    have hp : H y * (kernel m (16 * m) γ y + envelope m (16 * m) γ y) ≤
        peakMajorant m γ y := by
      calc
        _ ≤ ((4 * y + 11) * exp (y / 2)) * (2 * envelope m (16 * m) γ y) :=
          mul_le_mul (hnopeak y hyJ) hk2 hk0 hb0
        _ = 4 * ((4 * y + 11) * (coordinate m (16 * m) y ^ 2 + γ ^ 2 + 1)) *
            (exp (y / 2) * density m (16 * m) y) := by unfold envelope; ring
        _ ≤ 4 * ((81 * m + 2 * (y - 17 * m) ^ 2) *
            (γ ^ 2 + 3 / 2 + (y - 17 * m) ^ 2 / (2 * m ^ 2))) *
            (exp (y / 2) * density m (16 * m) y) := by
          have hp := mul_le_mul hb
            (show coordinate m (16 * m) y ^ 2 + γ ^ 2 + 1 ≤
              γ ^ 2 + 3 / 2 + (y - 17 * m) ^ 2 / (2 * m ^ 2) by linarith)
            (by positivity : 0 ≤ coordinate m (16 * m) y ^ 2 + γ ^ 2 + 1)
            (by positivity : 0 ≤ 81 * m + 2 * (y - 17 * m) ^ 2)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num))
            (mul_nonneg (exp_pos _).le (hd _ _))
        _ = peakMajorant m γ y := by rw [ht]; unfold peakMajorant; ring
    linarith
  · by_cases hy0 : 0 ≤ y
    · have htail : 100 * m ^ 2 ≤ (y - 18 * m) ^ 2 := by
        simp only [mem_Icc, not_and_or, not_le] at hyJ
        rcases hyJ with hy | hy
        · nlinarith [sq_nonneg (y - 4 * m)]
        · nlinarith [sq_nonneg (y - 28 * m)]
      have ht : exp y * density m (16 * m) y =
          exp (17 * m) * density m (18 * m) y := by
        convert tilted_density m (16 * m) 1 y hm0 using 1 <;> congr 1 <;> ring
      have hdTail := tail_density m (18 * m) y (25 * m / 2) hm0 (by nlinarith [htail])
      have hu : coordinate m (16 * m) y ^ 2 + γ ^ 2 + 1 ≤
          (γ + 10) ^ 2 + (y - 18 * m) ^ 2 / (2 * m ^ 2) := by
        have he : coordinate m (16 * m) y = (y - 18 * m) / (2 * m) + 1 := by
          unfold coordinate
          field_simp
          <;> ring
        have he2 : (y - 18 * m) ^ 2 / (2 * m ^ 2) =
            2 * ((y - 18 * m) / (2 * m)) ^ 2 := by field_simp <;> ring
        rw [he, he2]
        nlinarith [sq_nonneg ((y - 18 * m) / (2 * m) - 1)]
      have hp : H y * (kernel m (16 * m) γ y + envelope m (16 * m) γ y) ≤
          rightMajorant m γ y := by
        calc
          _ ≤ 4 * exp y * envelope m (16 * m) γ y := by
            simpa only [max_eq_left hy0] using habs
          _ = 8 * (coordinate m (16 * m) y ^ 2 + γ ^ 2 + 1) *
              (exp y * density m (16 * m) y) := by unfold envelope; ring
          _ ≤ 8 * ((γ + 10) ^ 2 + (y - 18 * m) ^ 2 / (2 * m ^ 2)) *
              (exp y * density m (16 * m) y) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hu (by norm_num))
              (mul_nonneg (exp_pos _).le (hd _ _))
          _ = 8 * ((γ + 10) ^ 2 + (y - 18 * m) ^ 2 / (2 * m ^ 2)) *
              exp (17 * m) * density m (18 * m) y := by rw [ht]; ring
          _ ≤ 8 * ((γ + 10) ^ 2 + (y - 18 * m) ^ 2 / (2 * m ^ 2)) *
              exp (17 * m) * (2 * exp (-(25 * m / 2)) * density (2 * m) (18 * m) y) := by
            gcongr
          _ = rightMajorant m γ y := by
            unfold rightMajorant
            rw [show 9 * m / 2 = 17 * m + -(25 * m / 2) by ring, exp_add]
            ring
      linarith
    · have hyneg : y < 0 := lt_of_not_ge hy0
      have htail : 256 * m ^ 2 ≤ (y - 16 * m) ^ 2 := by
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hyneg.le hm0.le, sq_nonneg y]
      have hdTail := tail_density m (16 * m) y (32 * m) hm0 (by nlinarith [htail])
      have hp : H y * (kernel m (16 * m) γ y + envelope m (16 * m) γ y) ≤
          leftMajorant m γ y := by
        calc
          _ ≤ 4 * envelope m (16 * m) γ y := by
            simpa only [max_eq_right hyneg.le, exp_zero, mul_one] using habs
          _ = 8 * (γ ^ 2 + 1 + (y - 16 * m) ^ 2 / (4 * m ^ 2)) *
              density m (16 * m) y := by unfold envelope coordinate; ring
          _ ≤ 8 * (γ ^ 2 + 1 + (y - 16 * m) ^ 2 / (4 * m ^ 2)) *
              (2 * exp (-(32 * m)) * density (2 * m) (16 * m) y) := by gcongr
          _ = leftMajorant m γ y := by unfold leftMajorant; ring
      linarith

/-- Absence of a positive peak bounds the full signed Gaussian response. -/
theorem gaussian_peak_localization (H : ℝ → ℝ) {m γ : ℝ} (hm : 1 ≤ m) (hγ : 10 < γ)
    (hiK : Integrable (fun y : ℝ => H y * kernel m (16 * m) γ y))
    (hiV : Integrable (fun y : ℝ => H y * envelope m (16 * m) γ y))
    (hgrowth : ∀ y, |H y| ≤ 2 * exp (max y 0))
    (hsmall : |∫ y : ℝ, H y * envelope m (16 * m) γ y| ≤
      1000 * (γ + 10) ^ 2 * exp (-83 * m))
    (hkernel : ∀ y, 0 ≤ envelope m (16 * m) γ y ∧
      |kernel m (16 * m) γ y| ≤ envelope m (16 * m) γ y)
    (hnopeak : ∀ y ∈ Icc (4 * m) (28 * m), H y ≤ (4 * y + 11) * exp (y / 2)) :
    (∫ y : ℝ, H y * kernel m (16 * m) γ y) ≤
      2000 * m * (γ + 10) ^ 2 * exp (33 * m / 4) := by
  obtain ⟨hiP, hiR, hiL, hP, hR, hL⟩ := majorant_integrals hm hγ
  have hsum := integral_mono (hiK.add hiV) ((hiP.add hiR).add hiL)
    (fun y => by
      simpa only [Pi.add_apply, ← mul_add] using response_majorant H hm hγ hgrowth hkernel hnopeak y)
  simp only [Pi.add_apply] at hsum
  rw [integral_add hiK hiV,
    integral_add (f := fun y => peakMajorant m γ y + rightMajorant m γ y)
      (hiP.add hiR) hiL, integral_add hiP hiR] at hsum
  have heR : exp (9 * m / 2) ≤ exp (33 * m / 4) := exp_le_exp.mpr (by linarith)
  have heL : exp (-32 * m) ≤ exp (33 * m / 4) := exp_le_exp.mpr (by linarith)
  have heV : exp (-83 * m) ≤ exp (33 * m / 4) := exp_le_exp.mpr (by linarith)
  have hR' := hR.trans (mul_le_mul_of_nonneg_left heR
    (by positivity : 0 ≤ 24 * (γ + 10) ^ 2))
  have hL' := hL.trans (mul_le_mul_of_nonneg_left heL
    (by positivity : 0 ≤ 16 * (γ + 10) ^ 2))
  have hV := (neg_le_neg hsmall).trans
    (neg_abs_le (∫ y : ℝ, H y * envelope m (16 * m) γ y))
  have hV' := mul_le_mul_of_nonneg_left heV (by positivity : 0 ≤ 1000 * (γ + 10) ^ 2)
  have hnonneg : 0 ≤ (γ + 10) ^ 2 * exp (33 * m / 4) := by positivity
  nlinarith [mul_nonneg (show 0 ≤ m - 1 by linarith) hnonneg]

end

end D5.S3.Arith.Robin.GaussianPeakLocalization
