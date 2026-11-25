/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpParity
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The reflection-odd weighted residual satisfies coercive Hermitian estimates in both Fourier involution sectors. -/

import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.SharpConstants

/-! Reflection-odd coordinates, the two involution sectors, and their exact coercivity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

abbrev OddCoordinates := ℂ × ℂ

def oddMass (x : OddCoordinates) : ℝ := ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2

def oddFourier (x : OddCoordinates) : OddCoordinates :=
  ((sharpSigma : ℂ) * x.1 + (sharpH : ℂ) * x.2,
    (sharpH : ℂ) * x.1 - (sharpSigma : ℂ) * x.2)

theorem oddFourier_involutive (x : OddCoordinates) : oddFourier (oddFourier x) = x := by
  have h : (sharpH : ℂ) ^ 2 + (sharpSigma : ℂ) ^ 2 = 1 := by exact_mod_cast sharp_h_sigma_sq
  apply Prod.ext <;> dsimp [oddFourier]
  · linear_combination x.1 * h
  · linear_combination x.2 * h

private def crossRe (x : OddCoordinates) : ℝ := x.1.re * x.2.re + x.1.im * x.2.im

private def quad (a b d : ℝ) (x : OddCoordinates) : ℝ :=
  a * ‖x.1‖ ^ 2 + 2 * b * crossRe x + d * ‖x.2‖ ^ 2

def oddRayleigh (x : OddCoordinates) : ℝ :=
  quad (sharpC - sharpH ^ 2) (sharpH * sharpSigma) (sharpC + sharpH ^ 2) x

/-- Conjugation by the odd Fourier matrix reverses the centering operator. -/
theorem oddRayleigh_fourier (x : OddCoordinates) :
    oddRayleigh (oddFourier x) =
      quad (sharpC + sharpH ^ 2) (-sharpH * sharpSigma) (sharpC - sharpH ^ 2) x := by
  simp only [oddRayleigh, quad, oddFourier, crossRe, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  linear_combination
    ((sharpC + sharpH ^ 2) * (x.1.re ^ 2 + x.1.im ^ 2) +
      (sharpC - sharpH ^ 2) * (x.2.re ^ 2 + x.2.im ^ 2) -
      2 * sharpH * sharpSigma * (x.1.re * x.2.re + x.1.im * x.2.im)) * sharp_h_sigma_sq

def oddDeficit (x y : OddCoordinates) : ℝ := oddRayleigh x + oddRayleigh (oddFourier y)

def oddWeighted (x y : OddCoordinates) : ℝ :=
  lightWeight * (‖(sharpAlpha : ℂ) * x.1 - (sharpBeta : ℂ) * y.1‖ ^ 2 +
    ‖(sharpBeta : ℂ) * (oddFourier x).1 - (sharpAlpha : ℂ) * (oddFourier y).1‖ ^ 2) +
  heavyWeight * (‖(sharpBeta : ℂ) * x.2 + (sharpAlpha : ℂ) * y.2‖ ^ 2 +
    ‖(sharpAlpha : ℂ) * (oddFourier x).2 + (sharpBeta : ℂ) * (oddFourier y).2‖ ^ 2)

def oddSector (s : ℝ) (x y : OddCoordinates) : OddCoordinates :=
  ((x.1 + (s : ℂ) * (oddFourier y).1) / 2,
    (x.2 + (s : ℂ) * (oddFourier y).2) / 2)

private def v₁ (s : ℝ) : ℝ := sharpAlpha - s * sharpBeta * sharpSigma
private def v₂ (s : ℝ) : ℝ := -s * sharpBeta * sharpH
private def w₁ (s : ℝ) : ℝ := s * sharpAlpha * sharpH
private def w₂ (s : ℝ) : ℝ := sharpBeta - s * sharpAlpha * sharpSigma

private def a₁₁ (s : ℝ) : ℝ :=
  4 * sharpC * (sharpC - sharpH ^ 2) - lightWeight * v₁ s ^ 2 - heavyWeight * w₁ s ^ 2
private def a₂₂ (s : ℝ) : ℝ :=
  4 * sharpC * (sharpC + sharpH ^ 2) - lightWeight * v₂ s ^ 2 - heavyWeight * w₂ s ^ 2
private def a₁₂ (s : ℝ) : ℝ :=
  4 * sharpC * sharpH * sharpSigma - lightWeight * v₁ s * v₂ s - heavyWeight * w₁ s * w₂ s

private def sectorResidual (s : ℝ) (x : OddCoordinates) : ℝ :=
  quad (a₁₁ s) (a₁₂ s) (a₂₂ s) x

private theorem nonnegative_product_bounds {l₁ u₁ l₂ u₂ x y : ℝ}
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (hx : l₁ ≤ x ∧ x ≤ u₁) (hy : l₂ ≤ y ∧ y ≤ u₂) :
    l₁ * l₂ ≤ x * y ∧ x * y ≤ u₁ * u₂ :=
  ⟨mul_le_mul hx.1 hy.1 hl₂ (hl₁.trans hx.1),
    mul_le_mul hx.2 hy.2 (hl₂.trans hy.1) (hl₁.trans (hx.1.trans hx.2))⟩

private theorem squared_bounds {l u x : ℝ} (hl : 0 ≤ l) (hx : l ≤ x ∧ x ≤ u) :
    l ^ 2 ≤ x ^ 2 ∧ x ^ 2 ≤ u ^ 2 := by
  simpa only [pow_two] using nonnegative_product_bounds hl hl hx hx

private theorem coefficient_intervals :
    (1.361 < a₁₁ 1 ∧ 2.744 < a₂₂ 1 ∧ 0 < a₁₂ 1 ∧ a₁₂ 1 < 0.675) ∧
    (0.1613 < a₁₁ (-1) ∧ 1.9277 < a₂₂ (-1) ∧ 0 < a₁₂ (-1) ∧ a₁₂ (-1) < 0.5558) := by
  have hc : 0.96104463 ≤ sharpC ∧ sharpC ≤ 0.96104465 :=
    ⟨sharp_c_bounds.1.le, sharp_c_bounds.2.le⟩
  have hh : 0.52573110 ≤ sharpH ∧ sharpH ≤ 0.52573113 :=
    ⟨sharp_h_bounds.1.le, sharp_h_bounds.2.le⟩
  have hσ : 0.85065080 ≤ sharpSigma ∧ sharpSigma ≤ 0.85065082 :=
    ⟨sharp_sigma_bounds.1.le, sharp_sigma_bounds.2.le⟩
  have hα : 0.1973710 ≤ sharpAlpha ∧ sharpAlpha ≤ 0.1973713 :=
    ⟨sharp_alpha_bounds.1.le, sharp_alpha_bounds.2.le⟩
  have hβ : 1.4003730 ≤ sharpBeta ∧ sharpBeta ≤ 1.4003731 :=
    ⟨sharp_beta_bounds.1.le, sharp_beta_bounds.2.le⟩
  have hh₂ := squared_bounds (by norm_num) hh
  have hminus : 0.6846514 ≤ sharpC - sharpH ^ 2 ∧ sharpC - sharpH ^ 2 ≤ 0.6846515 :=
    ⟨by linarith [hc.1, hh₂.2], by linarith [hc.2, hh₂.1]⟩
  have hplus : 1.2374378 ≤ sharpC + sharpH ^ 2 ∧ sharpC + sharpH ^ 2 ≤ 1.2374379 :=
    ⟨by linarith [hc.1, hh₂.1], by linarith [hc.2, hh₂.2]⟩
  have hhs := nonnegative_product_bounds (by norm_num) (by norm_num) hh hσ
  have hhs' : 0.4472135 ≤ sharpH * sharpSigma ∧ sharpH * sharpSigma ≤ 0.4472137 :=
    ⟨by linarith [hhs.1], by linarith [hhs.2]⟩
  have hdiag₁ := nonnegative_product_bounds (by norm_num) (by norm_num) hc hminus
  have hdiag₂ := nonnegative_product_bounds (by norm_num) (by norm_num) hc hplus
  have hoff := nonnegative_product_bounds (by norm_num) (by norm_num) hc hhs'
  have hbσ := nonnegative_product_bounds (by norm_num) (by norm_num) hβ hσ
  have hbH := nonnegative_product_bounds (by norm_num) (by norm_num) hβ hh
  have haH := nonnegative_product_bounds (by norm_num) (by norm_num) hα hh
  have haσ := nonnegative_product_bounds (by norm_num) (by norm_num) hα hσ
  have hpv : 0.9938570 ≤ sharpBeta * sharpSigma - sharpAlpha ∧
      sharpBeta * sharpSigma - sharpAlpha ≤ 0.9938576 :=
    ⟨by linarith [hbσ.1, hα.2], by linarith [hbσ.2, hα.1]⟩
  have hmv : 1.3885994 ≤ sharpAlpha + sharpBeta * sharpSigma ∧
      sharpAlpha + sharpBeta * sharpSigma ≤ 1.3885999 :=
    ⟨by linarith [hbσ.1, hα.1], by linarith [hbσ.2, hα.2]⟩
  have hpw : 1.2324789 ≤ sharpBeta - sharpAlpha * sharpSigma ∧
      sharpBeta - sharpAlpha * sharpSigma ≤ 1.2324794 :=
    ⟨by linarith [haσ.2, hβ.1], by linarith [haσ.1, hβ.2]⟩
  have hmw : 1.5682667 ≤ sharpBeta + sharpAlpha * sharpSigma ∧
      sharpBeta + sharpAlpha * sharpSigma ≤ 1.5682672 :=
    ⟨by linarith [haσ.1, hβ.1], by linarith [haσ.2, hβ.2]⟩
  have hv₂s := squared_bounds (by norm_num) hbH
  have hw₁s := squared_bounds (by norm_num) haH
  have hpvs := squared_bounds (by norm_num) hpv
  have hpws := squared_bounds (by norm_num) hpw
  have hmvs := squared_bounds (by norm_num) hmv
  have hmws := squared_bounds (by norm_num) hmw
  have hpvv := nonnegative_product_bounds (by norm_num) (by norm_num) hpv hbH
  have hpww := nonnegative_product_bounds (by norm_num) (by norm_num) haH hpw
  have hmvv := nonnegative_product_bounds (by norm_num) (by norm_num) hmv hbH
  have hmww := nonnegative_product_bounds (by norm_num) (by norm_num) haH hmw
  norm_num only [a₁₁, a₂₂, a₁₂, v₁, v₂, w₁, w₂, lightWeight, heavyWeight, one_mul, neg_mul,
    neg_neg, sub_neg_eq_add]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · nlinarith only [hdiag₁.1, hpvs.2, hw₁s.2]
  · nlinarith only [hdiag₂.1, hv₂s.2, hpws.2]
  · nlinarith only [hoff.1, hpvv.2, hpww.2]
  · nlinarith only [hoff.2, hpvv.1, hpww.1]
  · nlinarith only [hdiag₁.1, hmvs.2, hw₁s.2]
  · nlinarith only [hdiag₂.1, hv₂s.2, hmws.2]
  · nlinarith only [hoff.1, hmvv.2, hmww.1]
  · nlinarith only [hoff.2, hmvv.1, hmww.2]

private theorem real_quad_nonneg {a b d : ℝ} (ha : 0 < a) (hdet : b ^ 2 ≤ a * d)
    (u v : ℝ) : 0 ≤ a * u ^ 2 + 2 * b * u * v + d * v ^ 2 := by
  apply nonneg_of_mul_nonneg_left _ ha
  calc
    0 ≤ (a * u + b * v) ^ 2 + (a * d - b ^ 2) * v ^ 2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hdet) (sq_nonneg _))
    _ = (a * u ^ 2 + 2 * b * u * v + d * v ^ 2) * a := by ring

private theorem quad_ge_mass {a b d l : ℝ} (ha : 0 < a - l)
    (hdet : b ^ 2 ≤ (a - l) * (d - l)) (x : OddCoordinates) :
    l * oddMass x ≤ quad a b d x := by
  have hr := real_quad_nonneg ha hdet x.1.re x.2.re
  have hi := real_quad_nonneg ha hdet x.1.im x.2.im
  simp only [quad, oddMass, crossRe, Complex.sq_norm, Complex.normSq_apply]
  nlinarith only [hr, hi]

private theorem sector_plus_coercive (x : OddCoordinates) : oddMass x ≤ sectorResidual 1 x := by
  obtain ⟨ha, hd, hb, hb'⟩ := coefficient_intervals.1
  have hab : 0 < a₁₁ 1 - 1 := by linarith
  have hp : (0.361 : ℝ) * 1.744 ≤ (a₁₁ 1 - 1) * (a₂₂ 1 - 1) :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) hab.le
  have hsq := (sq_le_sq₀ hb.le (by norm_num : 0 ≤ (0.675 : ℝ))).mpr hb'.le
  simpa only [one_mul, sectorResidual] using
    quad_ge_mass hab (by linarith only [hp, hsq]) x

private theorem sector_minus_coercive (x : OddCoordinates) :
    0.0001 * oddMass x ≤ sectorResidual (-1) x := by
  obtain ⟨ha, hd, hb, hb'⟩ := coefficient_intervals.2
  have hab : 0 < a₁₁ (-1) - 0.0001 := by linarith
  have hp : (0.1612 : ℝ) * 1.9276 ≤ (a₁₁ (-1) - 0.0001) * (a₂₂ (-1) - 0.0001) :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) hab.le
  have hsq := (sq_le_sq₀ hb.le (by norm_num : 0 ≤ (0.5558 : ℝ))).mpr hb'.le
  exact quad_ge_mass hab (by linarith only [hp, hsq]) x

private theorem sector_map (s : ℝ) (x y : OddCoordinates) :
    oddFourier (oddSector s x y) =
      (((oddFourier x).1 + (s : ℂ) * y.1) / 2, ((oddFourier x).2 + (s : ℂ) * y.2) / 2) := by
  have h := oddFourier_involutive y
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  apply Prod.ext
  · dsimp [oddFourier, oddSector] at h₁ ⊢
    linear_combination (s : ℂ) / 2 * h₁
  · dsimp [oddFourier, oddSector] at h₂ ⊢
    linear_combination (s : ℂ) / 2 * h₂

private theorem quad_split (a b d : ℝ) (x y : OddCoordinates) :
    quad a b d x + quad a b d (oddFourier y) =
      2 * quad a b d (oddSector 1 x y) + 2 * quad a b d (oddSector (-1) x y) := by
  -- Pair the sum and difference in each complex coordinate.
  simp only [quad, oddSector, crossRe, Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.ofReal_one, Complex.ofReal_neg, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im]
  ring

private theorem sectorResidual_eq (s : ℝ) (x : OddCoordinates) :
    sectorResidual s x = 4 * sharpC * oddRayleigh x -
      lightWeight * ‖(sharpAlpha : ℂ) * x.1 - (s : ℂ) * (sharpBeta : ℂ) * (oddFourier x).1‖ ^ 2 -
      heavyWeight * ‖(sharpBeta : ℂ) * x.2 + (s : ℂ) * (sharpAlpha : ℂ) * (oddFourier x).2‖ ^ 2 := by
  simp only [sectorResidual, quad, a₁₁, a₁₂, a₂₂, v₁, v₂, w₁, w₂, oddRayleigh, oddFourier,
    crossRe, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

private theorem odd_energy_split (x y : OddCoordinates) :
    4 * sharpC * oddDeficit x y - oddWeighted x y =
      2 * sectorResidual 1 (oddSector 1 x y) + 2 * sectorResidual (-1) (oddSector (-1) x y) := by
  have hd :
      oddDeficit x y = 2 * oddRayleigh (oddSector 1 x y) +
        2 * oddRayleigh (oddSector (-1) x y) := quad_split _ _ _ x y
  rw [hd, sectorResidual_eq, sectorResidual_eq, sector_map, sector_map]
  simp only [oddWeighted, oddSector, Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_one, Complex.ofReal_neg,
    Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im]
  ring

/-- Quantitative complex Hermitian bound in both odd sectors. -/
theorem odd_weighted_coercivity (x y : OddCoordinates) :
    oddWeighted x y + 2 * oddMass (oddSector 1 x y) + 0.0002 * oddMass (oddSector (-1) x y)
      ≤ 4 * sharpC * oddDeficit x y := by
  linarith only [odd_energy_split x y, sector_plus_coercive (oddSector 1 x y),
    sector_minus_coercive (oddSector (-1) x y)]

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
