import D5.S3.Geometry.AdS3.AdS3MarkedFillingCharacter

/-! The longest geometric cores among the marked modular fillings. -/

set_option autoImplicit false

open scoped MatrixGroups UpperHalfPlane

namespace D5.S3.Geometry.AdS3MarkedFillingCharacter

open AdS3LoxodromicQuotient.Loxodromic
open AdS3RademacherFilling

private theorem modularFactor_sq_chamber (τ : ℍ) (hτ : τ ∈ ModularGroup.fd)
    (p : FillingIndex) :
    1 ≤ ‖modularFactor p.completion τ‖ ^ 2 ∧
    (‖modularFactor p.completion τ‖ ^ 2 = 1 ↔
      p = polarIndex ∨
      (p.c = 1 ∧ p.d = 0 ∧ ‖(τ : ℂ)‖ = 1) ∨
      (p.c = 1 ∧ p.d = 1 ∧ τ.re = -1 / 2 ∧ ‖(τ : ℂ)‖ = 1) ∨
      (p.c = 1 ∧ p.d = -1 ∧ τ.re = 1 / 2 ∧ ‖(τ : ℂ)‖ = 1)) := by
  by_cases hp : p = polarIndex
  · subst p
    simp [modularFactor, polarIndex]
  have hcpos : 0 < p.c := p.normalized.resolve_right fun h =>
    hp ((eq_polarIndex_iff p).mpr h.1)
  by_cases hc : p.c = 1
  · have hfactor : ‖modularFactor p.completion τ‖ ^ 2 =
        ‖(τ : ℂ)‖ ^ 2 + ((p.d : ℝ) * (2 * τ.re) + (p.d : ℝ) * p.d) := by
      simp only [modularFactor, FillingIndex.completion_c, FillingIndex.completion_d, hc,
        Int.cast_one, one_mul, Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
        Complex.add_im, Complex.intCast_re, Complex.intCast_im, add_zero,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have hre : |2 * τ.re| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith [hτ.2]
    have hshift := Int.nonneg_mul_add_sq_of_abs_le_one p.d hre
    have hnorm : 1 ≤ ‖(τ : ℂ)‖ ^ 2 := by
      simpa only [Complex.sq_norm] using hτ.1
    rw [hfactor]
    refine ⟨by linarith, ?_⟩
    have hshift_zero :
        (p.d : ℝ) * (2 * τ.re) + (p.d : ℝ) * p.d = 0 ↔
          p.d = 0 ∨ (p.d = 1 ∧ τ.re = -1 / 2) ∨ (p.d = -1 ∧ τ.re = 1 / 2) := by
      rw [← mul_add, mul_eq_zero, Int.cast_eq_zero]
      constructor
      · rintro (hd | h)
        · exact Or.inl hd
        have hlo : (-1 : ℝ) ≤ (p.d : ℝ) := by linarith [(abs_le.mp hre).2]
        have hhi : (p.d : ℝ) ≤ 1 := by linarith [(abs_le.mp hre).1]
        have hlo' : (-1 : ℤ) ≤ p.d := by exact_mod_cast hlo
        have hhi' : p.d ≤ 1 := by exact_mod_cast hhi
        rcases (show p.d = 0 ∨ p.d = 1 ∨ p.d = -1 by omega) with hd | hd | hd
        · exact Or.inl hd
        · norm_num [hd] at h
          exact Or.inr (Or.inl ⟨hd, by linarith⟩)
        · norm_num [hd] at h
          exact Or.inr (Or.inr ⟨hd, by linarith⟩)
      · rintro (hd | ⟨hd, hx⟩ | ⟨hd, hx⟩)
        · exact Or.inl hd
        · exact Or.inr (by norm_num [hd, hx])
        · exact Or.inr (by norm_num [hd, hx])
    have hsum :
        ‖(τ : ℂ)‖ ^ 2 + ((p.d : ℝ) * (2 * τ.re) + (p.d : ℝ) * p.d) = 1 ↔
          ‖(τ : ℂ)‖ ^ 2 = 1 ∧ (p.d : ℝ) * (2 * τ.re) + (p.d : ℝ) * p.d = 0 := by
      constructor
      · intro h
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h, h'⟩
        rw [h, h', add_zero]
    rw [hsum, pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, hshift_zero]
    simp only [hc, true_and, hp, false_or]
    tauto
  · have hc₂ : (2 : ℝ) ≤ (p.c : ℝ) := by
      exact_mod_cast (show (2 : ℤ) ≤ p.c by omega)
    have hden : ((p.c : ℝ) * τ.im) ^ 2 ≤ ‖modularFactor p.completion τ‖ ^ 2 := by
      rw [Complex.sq_norm, modularFactor, ← ModularGroup.denom_apply]
      exact τ.c_mul_im_sq_le_normSq_denom (p.completion : GL (Fin 2) ℝ)
    have hlarge : 1 < ‖modularFactor p.completion τ‖ ^ 2 := calc
      1 < (2 * τ.im) ^ 2 := by
        nlinarith [ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ]
      _ ≤ ((p.c : ℝ) * τ.im) ^ 2 := by gcongr
      _ ≤ _ := hden
    exact ⟨hlarge.le, by simp [hlarge.ne', hp, hc]⟩

/-- In the closed modular chamber the polar filling maximizes the geometric
core length. The normalized row of each tying embedded meridian is determined
by markedFillingEquiv. By norm_rawBoltzmann the same classification holds
for the moduli of the raw vacuum weights. -/
theorem coreTranslationLength_maximizers (τ : ℍ) (hτ : τ ∈ ModularGroup.fd)
    (m : MarkedFilling τ) :
    let p := (markedFillingEquiv τ).symm m
    coreTranslationLength p.completion τ ≤ coreTranslationLength polarIndex.completion τ ∧
    (coreTranslationLength p.completion τ = coreTranslationLength polarIndex.completion τ ↔
      p = polarIndex ∨
      (p.c = 1 ∧ p.d = 0 ∧ ‖(τ : ℂ)‖ = 1) ∨
      (p.c = 1 ∧ p.d = 1 ∧ τ.re = -1 / 2 ∧ ‖(τ : ℂ)‖ = 1) ∨
      (p.c = 1 ∧ p.d = -1 ∧ τ.re = 1 / 2 ∧ ‖(τ : ℂ)‖ = 1)) := by
  dsimp only
  generalize (markedFillingEquiv τ).symm m = p
  obtain ⟨hden, hties⟩ := modularFactor_sq_chamber τ hτ p
  have hpos : 0 < 2 * Real.pi * τ.im := by positivity
  have hpolar : coreTranslationLength polarIndex.completion τ = 2 * Real.pi * τ.im := by
    simp [coreTranslationLength_eq, modularFactor, polarIndex]
  rw [hpolar, coreTranslationLength_eq, div_le_iff₀ (zero_lt_one.trans_le hden),
    div_eq_iff (zero_lt_one.trans_le hden).ne']
  exact ⟨le_mul_of_one_le_right hpos.le hden, (by
    rw [eq_comm, mul_eq_left₀ hpos.ne', hties])⟩

end D5.S3.Geometry.AdS3MarkedFillingCharacter
