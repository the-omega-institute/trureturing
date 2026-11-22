/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteExceptionalMarginal
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteExceptionalMarginal
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteTraceChart, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMarginal]
   utility: none
   digest: The nilpotent two-site observation excludes every exceptional normal direction. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMarginal
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteTraceChart

/-! Exceptional amplitude directions over the base conics cannot match the special fiber. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteExceptionalMarginal

open PeriodicMPSSixSiteCoordinates PeriodicMPSSixSiteMarginal PeriodicMPSSixSiteTraceChart

private def twoLetterSlice (a b c d e : ℂ) : Fin 14 → ℂ :=
  ![a, b, c, d, 0, e, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem lift_on_base (d : ℂ) (z : Fin 3 → ℂ) :
    lift d 0 0 z = twoLetterSlice (z 0) ((d ^ 2 - 3 * d + 1) * z 1)
      (-(2 * d ^ 2 - 4 * d + 1) * z 2) ((2 * d ^ 2 - d) * z 2)
      (-2 * d ^ 2 * z 2) := by
  funext i
  fin_cases i <;> simp [lift, twoLetterSlice]

private theorem firstChart_corner_forces_aligned {s a b c d e : ℂ}
    (h : gram (shear s (twoLetterSlice a b c d e)) 3 3 = 0)
    (hp : twoLetterSlice a b c d e ≠ 0) : s = 0 := by
  by_contra hs
  let q := shear s (twoLetterSlice a b c d e)
  have hz := supported_of_corner_zero q h
  have h₂ : q 2 = 0 := congrFun hz 2
  have h₄ : q 4 = 0 := congrFun hz 4
  have h₆ : q 6 = 0 := congrFun hz 6
  have h₈ : q 8 = 0 := congrFun hz 8
  have h₁₀ : q 10 = 0 := congrFun hz 10
  let A := s ^ 2 * a
  let B := s * b
  change c + s * (2 * b) + s ^ 2 * a = 0 at h₂
  change 0 + s * (2 * c + d) + s ^ 2 * (3 * b) + s ^ 3 * a = 0 at h₄
  change 0 + s * (c + d + e) + s ^ 2 * (3 * b) + s ^ 3 * a = 0 at h₆
  change 0 + s * (2 * 0 + 0 + 0) + s ^ 2 * (3 * c + 2 * d + e) +
      s ^ 3 * (4 * b) + s ^ 4 * a = 0 at h₈
  change 0 + s * (0 + 0 + 0 + 0) + s ^ 2 * (2 * c + 3 * d + e) +
      s ^ 3 * (4 * b) + s ^ 4 * a = 0 at h₁₀
  have e₂ : A + 2 * B + c = 0 := by
    dsimp [A, B]
    linear_combination h₂
  have e₄ : A + 3 * B + 2 * c + d = 0 := by
    have hm : s * (A + 3 * B + 2 * c + d) = 0 := by
      dsimp [A, B]
      linear_combination h₄
    exact (mul_eq_zero.mp hm).resolve_left hs
  have e₆ : A + 3 * B + c + d + e = 0 := by
    have hm : s * (A + 3 * B + c + d + e) = 0 := by
      dsimp [A, B]
      linear_combination h₆
    exact (mul_eq_zero.mp hm).resolve_left hs
  have e₈ : A + 4 * B + 3 * c + 2 * d + e = 0 := by
    have hm : s ^ 2 * (A + 4 * B + 3 * c + 2 * d + e) = 0 := by
      dsimp [A, B]
      linear_combination h₈
    exact (mul_eq_zero.mp hm).resolve_left (pow_ne_zero _ hs)
  have e₁₀ : A + 4 * B + 2 * c + 3 * d + e = 0 := by
    have hm : s ^ 2 * (A + 4 * B + 2 * c + 3 * d + e) = 0 := by
      dsimp [A, B]
      linear_combination h₁₀
    exact (mul_eq_zero.mp hm).resolve_left (pow_ne_zero _ hs)
  have ha : A = 0 := by linear_combination 6 * e₂ - 5 * e₄ - 3 * e₆ + e₈ + 2 * e₁₀
  have hb : B = 0 := by linear_combination -3 * e₂ + 3 * e₄ + 2 * e₆ - e₈ - e₁₀
  have hc : c = 0 := by linear_combination e₂ - e₄ - e₆ + e₈
  have hd : d = 0 := by linear_combination e₂ - e₄ - e₆ + e₁₀
  have he : e = 0 := by linear_combination e₂ - 2 * e₄ + e₈
  apply hp
  have ha' : a = 0 := (mul_eq_zero.mp ha).resolve_left (pow_ne_zero _ hs)
  have hb' : b = 0 := (mul_eq_zero.mp hb).resolve_left hs
  funext i
  fin_cases i <;> simp [twoLetterSlice, ha', hb', hc, hd, he]

/-- A first-chart exceptional ray with no adjacent ones has zero diagonal-exchange
difference in the singleton block. -/
theorem firstChart_difference_eq_zero {s d : ℂ} (hd : vacuum d = 0)
    {z : Fin 3 → ℂ} (hz : z ≠ 0) (h : gram (shear s (lift d 0 0 z)) 3 3 = 0) :
    gram (shear s (lift d 0 0 z)) 1 1 = gram (shear s (lift d 0 0 z)) 1 2 := by
  have hp := lift_ne_zero_of_vacuum hd hz
  rw [lift_on_base] at h hp
  have hs := firstChart_corner_forces_aligned h hp
  subst s
  rw [shear_zero]
  have hslice := supported_of_corner_zero _ (by simpa only [shear_zero, lift_on_base] using h)
  have hc : -(2 * d ^ 2 - 4 * d + 1) * z 2 = 0 := congrFun hslice 2
  have hz₂ := (mul_eq_zero.mp hc).resolve_left (neg_ne_zero.mpr (controlling_factors_ne hd).2)
  have hp' : lift d 0 0 z = independentSlice (z 0) ((d ^ 2 - 3 * d + 1) * z 1) 0 0 0 := by
    funext i
    fin_cases i <;> simp [lift, independentSlice, hz₂]
  rw [hp', (independent_gram _ _ _ _ _).2.2.1, (independent_gram _ _ _ _ _).2.2.2.1]
  simp

private theorem swapped_head_zero {p : Fin 14 → ℂ}
    (h : gram (p ∘ swappedIndex) 3 3 = 0) : p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0 := by
  have hs := supported_of_corner_zero (p ∘ swappedIndex) h
  exact ⟨congrFun hs 13, congrFun hs 12, congrFun hs 8⟩

/-- The second physical letter has a nonzero trace component in this chart.
Consequently every nonzero exceptional ray has nonzero adjacent-ones weight. -/
theorem secondChart_corner_ne_zero {s d : ℂ} (hd : vacuum d = 0)
    {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    gram (shear s (lift d 0 0 z) ∘ swappedIndex) 3 3 ≠ 0 := by
  intro h
  obtain ⟨h₀, h₁, h₂⟩ := swapped_head_zero h
  have hz₀ : z 0 = 0 := h₀
  change (d ^ 2 - 3 * d + 1) * z 1 + s * z 0 = 0 at h₁
  rw [hz₀, mul_zero, add_zero] at h₁
  have hz₁ := (mul_eq_zero.mp h₁).resolve_left (controlling_factors_ne hd).1
  change -(2 * d ^ 2 - 4 * d + 1) * z 2 +
      s * (2 * ((d ^ 2 - 3 * d + 1) * z 1)) + s ^ 2 * z 0 = 0 at h₂
  rw [h₁, hz₀, mul_zero, mul_zero, mul_zero, add_zero, add_zero] at h₂
  have hz₂ := (mul_eq_zero.mp h₂).resolve_left (neg_ne_zero.mpr (controlling_factors_ne hd).2)
  apply hz
  funext i
  fin_cases i
  · exact hz₀
  · exact hz₁
  · exact hz₂

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteExceptionalMarginal
