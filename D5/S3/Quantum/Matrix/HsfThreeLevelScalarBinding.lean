/- GID: D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfThreeLevelScalarBinding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Quantum/Matrix/PsdThreeCubicComplex]
   utility: none
   digest: Bind the actual three-level coefficients to the universal complex PSD cubic criterion. -/

module

public import D5.S3.Quantum.Matrix.HsfThreeLevelScalarIdentity

/-! The exact positive-level coefficients are
   discharged here, including all collisions. There is no hypothesis that
   assumes the desired matrix sign. This is the closed cubic theorem; the
   original integral-to-moment and HSF derivative bridges remain separate.
   No equality classification, original HSF completion or novelty is claimed. -/

@[expose] public section
noncomputable section

open scoped ComplexOrder

namespace D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients

open PsdThreeCubic

/-- The actual polynomial comparison, with its positive denominators cleared. -/
theorem scalar_p396_margin (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    (rho p q+rho q r+rho r p)*(Xi p q r)^2 ≤
      4*(rho p q+rho q r+rho r p)*(rho p q*rho q r+rho q r*rho r p+rho r p*rho p q)+
        396*rho p q*rho q r*rho r p := by
  have hP := p396_nonneg p q r hp hq hr
  rw [p396_scaled p q r hp hq hr] at hP
  have hD : 0 < (commonDen p q r)^3 := by
    have hQ := Q_pos p q r hp hq hr
    unfold commonDen
    positivity
  have h := nonneg_of_mul_nonneg_right hP hD
  linarith only [h]

/-- The full coefficient domination, without a distinct-level restriction. -/
theorem coefficient_domination (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    Xi p q r ≤ allowance (rho p q) (rho q r) (rho r p) := by
  have ha := rho_nonneg p q hp hq
  have hb := rho_nonneg q r hq hr
  have hc := rho_nonneg r p hr hp
  by_cases hall : p = q ∧ q = r
  · rcases hall with ⟨rfl, rfl⟩
    simp [Xi_self, rho_self p hp, allowance, root3]
  · have hs : 0 < rho p q+rho q r+rho r p := by
      by_cases hpq : p = q
      · have hqr : q ≠ r := by intro h; exact hall ⟨hpq, h⟩
        have h := rho_pos q r hq hr hqr
        linarith only [ha, hc, h]
      · have h := rho_pos p q hp hq hpq
        linarith only [hb, hc, h]
    exact allowance_of_p396 (rho p q) (rho q r) (rho r p) (Xi p q r)
      ha hb hc (Xi_nonneg p q r hp hq hr) hs (scalar_p396_margin p q r hp hq hr)

/-- The full complex PSD3 closed cubic sign, for every positive spectrum,
    every source rank and phase, and every level collision. -/
theorem closed_cubic_nonneg (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (S : Mat) (hS : S.PosSemidef) : 0 ≤ closedCubic p q r S := by
  exact cubic_nonneg S hS (rho p q) (rho q r) (rho r p) (Xi p q r)
    (rho_nonneg p q hp hq) (rho_nonneg q r hq hr) (rho_nonneg r p hr hp)
    (Xi_nonneg p q r hp hq hr) (coefficient_domination p q r hp hq hr)

end D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients
