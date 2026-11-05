/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonSmallCases
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonSmallCases
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separate exact dipole and square spectra, with neutrality and actual unbounded neutral drift. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealBoundary

/-! Small spectra are consequences of the actual-field reduction, with BK credit retained. -/
noncomputable section
open Matrix Polynomial

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonSmallCases
open AlternatingPolygonSpectrum AlternatingPolygonModes AlternatingPolygonJordan
open AlternatingPolygonComplexSpectrum AlternatingPolygonCartesianChain
open AlternatingPolygonRealBoundary AlternatingPolygonNeutral

private theorem square_root_constant : (2 : ℂ) / (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  apply (div_eq_iff hn).mpr
  simpa only [pow_two] using hs.symm

/-- The actual dipole polynomial and its exhaustive complex spectrum. -/
theorem dipole (μ : ℂ) :
    (jacobian 2).charpoly = X ^ 2 * (X ^ 2 + C (1 / 2 : ℝ)) ∧
      ((actualOperator 1).HasEigenvalue μ ↔
        μ = 0 ∨ μ = Complex.I / (Real.sqrt 2 : ℂ) ∨
          μ = -(Complex.I / (Real.sqrt 2 : ℂ))) := by
  constructor
  · exact dipole_charpoly
  · rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, actualOperator,
      Matrix.charpoly_toLin', all_complex_roots 1 (by omega)]
    constructor
    · rintro ⟨r, hr, h⟩
      interval_cases r
      · simp [spectralRoot, div_eq_mul_inv] at h
        exact Or.inr h
      · simp [spectralRoot] at h
        exact Or.inl h
    · rintro (h | h | h)
      · exact ⟨1, le_rfl, Or.inl (by simpa [spectralRoot] using h)⟩
      · exact ⟨0, by omega, Or.inl (by simpa [spectralRoot, div_eq_mul_inv] using h)⟩
      · exact ⟨0, by omega, Or.inr (by simpa [spectralRoot, div_eq_mul_inv] using h)⟩

/-- The square constants are settled by the actual Cartesian field, with no presumed
explanation for the different numbers printed in BK arXiv v2 Eq. (12). -/
theorem square (μ : ℂ) :
    (jacobian 4).charpoly = X ^ 2 * (X ^ 2 + C (2 : ℝ)) *
        (X ^ 2 + C (1 / 4 : ℝ)) ^ 2 ∧
      ((actualOperator 2).HasEigenvalue μ ↔
        μ = 0 ∨ μ = Complex.I * (Real.sqrt 2 : ℂ) ∨
          μ = -(Complex.I * (Real.sqrt 2 : ℂ)) ∨
            μ = Complex.I / 2 ∨ μ = -(Complex.I / 2)) := by
  constructor
  · exact square_charpoly
  · rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, actualOperator,
      Matrix.charpoly_toLin', all_complex_roots 2 (by omega)]
    have h0 : spectralRoot 2 0 = Complex.I * (Real.sqrt 2 : ℂ) := by
      simp only [spectralRoot]
      norm_num only [show (0 : ℕ) ≠ 2 by omega, show (0 : ℕ) = 0 by rfl,
        if_false, if_true, Nat.cast_ofNat]
      rw [square_root_constant]
    have h1 : spectralRoot 2 1 = Complex.I / 2 := by norm_num [spectralRoot, div_eq_mul_inv]
    have h2 : spectralRoot 2 2 = 0 := by simp [spectralRoot]
    constructor
    · rintro ⟨r, hr, h⟩
      interval_cases r
      · rw [h0] at h; tauto
      · rw [h1] at h; tauto
      · rw [h2, neg_zero, or_self] at h; exact Or.inl h
    · rintro (h | h | h | h | h)
      · exact ⟨2, le_rfl, Or.inl (by rwa [h2])⟩
      · exact ⟨0, by omega, Or.inl (by rwa [h0])⟩
      · exact ⟨0, by omega, Or.inr (by rwa [h0])⟩
      · exact ⟨1, by omega, Or.inl (by rwa [h1])⟩
      · exact ⟨1, by omega, Or.inr (by rwa [h1])⟩

/-- Spectral neutrality coexists with a nonzero actual real unbounded drift orbit. -/
theorem small_neutral_drift (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) (hm2 : m ≤ 2) :
    (∀ μ : ℂ, (actualOperator m).HasEigenvalue μ → μ.re = 0) ∧
      Module.finrank ℂ ((actualOperator m).maxGenEigenspace 0) = 2 ∧
      Module.finrank ℂ ((actualOperator m).eigenspace 0) = 1 ∧
      ¬ Bornology.IsBounded (Set.range (fun t : ℝ => cartesian1 m + t • cartesian0 m)) := by
  exact ⟨fun _ h => small_spectral_neutrality m hm hm2 h,
    neutral_generalized_finrank m hm, neutral_geometric_finrank m hm,
    (unbounded_linear_drift m hm).2⟩

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonSmallCases
