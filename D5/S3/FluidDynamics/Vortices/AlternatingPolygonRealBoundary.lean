/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealBoundary
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonRealBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exhaustive real signs and the separate spectrally neutral dipole and square. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces

/-! Sign classification and the small-polygon boundary. -/
noncomputable section
open Matrix

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealBoundary
open AlternatingPolygonSpectrum AlternatingPolygonModes AlternatingPolygonJordan
open AlternatingPolygonRealSpaces AlternatingPolygonComplexSpectrum

/-- Every positive real eigenvalue is one of the canonical positive roots, with no extra sign branch. -/
theorem positive_eigenvalue_iff (m : ℕ) (hm : 3 ≤ m) {μ : ℝ} (hμ : 0 < μ) :
    (realOperator m).HasEigenvalue μ ↔
      ∃ k : Fin (m - 2), μ = positiveRoot m (k.val + 2) := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, realOperator, Matrix.charpoly_toLin',
    root_iff_mode m hm μ (ne_of_gt hμ)]
  constructor
  · rintro ⟨r, hr, hrm, hs⟩
    refine ⟨⟨r - 2, by omega⟩, ?_⟩
    have he : r - 2 + 2 = r := by omega
    simp only [he]
    apply (sq_eq_sq₀ (le_of_lt hμ) (le_of_lt (positiveRoot_pos m r hr hrm))).mp
    rw [positiveRoot_sq m r hr]
    exact hs
  · rintro ⟨k, rfl⟩
    exact ⟨k.val + 2, by omega, by omega, positiveRoot_sq m _ (by omega)⟩

theorem negative_eigenvalue_iff (m : ℕ) (hm : 3 ≤ m) {μ : ℝ} (hμ : μ < 0) :
    (realOperator m).HasEigenvalue μ ↔
      ∃ k : Fin (m - 2), μ = -positiveRoot m (k.val + 2) := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, realOperator, Matrix.charpoly_toLin',
    root_iff_mode m hm μ (ne_of_lt hμ)]
  constructor
  · rintro ⟨r, hr, hrm, hs⟩
    refine ⟨⟨r - 2, by omega⟩, ?_⟩
    have he : r - 2 + 2 = r := by omega
    simp only [he]
    have hn : -μ = positiveRoot m r := by
      apply (sq_eq_sq₀ (by linarith) (le_of_lt (positiveRoot_pos m r hr hrm))).mp
      rw [neg_sq, positiveRoot_sq m r hr]
      exact hs
    linarith
  · rintro ⟨k, rfl⟩
    refine ⟨k.val + 2, by omega, by omega, ?_⟩
    rw [neg_sq, positiveRoot_sq m _ (by omega)]

/-- Each complex eigenvalue outside the imaginary axis is real. -/
theorem off_axis_is_real (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) {μ : ℂ}
    (hμ : (actualOperator m).HasEigenvalue μ) (hre : μ.re ≠ 0) : μ.im = 0 := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, actualOperator,
    Matrix.charpoly_toLin', all_complex_roots m hm] at hμ
  obtain ⟨r, hr, hroot⟩ := hμ
  by_cases hrm : r = m
  · simp only [spectralRoot, if_pos hrm, neg_zero, or_self] at hroot
    simp [hroot] at hre
  · by_cases hr0 : r = 0
    · subst r
      rcases hroot with rfl | rfl <;>
        simp [spectralRoot, hrm, Complex.mul_re, Complex.div_re] at hre
    · by_cases hr1 : r = 1
      · subst r
        rcases hroot with rfl | rfl <;>
          simp [spectralRoot, hrm, Complex.mul_re, Complex.div_re] at hre
      · rcases hroot with rfl | rfl <;> simp [spectralRoot, hrm, hr0, hr1]

/-- Dipole and square have no complex eigenvalue with nonzero real part. -/
theorem small_spectral_neutrality (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) (hm2 : m ≤ 2)
    {μ : ℂ} (hμ : (actualOperator m).HasEigenvalue μ) : μ.re = 0 := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, actualOperator,
    Matrix.charpoly_toLin', all_complex_roots m hm] at hμ
  obtain ⟨r, hr, hroot⟩ := hμ
  interval_cases m <;> interval_cases r <;>
    rcases hroot with rfl | rfl <;>
    simp [spectralRoot, Complex.mul_re, Complex.div_re]

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealBoundary
