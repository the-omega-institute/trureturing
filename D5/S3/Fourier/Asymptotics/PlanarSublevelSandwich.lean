/- GID: D5/S3/Fourier/Asymptotics/PlanarSublevelSandwich
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/PlanarSublevelSandwich
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smooth test functions bound a planar sublevel near a regular zero. -/

import OmegaMath.Analysis.PlanarSublevelSandwich

/-! Lean reference for the regular-zero sublevel bounds in the two-clock argument. -/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace D5.S3.Fourier.Asymptotics.PlanarSublevelSandwich

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Fixed smooth planar windows bracket a small sublevel around a regular zero. -/
theorem smooth_local_ellipse_sandwich {f : Plane → Plane} {z : Plane}
    (A : Plane ≃L[ℝ] Plane) (hf : HasFDerivAt f (A : Plane →L[ℝ] Plane) z) (hz : f z = 0)
    {η ρ σ : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hρ : 0 < ρ) (hρ' : ρ < (1 + η)⁻¹) (hσ : (1 - η)⁻¹ < σ) :
    let determinant := |LinearMap.det (A.toLinearEquiv : Plane →ₗ[ℝ] Plane)|
    ∃ (r : ℝ) (lower upper : Plane → ℝ), 0 < r ∧
      ContDiff ℝ ∞ lower ∧ ContDiff ℝ ∞ upper ∧
      HasCompactSupport lower ∧ HasCompactSupport upper ∧
      Real.pi * ρ ^ 2 / determinant ≤ (∫ u, lower u) ∧
      (∫ u, upper u) ≤ Real.pi * σ ^ 2 / determinant ∧
      ∀ ε > 0, ε * (‖(A.symm : Plane →L[ℝ] Plane)‖ * (1 + η)⁻¹) < r →
        ∀ u : Plane, lower u ≤ (if ε * ‖u‖ < r ∧ ‖f (z + ε • u)‖ < ε then 1 else 0) ∧
          (if ε * ‖u‖ < r ∧ ‖f (z + ε • u)‖ < ε then 1 else 0) ≤ upper u :=
  Omega.Analysis.PlanarSublevelSandwich.smooth_local_ellipse_sandwich A hf hz hη hη1 hρ hρ' hσ

#print axioms smooth_local_ellipse_sandwich

end D5.S3.Fourier.Asymptotics.PlanarSublevelSandwich
