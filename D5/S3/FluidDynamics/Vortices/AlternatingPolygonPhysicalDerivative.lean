/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonPhysicalDerivative
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonPhysicalDerivative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The physical Frechet derivative and explicit real Cartesian chain at every positive parameter pair. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain

/-! The positive-parameter matrix and chain belong to the genuine Cartesian field. -/
noncomputable section

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
open AlternatingPolygonSpectrum AlternatingPolygonRealSpaces AlternatingPolygonCartesianChain
open AlternatingPolygonPhysicalSpectrum

/-- The physical Frechet derivative is exactly 2*Omega times the canonical Cartesian Jacobian. -/
theorem physical_derivative (N : ℕ) {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) :
    HasFDerivAt (AlternatingPolygonParameters.field N b Ω)
      (((2 * Ω) • jacobian N).toLin'.toContinuousLinearMap)
      (AlternatingPolygonParameters.radius b Ω • polygon N) := by
  have hR := ne_of_gt (AlternatingPolygonParameters.radius_pos hb hΩ)
  have hbR : b = 4 * Ω * AlternatingPolygonParameters.radius b Ω ^ 2 := by
    rw [AlternatingPolygonParameters.radius_sq hb hΩ]
    field_simp
  have hz := (AlternatingPolygonParameters.collision_free_smul hR).mpr
    (AlternatingPolygonParameters.polygon_collision_free N)
  have h := AlternatingPolygonDerivative.hasFDerivAt_field b Ω hz
  rw [AlternatingPolygonParameters.jacobian_scaling N hR hbR] at h
  exact h

/-- The exact source's real Cartesian chain transports to every positive b and Omega. -/
theorem physical_cartesian_chain (m : ℕ) (hm : 1 ≤ m)
    {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) :
    physicalRealOperator m b Ω (cartesian0 m) = 0 ∧
      physicalRealOperator m b Ω ((2 * Ω)⁻¹ • cartesian1 m) = cartesian0 m := by
  rw [physicalRealOperator_eq m hb hΩ]
  constructor
  · simp only [LinearMap.smul_apply, (cartesian_chain m hm).1, smul_zero]
  · rw [LinearMap.smul_apply, map_smul, (cartesian_chain m hm).2, smul_smul,
      mul_inv_cancel₀ (by positivity : (2 : ℝ) * Ω ≠ 0), one_smul]

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
