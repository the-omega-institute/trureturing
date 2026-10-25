import D5.S3.Geometry.Hyperideal.CFMPFrameMotion435Transient
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! Exact static affine Piola application in the last-coordinate chart. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators
open CFMPFrameMotion435Transient

namespace CFMPStaticAffinePiola435Transient
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ

def pullFlux (B : M3) (o : V) (H : V → V) (u : V) : V :=
  |B.det| • B⁻¹.mulVec (H (o+B.mulVec u))

theorem divergence_of_fderiv (F : V → V) (L : V →L[ℝ] V) (x : V)
    (hF : HasFDerivAt F L x) :
    divergence F x = (LinearMap.toMatrix' L.toLinearMap).trace := by
  have hd (i : Fin 3) :
      HasDerivAt (fun r : ℝ => F (x+r • basis i) i) ((L (basis i)) i) 0 := by
    have hi : HasDerivAt (fun r : ℝ => x+r • basis i) (basis i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (basis i)).const_add x
    have hF0 : HasFDerivAt F L (x+(0 : ℝ) • basis i) := by
      simpa only [zero_smul, add_zero] using hF
    have h := hF0.comp_hasDerivAt 0 hi
    simpa only [Function.comp_def] using hasDerivAt_pi.mp h i
  unfold divergence
  simp_rw [(hd _).deriv]
  rfl

theorem pullFlux_hasFDerivAt (B : M3) (o u : V) (H : V → V) (L : V →L[ℝ] V)
    (hH : HasFDerivAt H L (o+B.mulVec u)) :
    HasFDerivAt (pullFlux B o H)
      (|B.det| • ((B⁻¹).mulVecLin.toContinuousLinearMap.comp
        (L.comp B.mulVecLin.toContinuousLinearMap))) u := by
  have ha := (B.mulVecLin.toContinuousLinearMap.hasFDerivAt (x:=u)).const_add o
  have h := ((B⁻¹).mulVecLin.toContinuousLinearMap.hasFDerivAt.comp u (hH.comp u ha)).const_smul |B.det|
  exact h

theorem static_affine_piola (B : M3) (o u : V) (H : V → V) (L : V →L[ℝ] V)
    (hB : B.det ≠ 0) (hH : HasFDerivAt H L (o+B.mulVec u)) :
    divergence (pullFlux B o H) u = |B.det| * divergence H (o+B.mulVec u) := by
  rw [divergence_of_fderiv _ _ _ (pullFlux_hasFDerivAt B o u H L hH),
    divergence_of_fderiv H L _ hH]
  have hm : LinearMap.toMatrix'
      (|B.det| • ((B⁻¹).mulVecLin.toContinuousLinearMap.comp
        (L.comp B.mulVecLin.toContinuousLinearMap))).toLinearMap =
      |B.det| • (B⁻¹ * LinearMap.toMatrix' L.toLinearMap * B) := by
    change LinearMap.toMatrix' (|B.det| • ((B⁻¹).toLin'.comp
      (L.toLinearMap.comp B.toLin'))) = _
    rw [map_smul, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp]
    simp only [LinearMap.toMatrix'_toLin', Matrix.mul_assoc]
  rw [hm, Matrix.trace_smul, Matrix.trace_mul_cycle,
    Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB), Matrix.one_mul] <;> rfl

#print axioms static_affine_piola
end CFMPStaticAffinePiola435Transient
