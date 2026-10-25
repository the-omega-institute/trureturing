import D5.S3.Geometry.Hyperideal.CFMPNativePullbackBridge435Transient
import D5.S3.Geometry.Hyperideal.CFMPReflectedPlaneChart435Transient
import Mathlib.LinearAlgebra.CrossProduct

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open CFMPLorentzLiftSurface435Transient
open CFMPNativePullbackMetric435Transient
open CFMPNativePullbackBridge435Transient

namespace CFMPNativeSurfaceJacobian435Transient

def dropPlane (U : W) : CFMPReflectedPlaneChart435Transient.W := ![U 0,U 2,U 3]
def planeColumns (b c : W) : CFMPReflectedPlaneChart435Transient.A32 :=
  !![b 0,c 0; b 2,c 2; b 3,c 3]
def gram3 (U b c : W) : ℝ :=
  lorentz U U * (lorentz b b * lorentz c c - (lorentz b c)^2) -
  lorentz U b * (lorentz U b * lorentz c c - lorentz U c * lorentz b c) +
  lorentz U c * (lorentz U b * lorentz b c - lorentz U c * lorentz b b)

theorem pairing_symm (u v : W) : lorentz u v = lorentz v u := by
  simp [lorentz,Fin.sum_univ_four]
  ring

theorem plane_gram_det (U b c : W) (hU : U 1 = 0) (hb : b 1 = 0) (hc : c 1 = 0) :
    (CFMPReflectedPlaneChart435Transient.augmented (planeColumns b c) (dropPlane U)).det^2 =
      -gram3 U b c := by
  simp [CFMPReflectedPlaneChart435Transient.augmented,planeColumns,dropPlane,
    gram3,lorentz,Fin.sum_univ_four,Matrix.det_fin_three,hU,hb,hc]
  ring

theorem reflected_gram_det (U b c : W) (R : W →ₗ[ℝ] W)
    (hR : ∀ u v, lorentz (R u) (R v) = lorentz u v)
    (hU : R U 1 = 0) (hb : R b 1 = 0) (hc : R c 1 = 0) :
    (CFMPReflectedPlaneChart435Transient.augmented
      (planeColumns (R b) (R c)) (dropPlane (R U))).det^2 = -gram3 U b c := by
  have h := plane_gram_det (R U) (R b) (R c) hU hb hc
  simpa only [gram3,hR] using h

theorem native_surface_gram_det (U b c : W) (hr : 0 < radius U) (hd : delta U ≠ 0)
    (R : W →ₗ[ℝ] W) (hR : ∀ u v, lorentz (R u) (R v) = lorentz u v)
    (hU : R U 1 = 0) (hb : R b 1 = 0) (hc : R c 1 = 0) :
    let db := (nativeMatrix U).mulVec b
    let dc := (nativeMatrix U).mulVec c
    dotProduct (db ⨯₃ dc) (db ⨯₃ dc) / (nativeMap U 2)^4 =
      (CFMPReflectedPlaneChart435Transient.augmented
        (planeColumns (R b) (R c)) (dropPlane (R U))).det^2 / (radius U)^3 := by
  let db := (nativeMatrix U).mulVec b
  let dc := (nativeMatrix U).mulVec c
  have hh : nativeMap U 2 ≠ 0 := div_ne_zero (Real.sqrt_pos.mpr hr).ne' hd
  have hUU : lorentz U U = -radius U := by simp [radius]
  calc
    _ = (dotProduct db db / (nativeMap U 2)^2) *
          (dotProduct dc dc / (nativeMap U 2)^2) -
        (dotProduct db dc / (nativeMap U 2)^2) *
          (dotProduct dc db / (nativeMap U 2)^2) := by
      rw [cross_dot_cross]
      field_simp [hh]
      <;> ring
    _ = -gram3 U b c / (radius U)^3 := by
      rw [coordinate_pullback_pairing U b b hr hd,
        coordinate_pullback_pairing U c c hr hd,
        coordinate_pullback_pairing U b c hr hd,
        coordinate_pullback_pairing U c b hr hd]
      rw [pairing_symm c b]
      dsimp only [gram3]
      rw [hUU]
      field_simp [hr.ne']
      <;> ring
    _ = _ := by rw [← reflected_gram_det U b c R hR hU hb hc]

theorem native_surface_jacobian (U b c : W) (hr : 0 < radius U) (hd : delta U ≠ 0)
    (R : W →ₗ[ℝ] W) (hR : ∀ u v, lorentz (R u) (R v) = lorentz u v)
    (hU : R U 1 = 0) (hb : R b 1 = 0) (hc : R c 1 = 0) :
    let db := (nativeMatrix U).mulVec b
    let dc := (nativeMatrix U).mulVec c
    Real.sqrt (dotProduct (db ⨯₃ dc) (db ⨯₃ dc)) / (nativeMap U 2)^2 =
      |(CFMPReflectedPlaneChart435Transient.augmented
        (planeColumns (R b) (R c)) (dropPlane (R U))).det| / (Real.sqrt (radius U))^3 := by
  let db := (nativeMatrix U).mulVec b
  let dc := (nativeMatrix U).mulVec c
  let C := (CFMPReflectedPlaneChart435Transient.augmented
    (planeColumns (R b) (R c)) (dropPlane (R U))).det
  let X := Real.sqrt (dotProduct (db ⨯₃ dc) (db ⨯₃ dc)) / (nativeMap U 2)^2
  let Y := |C| / (Real.sqrt (radius U))^3
  have hn : 0 ≤ dotProduct (db ⨯₃ dc) (db ⨯₃ dc) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg ((db ⨯₃ dc) i))
  have hX : 0 ≤ X := div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  have hY : 0 ≤ Y := div_nonneg (abs_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) 3)
  have hXs : X^2 = dotProduct (db ⨯₃ dc) (db ⨯₃ dc)/(nativeMap U 2)^4 := by
    dsimp only [X]
    rw [div_pow,Real.sq_sqrt hn]
    ring
  have hden : ((Real.sqrt (radius U))^3)^2 = (radius U)^3 := by
    calc
      _ = ((Real.sqrt (radius U))^2)^3 := by ring
      _ = _ := by rw [Real.sq_sqrt hr.le]
  have hYs : Y^2 = C^2/(radius U)^3 := by
    dsimp only [Y]
    rw [div_pow,sq_abs,hden]
  have hg := native_surface_gram_det U b c hr hd R hR hU hb hc
  have heq : X^2 = Y^2 := hXs.trans (hg.trans hYs.symm)
  change X = Y
  nlinarith

end CFMPNativeSurfaceJacobian435Transient
