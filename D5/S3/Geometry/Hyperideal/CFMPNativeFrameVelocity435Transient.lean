import D5.S3.Geometry.Hyperideal.CFMPFrameContinuity435Transient
import D5.S3.Geometry.Hyperideal.CFMPNativePullbackMetric435Transient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPNativePullbackMetric435Transient
open D5.S3.Geometry.Hyperideal.LengthGramBody (lorentz)

namespace CFMPNativeFrameVelocity435Transient

theorem native_radial_zero (U : W) (hU : 0 < radius U) (hd : delta U ≠ 0) :
    (nativeMatrix U).mulVec U = 0 := by
  let s := Real.sqrt (radius U)
  let d := delta U
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hU).ne'
  have hsq : s^2 = -lorentz U U := Real.sq_sqrt hU.le
  have hn : (nativeMatrix U).mulVec U =
      ![U 0/d-U 0*(U 3-U 2)/d^2,
        U 1/d-U 1*(U 3-U 2)/d^2,
        -lorentz U U/(s*d)-s*(U 3-U 2)/d^2] := by
    ext i
    fin_cases i <;>
      simp [nativeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    all_goals dsimp [s,d]
    all_goals field_simp [show Real.sqrt (radius U) ≠ 0 from hs, hd]
    all_goals try simp [lorentz, Fin.sum_univ_four]
    all_goals ring_nf
    all_goals simp
  rw [hn]
  ext i
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Pi.zero_apply]
  · dsimp [d,delta]
    field_simp [show U 3-U 2 ≠ 0 from hd] <;> ring
  · dsimp [d,delta]
    field_simp [show U 3-U 2 ≠ 0 from hd] <;> ring
  · rw [← hsq]
    dsimp [d,delta]
    field_simp [hs,show U 3-U 2 ≠ 0 from hd] <;> ring

theorem frame_spatial_native_velocity (M D : M4) (x : V)
    (hM : M.det ≠ 0) (hq : 0 < q M x) (hd : delta (ambient M x) ≠ 0) :
    HasDerivAt
      (fun r : ℝ => nativeMap (ambient M (x + r • field (D * M⁻¹) x)))
      ((nativeMatrix (ambient M x)).mulVec (Matrix.vecMul (lift x) D)) 0 := by
  let K := D * M⁻¹
  have hK : K * M = D := by
    dsimp [K]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM),
      Matrix.mul_one]
  have hvec : Matrix.vecMul (tangent (field K x)) M =
      Matrix.vecMul (lift x) D - alpha K x • ambient M x := by
    rw [field_tangent, Matrix.sub_vecMul, Matrix.smul_vecMul,
      Matrix.vecMul_vecMul, hK]
    rfl
  have hf : HasFDerivAt nativeMap
      (nativeMatrix (ambient M x)).mulVecLin.toContinuousLinearMap
      (ambient M (x + (0 : ℝ) • field K x)) := by
    simpa only [zero_smul, add_zero] using
      nativeMap_hasFDerivAt (ambient M x) hq hd
  have h := hf.comp_hasDerivAt 0 (ambient_line M x (field K x))
  change HasDerivAt
    (fun r : ℝ => nativeMap (ambient M (x + r • field K x)))
    ((nativeMatrix (ambient M x)).mulVec (Matrix.vecMul (tangent (field K x)) M)) 0 at h
  rw [hvec, Matrix.mulVec_sub, Matrix.mulVec_smul,
    native_radial_zero (ambient M x) hq hd, smul_zero, sub_zero] at h
  exact h

theorem frame_time_native_velocity (M : ℝ → M4) (D : M4) (x : V) (t : ℝ)
    (hM : HasDerivAt M D t) (hq : 0 < q (M t) x)
    (hd : delta (ambient (M t) x) ≠ 0) :
    HasDerivAt (fun s => nativeMap (ambient (M s) x))
      ((nativeMatrix (ambient (M t) x)).mulVec (Matrix.vecMul (lift x) D)) t := by
  exact (nativeMap_hasFDerivAt (ambient (M t) x) hq hd).comp_hasDerivAt t
    (ambient_time M D x t hM)

theorem original_native_motion_balance (M : ℝ → M4) (D : M4) (x : V) (t : ℝ)
    (hM : HasDerivAt M D t) (hdet : (M t).det ≠ 0)
    (hq : 0 < q (M t) x) (hd : delta (ambient (M t) x) ≠ 0) :
    deriv (fun s => nativeMap (ambient (M s) x)) t =
      deriv (fun r : ℝ => nativeMap
        (ambient (M t) (x + r • field (D * (M t)⁻¹) x))) 0 := by
  rw [(frame_time_native_velocity M D x t hM hq hd).deriv,
    (frame_spatial_native_velocity (M t) D x hdet hq hd).deriv]

#print axioms original_native_motion_balance
end CFMPNativeFrameVelocity435Transient
