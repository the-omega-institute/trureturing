import D5.S3.Geometry.Hyperideal.CFMPNativeFrameVelocity435Transient

/-! Exact moving-point applications for the original native coordinates. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPNativePullbackMetric435Transient CFMPNativeFrameVelocity435Transient

namespace CFMPNativeMovingPoint435Transient

theorem tangent_add (v w : V) : tangent (v+w) = tangent v + tangent w := by
  ext i
  fin_cases i <;> simp [tangent] <;> ring

theorem lift_path (x : ℝ → V) (v : V) (t : ℝ) (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => lift (x s)) (tangent v) t := by
  have h0 := hasDerivAt_pi.mp hx 0
  have h1 := hasDerivAt_pi.mp hx 1
  have h2 := hasDerivAt_pi.mp hx 2
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [lift, tangent] using h0
  · simpa [lift, tangent] using h1
  · simpa [lift, tangent] using h2
  · simpa -implicitDefEqProofs [lift, tangent, Pi.sub_def] using
      ((((hasDerivAt_const t (1 : ℝ)).sub h0).sub h1).sub h2)

theorem ambient_moving (M : ℝ → M4) (D : M4) (x : ℝ → V) (v : V) (t : ℝ)
    (hM : HasDerivAt M D t) (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => ambient (M s) (x s))
      (Matrix.vecMul (tangent v) (M t) + Matrix.vecMul (lift (x t)) D) t := by
  have ha := lift_path x v t hx
  apply hasDerivAt_pi.mpr
  intro j
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 4)))
    (fun i _ => (hasDerivAt_pi.mp ha i).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hM i) j))
  convert h using 1
  · rfl
  · simp [Matrix.vecMul, dotProduct, Finset.sum_add_distrib]

theorem native_spatial_direction (M : M4) (x v : V)
    (hq : 0 < q M x) (hd : delta (ambient M x) ≠ 0) :
    HasDerivAt (fun r : ℝ => nativeMap (ambient M (x+r • v)))
      ((nativeMatrix (ambient M x)).mulVec (Matrix.vecMul (tangent v) M)) 0 := by
  have hf : HasFDerivAt nativeMap
      (nativeMatrix (ambient M x)).mulVecLin.toContinuousLinearMap
      (ambient M (x+(0 : ℝ) • v)) := by
    simpa only [zero_smul, add_zero] using nativeMap_hasFDerivAt (ambient M x) hq hd
  exact hf.comp_hasDerivAt 0 (ambient_line M x v)

theorem native_moving_derivative (M : ℝ → M4) (D : M4) (x : ℝ → V) (v : V) (t : ℝ)
    (hM : HasDerivAt M D t) (hx : HasDerivAt x v t)
    (hq : 0 < q (M t) (x t)) (hd : delta (ambient (M t) (x t)) ≠ 0) :
    HasDerivAt (fun s => nativeMap (ambient (M s) (x s)))
      ((nativeMatrix (ambient (M t) (x t))).mulVec
        (Matrix.vecMul (tangent v) (M t) + Matrix.vecMul (lift (x t)) D)) t := by
  exact (nativeMap_hasFDerivAt (ambient (M t) (x t)) hq hd).comp_hasDerivAt t
    (ambient_moving M D x v t hM hx)

theorem total_native_velocity (M : ℝ → M4) (D : M4) (x : ℝ → V) (v : V) (t : ℝ)
    (hM : HasDerivAt M D t) (hx : HasDerivAt x v t) (hdet : (M t).det ≠ 0)
    (hq : 0 < q (M t) (x t)) (hd : delta (ambient (M t) (x t)) ≠ 0) :
    deriv (fun s => nativeMap (ambient (M s) (x s))) t =
      deriv (fun r : ℝ => nativeMap (ambient (M t)
        (x t+r • (v+field (D*(M t)⁻¹) (x t))))) 0 := by
  have hfield :
      (nativeMatrix (ambient (M t) (x t))).mulVec
        (Matrix.vecMul (tangent (field (D*(M t)⁻¹) (x t))) (M t)) =
      (nativeMatrix (ambient (M t) (x t))).mulVec
        (Matrix.vecMul (lift (x t)) D) :=
    (native_spatial_direction (M t) (x t) (field (D*(M t)⁻¹) (x t)) hq hd).unique
      (frame_spatial_native_velocity (M t) D (x t) hdet hq hd)
  have hs := native_spatial_direction (M t) (x t)
    (v+field (D*(M t)⁻¹) (x t)) hq hd
  rw [tangent_add, Matrix.add_vecMul, Matrix.mulVec_add, hfield] at hs
  have ht := native_moving_derivative M D x v t hM hx hq hd
  rw [Matrix.mulVec_add] at ht
  rw [ht.deriv, hs.deriv]

#print axioms total_native_velocity
end CFMPNativeMovingPoint435Transient
