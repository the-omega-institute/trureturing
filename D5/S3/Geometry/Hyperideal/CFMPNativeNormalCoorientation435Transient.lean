import D5.S3.Geometry.Hyperideal.CFMPNativePlaneNormal435Transient

noncomputable section
set_option autoImplicit false
open Filter Set
open scoped Topology Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open CFMPLorentzLiftSurface435Transient
open CFMPNativePlaneNormal435Transient

namespace CFMPNativeNormalCoorientation435Transient

theorem normal_plane_derivative (p : V) (N : W) (hp : p 2 ≠ 0)
    (hplane : lorentz (coordinateLift p) N = 0) (hunit : lorentz N N = 1) :
    HasDerivAt (fun t : ℝ =>
      lorentz (coordinateLift (p+t • coordinateNormal p N)) N) 1 0 := by
  have hline : HasDerivAt (fun t : ℝ => p+t • coordinateNormal p N)
      (coordinateNormal p N) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateNormal p N)).const_add p
  have hL : HasDerivAt (fun t : ℝ => coordinateLift (p+t • coordinateNormal p N)) N 0 := by
    have h := (coordinateLift_hasFDerivAt p hp).comp_hasDerivAt_of_eq 0 hline (by simp)
    change HasDerivAt (fun t : ℝ => coordinateLift (p+t • coordinateNormal p N))
      ((liftMatrix p).mulVec (coordinateNormal p N)) 0 at h
    rw [coordinateNormal_lift p N hp hplane] at h
    exact h
  have hc (i : Fin 4) : HasDerivAt
      (fun t : ℝ => coordinateLift (p+t • coordinateNormal p N) i) (N i) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj i : W →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hL
  have h := ((((hc 0).mul_const (N 0)).add ((hc 1).mul_const (N 1))).add
    ((hc 2).mul_const (N 2))).sub ((hc 3).mul_const (N 3))
  have hu : N 0*N 0+N 1*N 1+N 2*N 2-N 3*N 3 = 1 := by
    simpa [lorentz, Fin.sum_univ_four, sub_eq_add_neg] using hunit
  convert h using 1
  · funext t
    simp [lorentz, Fin.sum_univ_four]
    <;> ring
  · exact hu.symm

-- Positive parameter moves into the positive defining-function side.
-- Thus this is the outward choice for a body on the nonpositive side.
theorem normal_points_positive (p : V) (N : W) (hp : 0 < p 2)
    (hplane : lorentz (coordinateLift p) N = 0) (hunit : lorentz N N = 1) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 < (p+t • coordinateNormal p N) 2 ∧
      0 < lorentz (coordinateLift (p+t • coordinateNormal p N)) N := by
  have hd := normal_plane_derivative p N hp.ne' hplane hunit
  have hs : Tendsto (fun t : ℝ =>
      lorentz (coordinateLift (p+t • coordinateNormal p N)) N / t)
      (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    simpa [hplane, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hd.tendsto_slope_zero_right
  have hquot : ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 < lorentz (coordinateLift (p+t • coordinateNormal p N)) N / t :=
    hs.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hh : ContinuousAt (fun t : ℝ => (p+t • coordinateNormal p N) 2) 0 := by
    fun_prop
  have hheight : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      0 < (p+t • coordinateNormal p N) 2 :=
    continuousAt_const.eventually_lt hh (by simpa using hp)
  filter_upwards [hquot,hheight.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
    with t ht hh htpos
  exact ⟨hh, (div_pos_iff_of_pos_right htpos).mp ht⟩

end CFMPNativeNormalCoorientation435Transient
