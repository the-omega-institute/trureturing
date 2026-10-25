import D5.S3.Geometry.Hyperideal.CFMPNativeMetricSpeed435Transient

noncomputable section
set_option autoImplicit false
open Filter Set
open scoped Topology Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient
open CFMPNativePullbackMetric435Transient
open CFMPNativePullbackBridge435Transient
open CFMPOriginalNativeCoordinates435Transient
open CFMPNativeMetricSpeed435Transient

namespace CFMPOriginalNativeMetricSpeed435Transient

def positiveCoordinateCurve (p : UpperHalfSpace ℂ) (F : ℝ → V) (t : ℝ) :
    UpperHalfSpace ℂ :=
  if h : 0 < F t 2 then ⟨packLinear (F t),h⟩ else p

theorem pack_nativeCoordinates (p : HyperbolicThreeSpace) :
    packLinear (nativeCoordinates p) = p.coordinates.val := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply Complex.ext <;> rfl
  · rfl

-- The curve is an ambient coordinate extension at the same original point.
-- It is not asserted to stay in the closed cut body for both time directions.
theorem original_native_metric_speed
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (ξ : cutBody l) (η : W) :
    ∃ γ : ℝ → UpperHalfSpace ℂ,
      γ 0 = (f ξ).coordinates ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), (γ t).val =
        packLinear (nativeMap ((ξ.val+t • η) ᵥ* M))) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ hmem : ξ.val+t • η ∈ cutBody l,
        HyperbolicSpace.mk (γ t) = f ⟨ξ.val+t • η,hmem⟩) ∧
      Tendsto (fun t => (dist (f ξ) (HyperbolicSpace.mk (γ t))/|t|)^2)
        (𝓝[≠] 0)
        (𝓝 (lorentz (η ᵥ* M) (η ᵥ* M)/radius (ξ.val ᵥ* M) +
          lorentz (ξ.val ᵥ* M) (η ᵥ* M)*lorentz (ξ.val ᵥ* M) (η ᵥ* M)/
            (radius (ξ.val ᵥ* M))^2)) := by
  obtain ⟨hr,hd,hcoord⟩ := original_native_coordinates l hl M f hf ξ
  let U := ξ.val ᵥ* M
  let v := η ᵥ* M
  let z := (nativeMatrix U).mulVec v
  let F : ℝ → V := fun t => nativeMap ((ξ.val+t • η) ᵥ* M)
  have hline : HasDerivAt (fun t : ℝ => ξ.val+t • η) η 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const η).const_add ξ.val
  have hF : HasDerivAt F z 0 := by
    have h := (coefficient_coordinate_hasFDerivAt M ξ.val hr hd.ne').comp_hasDerivAt_of_eq
      0 hline (by simp)
    simpa! [F,z,U,v,Function.comp_def] using h
  have hF0 : F 0 = nativeCoordinates (f ξ) := by simpa [F] using hcoord.symm
  have hpos : 0 < F 0 2 := by
    rw [hF0]
    exact (f ξ).coordinates.property
  have hposnear : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < F t 2 :=
    continuousAt_const.eventually_lt ((continuous_apply (2 : Fin 3)).continuousAt.comp hF.continuousAt) hpos
  let γ := positiveCoordinateCurve (f ξ).coordinates F
  have he : (fun t => (γ t).val) =ᶠ[𝓝 (0 : ℝ)] (fun t => packLinear (F t)) := by
    filter_upwards [hposnear] with t ht
    simp [γ,positiveCoordinateCurve,ht]
  have hγ : HasDerivAt (fun t => (γ t).val) (packLinear z) 0 :=
    ((packLinear.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0 hF).congr_of_eventuallyEq he
  have hγ0 : γ 0 = (f ξ).coordinates := by
    apply Subtype.ext
    simp only [γ,positiveCoordinateCurve,dif_pos hpos]
    rw [hF0,pack_nativeCoordinates]
  have hsame : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ hmem : ξ.val+t • η ∈ cutBody l,
      HyperbolicSpace.mk (γ t) = f ⟨ξ.val+t • η,hmem⟩ := by
    filter_upwards [he] with t ht
    intro hmem
    have hc := (original_native_coordinates l hl M f hf ⟨ξ.val+t • η,hmem⟩).2.2
    have ha : (γ t).val = (f ⟨ξ.val+t • η,hmem⟩).coordinates.val := by
      change nativeCoordinates (f ⟨ξ.val+t • η,hmem⟩) = F t at hc
      rw [ht,← hc,pack_nativeCoordinates]
    have hn : γ t = (f ⟨ξ.val+t • η,hmem⟩).coordinates := Subtype.ext ha
    rw [hn]
  refine ⟨γ,hγ0,he,hsame,?_⟩
  have hlim := native_coordinate_speed γ z hγ
  rw [hγ0] at hlim
  have hheight : height (f ξ).coordinates = nativeMap U 2 := by
    have h := congrFun hcoord 2
    exact h
  have hpoint : HyperbolicSpace.mk (f ξ).coordinates = f ξ := by cases f ξ; rfl
  rw [hpoint,hheight,coordinate_pullback_pairing U v v hr hd.ne'] at hlim
  exact hlim

end CFMPOriginalNativeMetricSpeed435Transient
