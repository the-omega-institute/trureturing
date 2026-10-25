import D5.S3.Geometry.Hyperideal.CFMPOriginalNormalDerivative435Transient
import D5.S3.Geometry.Hyperideal.CFMPActualPlaneIsometry435Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Elementwise
open Set Filter
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPAnchoredSmoothFrame435Transient
open CFMPOriginalCellsIndependent435Transient CFMPActualCellMotion435Transient
open CFMPOriginalExteriorFaceChart435Transient CFMPOriginalExteriorNativeNormal435Transient
open CFMPAnchoredOriginalExteriorFaceMotion435Transient
open CFMPNativePullbackMetric435Transient CFMPNativePullbackBridge435Transient
open CFMPOriginalNativeCoordinates435Transient CFMPNativePlaneNormal435Transient

namespace CFMPOriginalNormalSpeedDerivative435Transient

theorem lorentz_pair_derivative (X Y : ℝ → Fin 4 → ℝ)
    (dX dY : Fin 4 → ℝ) (t : ℝ)
    (hX : HasDerivAt X dX t) (hY : HasDerivAt Y dY t) :
    HasDerivAt (fun s => lorentz (X s) (Y s))
      (lorentz dX (Y t) + lorentz (X t) dY) t := by
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 4)))
    (fun i _ => ((hasDerivAt_pi.mp hX i).const_mul
      (![(1 : ℝ),1,1,-1] i)).mul (hasDerivAt_pi.mp hY i))
  convert h using 1
  · rfl
  · simp [lorentz, Fin.sum_univ_four]
    ring

private theorem pair_smul_right (X Y : Fin 4 → ℝ) (a : ℝ) :
    lorentz X (a • Y) = a * lorentz X Y := by
  simpa only [zero_smul, add_zero, zero_mul, add_zero] using lorentz_right X Y Y a 0

private theorem pair_smul_left (X Y : Fin 4 → ℝ) (a : ℝ) :
    lorentz (a • X) Y = a * lorentz X Y := by
  rw [lorentz_symm, pair_smul_right, lorentz_symm Y X]

theorem actual_normal_speed_derivative
    (l0 : Fin 6 → ℝ) (hl0 : ∀ k, 0 < l0 k)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (l : ℝ → Fin 6 → ℝ) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : HasDerivAt l dl t) (hbase : l t = l0)
    (n : Fin 20) (u : Fin 2 → ℝ) (hu : u ∈ parameterTriangle) :
    let P : ℝ → M4 := fun s => frame M0 (l s)
    let N : ℝ → Fin 4 → ℝ := fun s => unit (l s) (P s) n
    let c : ℝ → Fin 3 → ℝ := fun s =>
      nativeMap (ambient (P s) (facePoint (l s) n u))
    let w : cutBody l0 := ⟨xi l0 n u, xi_mem_cutBody l0 hl0 n u hu⟩
    let p := nativeCoordinates (f w)
    DifferentiableAt ℝ N t ∧ DifferentiableAt ℝ c t ∧
      dotProduct (deriv c t) (coordinateNormal p (unit l0 M0 n)) / (p 2)^2 =
        -lorentz (coordinateLift p) (deriv N t) := by
  let P : ℝ → M4 := fun s => frame M0 (l s)
  let N : ℝ → Fin 4 → ℝ := fun s => unit (l s) (P s) n
  let U : ℝ → Fin 4 → ℝ := fun s => ambient (P s) (facePoint (l s) n u)
  let c : ℝ → Fin 3 → ℝ := fun s => nativeMap (U s)
  let w : cutBody l0 := ⟨xi l0 n u, xi_mem_cutBody l0 hl0 n u hu⟩
  let p := nativeCoordinates (f w)
  have hgood : good (H M0 l0) := by
    rw [normalized_base M0 hm0 l0 hg0]
    exact base.2
  have hframe : DifferentiableAt ℝ (frame M0) (l t) := by
    rw [hbase]
    exact (smooth_frame M0 l0 hgood).differentiableAt (by simp)
  have hP : DifferentiableAt ℝ P t := hframe.comp t hl.differentiableAt
  have hPt : P t = M0 := by
    dsimp only [P]
    rw [hbase, anchored M0 hm0 l0 hg0]
  have hUt : U t = w.val ᵥ* M0 := by
    change ambient (P t) (facePoint (l t) n u) = _
    rw [hPt, hbase]
    exact congrArg (fun v => v ᵥ* M0) (lift_facePoint l0 hl0 n u)
  have hface := facePoint_differentiable l t hl.differentiableAt n u
  have hU : DifferentiableAt ℝ U t :=
    (CFMPNativeMovingPoint435Transient.ambient_moving P (deriv P t)
      (fun s => facePoint (l s) n u) _ t hP.hasDerivAt hface.hasDerivAt).differentiableAt
  have hnormal := CFMPOriginalNormalDerivative435Transient.actual_normal_derivative
    l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase n
  have hN : DifferentiableAt ℝ N t := hnormal.2.1
  have hNt : N t = unit l0 M0 n := hnormal.1
  have hgoodEventually : ∀ᶠ s in 𝓝 t, good (H M0 (l s)) := by
    have hc := (smooth_H M0).continuous.continuousAt.comp hl.continuousAt
    exact hc.eventually (good_open.mem_nhds (by simpa only [Function.comp_apply, Set.mem_setOf_eq, hbase] using hgood))
  have hposEventually : ∀ᶠ s in 𝓝 t, ∀ i, 0 < l s i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc := continuousAt_pi.mp hl.continuousAt i
    exact hc.eventually (Ioi_mem_nhds (by simpa only [hbase] using hl0 i))
  have hzero : (fun s => lorentz (U s) (N s)) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [hgoodEventually, hposEventually] with s hgood hpos
    have hdet := frame_det_nonzero M0 hm0 (l s) hgood
    change lorentz (CFMPFrameMotion435Transient.lift (facePoint (l s) n u) ᵥ* P s)
      ((Real.sqrt (lorentz (raw (l s) (P s) n) (raw (l s) (P s) n)))⁻¹ •
        raw (l s) (P s) n) = 0
    rw [lift_facePoint (l s) hpos n u, pair_smul_right,
      pair_raw (l s) (P s) hdet n, face_readout (l s) hpos n u, mul_zero]
  have hpair := lorentz_pair_derivative U N (deriv U t) (deriv N t) t
    hU.hasDerivAt hN.hasDerivAt
  have hconstant : HasDerivAt (fun _ : ℝ => (0 : ℝ))
      (lorentz (deriv U t) (N t) + lorentz (U t) (deriv N t)) t :=
    hpair.congr_of_eventuallyEq hzero.symm
  have hbalance := hconstant.unique (hasDerivAt_const t (0 : ℝ))
  have hplane : lorentz (U t) (N t) = 0 := hzero.self_of_nhds
  have hcoord := original_native_coordinates l0 hl0 M0 f hf w
  have hR : 0 < radius (U t) := by simpa only [hUt] using hcoord.1
  have hd : delta (U t) ≠ 0 := by simpa only [hUt] using hcoord.2.1.ne'
  have hct : c t = p := by
    change nativeMap (U t) = _
    rw [hUt]
    exact hcoord.2.2.symm
  have hc := (nativeMap_hasFDerivAt (U t) hR hd).comp_hasDerivAt t hU.hasDerivAt
  have hdc : deriv c t = (nativeMatrix (U t)).mulVec (deriv U t) := hc.deriv
  have hp : p 2 ≠ 0 := (f w).coordinates.property.ne'
  have hLift : coordinateLift p = (Real.sqrt (radius (U t)))⁻¹ • U t := by
    change lift (f w) = _
    rw [hUt]
    exact CFMPActualPlaneIsometry435Transient.original_frame_normalized_lift
      l0 M0 (CFMPAnchoredFrameContinuity435Transient.matrix_gram_rows M0 l0 hg0) f hf w
  have hnativeplane : lorentz (coordinateLift p) (unit l0 M0 n) = 0 := by
    rw [hLift, pair_smul_left, ← hNt, hplane, mul_zero]
  refine ⟨hN, hc.differentiableAt, ?_⟩
  rw [coordinateNormal_pairing p (deriv c t) (unit l0 M0 n) hp hnativeplane,
    hdc, ← hct, derivative_intertwining (U t) (deriv U t) hR hd]
  change lorentz (normalizedTangent (U t) (deriv U t)) (unit l0 M0 n) =
    -lorentz (coordinateLift p) (deriv N t)
  rw [← hNt, hLift]
  have hexpand : lorentz (normalizedTangent (U t) (deriv U t)) (N t) =
      (Real.sqrt (radius (U t)))⁻¹ * lorentz (deriv U t) (N t) +
      (lorentz (U t) (deriv U t) / (Real.sqrt (radius (U t)))^3) *
        lorentz (U t) (N t) := by
    simp only [normalizedTangent]
    simpa only [one_smul, zero_smul, add_zero, mul_one, mul_zero, zero_mul, zero_add] using
      lorentz_linear (deriv U t) (U t) (N t) (N t)
        ((Real.sqrt (radius (U t)))⁻¹)
        (lorentz (U t) (deriv U t) / (Real.sqrt (radius (U t)))^3) 1 0
  rw [hexpand, hplane, mul_zero, add_zero, pair_smul_left]
  linear_combination (Real.sqrt (radius (U t)))⁻¹ * hbalance

end CFMPOriginalNormalSpeedDerivative435Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPOriginalNormalSpeedDerivative435Transient.lorentz_pair_derivative,
      ``CFMPOriginalNormalSpeedDerivative435Transient.actual_normal_speed_derivative] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP598 declaration absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP598 disallowed axiom {ax} for {name}"
    Lean.logInfo m!"CFMP598 CHECKED {name} axioms={axioms}"
