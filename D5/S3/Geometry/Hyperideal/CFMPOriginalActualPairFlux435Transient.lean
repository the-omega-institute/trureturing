import D5.S3.Geometry.Hyperideal.CFMPOriginalActualTraceIntegrability435Transient

/-! Temporary exact application: cancellation of the actual paired moving traces. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Matrix BigOperators ENNReal Classical
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPOriginalFacePairing435Transient
open CFMPOriginalPairedFaceMotion435Transient
open CFMPOriginalInternalFaceBridge435V2Transient
open CFMPOriginalInternalNormals435Transient
open CFMPOriginalNativeCoordinates435Transient
open CFMPNativePullbackMetric435Transient
open CFMPNativePlaneNormal435Transient
open CFMPFrameMotion435Transient
open CFMPFrameContinuity435Transient
open CFMPAnchoredSmoothFrame435Transient

namespace CFMPOriginalActualPairFlux435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem anchored_actual_paired_flux_cancels
    (l0 : Fin 6 → ℝ) (hl0 : ∀ k, 0 < l0 k)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (l : ℝ → Fin 6 → ℝ) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : HasDerivAt l dl t) (hbase : l t = l0) (p : Fin 30) :
    let a := (pairTable p).1
    let b := (pairTable p).2
    let F : (Fin 20 × Fin 3) → parameterTriangle → HyperbolicThreeSpace :=
      fun j q => f ⟨xi l0 j.1 j.2 q.val,
        xi_mem_cutBody l0 hl0 j.1 j.2 q.val q.property⟩
    let c : (Fin 20 × Fin 3) → parameterTriangle → ℝ → Fin 3 → ℝ :=
      fun j q s => nativeMap
        (ambient (frame M0 (l s)) (facePoint (l s) j.1 j.2 q.val))
    let mu := (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)
    ∃ phiA phiB : HyperbolicThreeSpace → ℝ,
      range (F a) = range (F b) ∧
      ContinuousOn phiA (range (F a)) ∧ ContinuousOn phiB (range (F b)) ∧
      IntegrableOn phiA (range (F a)) mu ∧
      IntegrableOn phiB (range (F b)) mu ∧
      EqOn phiA (fun z => -phiB z) (range (F a)) ∧
      (∫ z in range (F a),phiA z ∂mu) +
        (∫ z in range (F b),phiB z ∂mu) = 0 ∧
      (∀ q : parameterTriangle,
        c a q t = nativeCoordinates (F a q) ∧
        DifferentiableAt ℝ (c a q) t ∧
        dotProduct (deriv (c a q) t)
          (coordinateNormal (nativeCoordinates (F a q)) (unit M0 (A l0 a.1 a.2))) /
            (nativeCoordinates (F a q) 2)^2 = phiA (F a q)) ∧
      (∀ q : parameterTriangle,
        c b q t = nativeCoordinates (F b q) ∧
        DifferentiableAt ℝ (c b q) t ∧
        dotProduct (deriv (c b q) t)
          (coordinateNormal (nativeCoordinates (F b q)) (unit M0 (A l0 b.1 b.2))) /
            (nativeCoordinates (F b q) 2)^2 = phiB (F b q)) := by
  classical
  let a := (pairTable p).1
  let b := (pairTable p).2
  let F : (Fin 20 × Fin 3) → parameterTriangle → HyperbolicThreeSpace :=
    fun j q => f ⟨xi l0 j.1 j.2 q.val,
      xi_mem_cutBody l0 hl0 j.1 j.2 q.val q.property⟩
  let c : (Fin 20 × Fin 3) → parameterTriangle → ℝ → Fin 3 → ℝ :=
    fun j q s => nativeMap
      (ambient (frame M0 (l s)) (facePoint (l s) j.1 j.2 q.val))
  let mu := (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)
  obtain ⟨phiA,hca,hia,hta⟩ :=
    CFMPOriginalActualTraceIntegrability435Transient.anchored_actual_normal_trace_integrable
      l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase a.1 a.2
  obtain ⟨phiB,hcb,hib,htb⟩ :=
    CFMPOriginalActualTraceIntegrability435Transient.anchored_actual_normal_trace_integrable
      l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase b.1 b.2
  have hset : range (F a) = range (F b) := paired_native_face l0 hl0 f p
  have hparam (q : parameterTriangle) : pairedParam p q.val ∈ parameterTriangle := by
    change 0 ≤ pairedParam p q.val 0 ∧ 0 ≤ pairedParam p q.val 1 ∧
      pairedParam p q.val 0 + pairedParam p q.val 1 ≤ 1
    unfold pairedParam
    split_ifs
    · exact ⟨q.property.2.1,q.property.1,by simpa [add_comm] using q.property.2.2⟩
    · exact q.property
  have hpoint (q : parameterTriangle) :
      F a q = F b ⟨pairedParam p q.val,hparam q⟩ := by
    apply congrArg f
    apply Subtype.ext
    exact pair_xi l0 p q.val
  have hanti : EqOn phiA (fun z => -phiB z) (range (F a)) := by
    rintro z ⟨q,rfl⟩
    let q' : parameterTriangle := ⟨pairedParam p q.val,hparam q⟩
    have hvel : deriv (c a q) t = deriv (c b q') t :=
      paired_native_velocities l (fun s => frame M0 (l s)) p q.val t
    have hn : unit M0 (A l0 a.1 a.2) = -unit M0 (A l0 b.1 b.2) :=
      paired_normals l0 M0 p
    calc
      phiA (F a q) = dotProduct (deriv (c a q) t)
          (coordinateNormal (nativeCoordinates (F a q)) (unit M0 (A l0 a.1 a.2))) /
            (nativeCoordinates (F a q) 2)^2 := (hta q).2.2.2.symm
      _ = -(dotProduct (deriv (c b q') t)
          (coordinateNormal (nativeCoordinates (F b q')) (unit M0 (A l0 b.1 b.2))) /
            (nativeCoordinates (F b q') 2)^2) := by
        rw [hvel,hpoint q,hn,coordinateNormal_neg,dotProduct_neg,neg_div]
      _ = -phiB (F b q') := congrArg Neg.neg (htb q').2.2.2
      _ = -phiB (F a q) := by rw [hpoint q]
  have hG := CFMPAnchoredFrameContinuity435Transient.matrix_gram_rows M0 l0 hg0
  have hclosed :=
    (CFMPOriginalTraceIntegrability435Transient.original_face_continuous_trace_integrable
      l0 hl0 M0 hm0 hG f hf a.1 a.2).1
  have hm : MeasurableSet (range (F a)) := hclosed.isClosed_range.measurableSet
  refine ⟨phiA,phiB,hset,hca,hcb,hia,hib,hanti,?_,?_,?_⟩
  · rw [setIntegral_congr_fun hm hanti,integral_neg,← hset]
    exact neg_add_cancel _
  · intro q
    exact (hta q).2
  · intro q
    exact (htb q).2

end CFMPOriginalActualPairFlux435Transient
