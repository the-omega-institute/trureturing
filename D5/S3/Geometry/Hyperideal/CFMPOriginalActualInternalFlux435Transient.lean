import D5.S3.Geometry.Hyperideal.CFMPOriginalActualPairFlux435Transient

/-! Temporary exact application: all sixty actual internal moving-face fluxes cancel. -/
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

namespace CFMPOriginalActualInternalFlux435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem anchored_actual_internal_flux_sum_zero
    (l0 : Fin 6 → ℝ) (hl0 : ∀ k, 0 < l0 k)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (l : ℝ → Fin 6 → ℝ) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : HasDerivAt l dl t) (hbase : l t = l0) :
    let F : (Fin 20 × Fin 3) → parameterTriangle → HyperbolicThreeSpace :=
      fun j q => f ⟨xi l0 j.1 j.2 q.val,
        xi_mem_cutBody l0 hl0 j.1 j.2 q.val q.property⟩
    let c : (Fin 20 × Fin 3) → parameterTriangle → ℝ → Fin 3 → ℝ :=
      fun j q s => nativeMap
        (ambient (frame M0 (l s)) (facePoint (l s) j.1 j.2 q.val))
    let mu := (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)
    ∃ Phi : (Fin 20 × Fin 3) → HyperbolicThreeSpace → ℝ,
      (∀ j, ContinuousOn (Phi j) (range (F j)) ∧
        IntegrableOn (Phi j) (range (F j)) mu ∧
        ∀ q : parameterTriangle,
          c j q t = nativeCoordinates (F j q) ∧
          DifferentiableAt ℝ (c j q) t ∧
          dotProduct (deriv (c j q) t)
            (coordinateNormal (nativeCoordinates (F j q)) (unit M0 (A l0 j.1 j.2))) /
              (nativeCoordinates (F j q) 2)^2 = Phi j (F j q)) ∧
      (∑ n : Fin 20,∑ i : Fin 3,∫ z in range (F (n,i)),Phi (n,i) z ∂mu) = 0 := by
  classical
  let F : (Fin 20 × Fin 3) → parameterTriangle → HyperbolicThreeSpace :=
    fun j q => f ⟨xi l0 j.1 j.2 q.val,
      xi_mem_cutBody l0 hl0 j.1 j.2 q.val q.property⟩
  let c : (Fin 20 × Fin 3) → parameterTriangle → ℝ → Fin 3 → ℝ :=
    fun j q s => nativeMap
      (ambient (frame M0 (l s)) (facePoint (l s) j.1 j.2 q.val))
  let mu := (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)
  have hex (j : Fin 20 × Fin 3) :
      ∃ phi : HyperbolicThreeSpace → ℝ,
        ContinuousOn phi (range (F j)) ∧ IntegrableOn phi (range (F j)) mu ∧
        ∀ q : parameterTriangle,
          c j q t = nativeCoordinates (F j q) ∧
          DifferentiableAt ℝ (c j q) t ∧
          dotProduct (deriv (c j q) t)
            (coordinateNormal (nativeCoordinates (F j q)) (unit M0 (A l0 j.1 j.2))) /
              (nativeCoordinates (F j q) 2)^2 = phi (F j q) := by
    obtain ⟨phi,hcont,hint,htrace⟩ :=
      CFMPOriginalActualTraceIntegrability435Transient.anchored_actual_normal_trace_integrable
        l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase j.1 j.2
    exact ⟨phi,hcont,hint,fun q => (htrace q).2⟩
  choose Phi hcont hint htrace using hex
  let flux : (Fin 20 × Fin 3) → ℝ :=
    fun j => ∫ z in range (F j),Phi j z ∂mu
  have hG := CFMPAnchoredFrameContinuity435Transient.matrix_gram_rows M0 l0 hg0
  have hmeas (j : Fin 20 × Fin 3) : MeasurableSet (range (F j)) :=
    (CFMPOriginalTraceIntegrability435Transient.original_face_continuous_trace_integrable
      l0 hl0 M0 hm0 hG f hf j.1 j.2).1.isClosed_range.measurableSet
  have hpair (p : Fin 30) : flux (pairTable p).1 + flux (pairTable p).2 = 0 := by
    obtain ⟨phiA,phiB,hset,hca,hcb,hia,hib,hanti,hcancel,hta,htb⟩ :=
      CFMPOriginalActualPairFlux435Transient.anchored_actual_paired_flux_cancels
        l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase p
    have heqA : EqOn (Phi (pairTable p).1) phiA (range (F (pairTable p).1)) := by
      rintro z ⟨q,rfl⟩
      exact ((htrace (pairTable p).1 q).2.2).symm.trans (hta q).2.2
    have heqB : EqOn (Phi (pairTable p).2) phiB (range (F (pairTable p).2)) := by
      rintro z ⟨q,rfl⟩
      exact ((htrace (pairTable p).2 q).2.2).symm.trans (htb q).2.2
    change (∫ z in range (F (pairTable p).1),Phi (pairTable p).1 z ∂mu) +
      (∫ z in range (F (pairTable p).2),Phi (pairTable p).2 z ∂mu) = 0
    rw [setIntegral_congr_fun (hmeas _) heqA,setIntegral_congr_fun (hmeas _) heqB]
    exact hcancel
  refine ⟨Phi,fun j => ⟨hcont j,hint j,htrace j⟩,?_⟩
  let e : (Fin 30 × Bool) ≃ (Fin 20 × Fin 3) :=
    Equiv.ofBijective pairedOccurrence (by decide)
  calc
    _ = ∑ j : Fin 20 × Fin 3,flux j := (Fintype.sum_prod_type _).symm
    _ = ∑ j : Fin 30 × Bool,flux (e j) := (Equiv.sum_comp e _).symm
    _ = ∑ p : Fin 30,(flux (pairTable p).1 + flux (pairTable p).2) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro p _
      simp [e,pairedOccurrence,Fintype.sum_bool,add_comm]
    _ = 0 := by simp_rw [hpair];simp

end CFMPOriginalActualInternalFlux435Transient
