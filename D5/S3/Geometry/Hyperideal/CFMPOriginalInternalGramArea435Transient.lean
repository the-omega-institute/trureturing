import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalMomentArea435Transient

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient
open CFMPOriginalInternalFaceBridge435V2Transient
open CFMPPlaneMomentDivergence435Transient CFMPPlaneEdgeCofactor435Transient
open CFMPPlaneDualConormal435Transient CFMPOriginalInternalMomentArea435Transient

namespace CFMPOriginalInternalGramArea435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem scalar_gram_det (U b c : W) :
    (gram (pairingEntries U b c)).det =
      CFMPNativeSurfaceJacobian435Transient.gram3 U b c := by
  rw [Matrix.det_fin_three]
  simp [gram,pairingEntries,CFMPNativeSurfaceJacobian435Transient.gram3]
  ring

theorem internal_gram_cofactor
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) :
    (gram (pairingEntries (faceV0 l M n) (faceB l M n i) (faceC l M n i))).det =
      -M.det^2 * lorentz
        (CFMPOriginalInternalNormals435Transient.raw M
          (CFMPOriginalFacePairing435Transient.coefficient l n i))
        (CFMPOriginalInternalNormals435Transient.raw M
          (CFMPOriginalFacePairing435Transient.coefficient l n i)) := by
  have hN := CFMPOriginalInternalNormals435Transient.raw_spacelike l hl M hM f hf n i
  rw [CFMPOriginalFaceDensity435Transient.raw_norm l hl M n i 0] at hN
  have h := CFMPActualCoefficientDensity435Transient.actual_face_gram M hM
    (CFMPOriginalFaceDensity435Transient.x l n i 0)
    (CFMPOriginalFaceDensity435Transient.v l n i 0)
    (CFMPOriginalFaceDensity435Transient.v l n i 1) hN
  simp only [CFMPOriginalFaceDensity435Transient.lift_x l hl n i 0,
    CFMPOriginalFaceDensity435Transient.tangent_v l hl n i 0,
    CFMPOriginalFaceDensity435Transient.tangent_v l hl n i 1,
    ← CFMPOriginalFaceDensity435Transient.raw_norm l hl M n i 0] at h
  have hzero : xi l n i 0 = base l n := by simp [xi]
  rw [hzero] at h
  rw [scalar_gram_det]
  exact h

theorem internal_area_coefficient
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) :
    Real.sqrt (-(gram (pairingEntries (faceV0 l M n)
      (faceB l M n i) (faceC l M n i))).det) = areaCoefficient l M n i := by
  rw [internal_gram_cofactor l hl M hM f hf n i]
  simp only [neg_mul,neg_neg]
  rw [Real.sqrt_mul (sq_nonneg M.det),Real.sqrt_sq_eq_abs]
  rfl

theorem internal_gram_negative
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) :
    (gram (pairingEntries (faceV0 l M n) (faceB l M n i)
      (faceC l M n i))).det < 0 := by
  rw [internal_gram_cofactor l hl M hM f hf n i]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_ne_zero hM))
    (CFMPOriginalInternalNormals435Transient.raw_spacelike l hl M hM f hf n i)

-- The coefficient is now exactly the Gram coefficient used by coordinate FTC.
-- Native moment integrability is retained as an explicit hypothesis.
theorem original_internal_native_gram_moment
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) (a : Fin 3 → ℝ)
    (hint : IntegrableOn
      (fun p => lorentz (lift p)
        (basisPoint (faceV0 l M n) (faceB l M n i) (faceC l M n i) a))
      (faceImage l hl f n i)
      (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) :
    (∫ p in faceImage l hl f n i,
      lorentz (lift p)
        (basisPoint (faceV0 l M n) (faceB l M n i) (faceC l M n i) a)
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
    ∫ z in CFMPSimplexDirection435Transient.triangle 1,
      Real.sqrt (-(gram (pairingEntries (faceV0 l M n) (faceB l M n i)
        (faceC l M n i))).det) *
        moment (pairingEntries (faceV0 l M n) (faceB l M n i) (faceC l M n i)) a z /
        (Q (pairingEntries (faceV0 l M n) (faceB l M n i) (faceC l M n i)) z)^2 := by
  rw [internal_area_coefficient l hl M hM f hf n i]
  exact original_internal_native_moment l hl M hM hG f hf n i a hint

end CFMPOriginalInternalGramArea435Transient
