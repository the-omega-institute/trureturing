import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorMomentArea435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalGramArea435Transient

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient
open CFMPOriginalExteriorFaceChart435Transient
open CFMPPlaneMomentDivergence435Transient CFMPPlaneEdgeCofactor435Transient
open CFMPPlaneDualConormal435Transient CFMPOriginalExteriorMomentArea435Transient

open CFMPOriginalInternalGramArea435Transient (scalar_gram_det)

namespace CFMPOriginalExteriorGramArea435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem exterior_gram_cofactor
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) :
    (gram (pairingEntries (faceV0 l M n) (faceB l M n) (faceC l M n))).det =
      -M.det^2 * lorentz
        (CFMPOriginalExteriorNativeNormal435Transient.raw l M n)
        (CFMPOriginalExteriorNativeNormal435Transient.raw l M n) := by
  have hN := CFMPOriginalExteriorNativeNormal435Transient.raw_spacelike l hl M hM hG f hf n
  rw [CFMPOriginalExteriorDensity435Transient.raw_norm l hl M n 0] at hN
  have h := CFMPActualCoefficientDensity435Transient.actual_face_gram M hM
    (CFMPOriginalExteriorDensity435Transient.x l n 0)
    (CFMPOriginalExteriorDensity435Transient.v l n 0)
    (CFMPOriginalExteriorDensity435Transient.v l n 1) hN
  simp only [CFMPOriginalExteriorDensity435Transient.lift_x l hl n 0,
    CFMPOriginalExteriorDensity435Transient.tangent_v l hl n 0,
    CFMPOriginalExteriorDensity435Transient.tangent_v l hl n 1,
    ← CFMPOriginalExteriorDensity435Transient.raw_norm l hl M n 0] at h
  have hzero : xi l n 0 = base l n := by simp [xi]
  rw [hzero] at h
  rw [scalar_gram_det]
  exact h

theorem exterior_area_coefficient
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) :
    Real.sqrt (-(gram (pairingEntries (faceV0 l M n)
      (faceB l M n) (faceC l M n))).det) = areaCoefficient l M n := by
  rw [exterior_gram_cofactor l hl M hM hG f hf n]
  simp only [neg_mul,neg_neg]
  rw [Real.sqrt_mul (sq_nonneg M.det),Real.sqrt_sq_eq_abs]
  rfl

theorem exterior_gram_negative
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) :
    (gram (pairingEntries (faceV0 l M n) (faceB l M n)
      (faceC l M n))).det < 0 := by
  rw [exterior_gram_cofactor l hl M hM hG f hf n]
  have hn := CFMPOriginalExteriorNativeNormal435Transient.raw_spacelike l hl M hM hG f hf n
  nlinarith [mul_pos (sq_pos_of_ne_zero hM) hn]

-- The coefficient is now exactly the Gram coefficient used by coordinate FTC.
-- Native moment integrability is supplied by the actual compact triangle.
theorem original_exterior_native_gram_moment
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (a : Fin 3 → ℝ) :
    (∫ p in faceImage l hl f n,
      lorentz (lift p)
        (basisPoint (faceV0 l M n) (faceB l M n) (faceC l M n) a)
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
    ∫ z in CFMPSimplexDirection435Transient.triangle 1,
      Real.sqrt (-(gram (pairingEntries (faceV0 l M n) (faceB l M n)
        (faceC l M n))).det) *
        moment (pairingEntries (faceV0 l M n) (faceB l M n) (faceC l M n)) a z /
        (Q (pairingEntries (faceV0 l M n) (faceB l M n) (faceC l M n)) z)^2 := by
  rw [exterior_area_coefficient l hl M hM hG f hf n]
  exact original_exterior_native_moment l hl M hM hG f hf n a

end CFMPOriginalExteriorGramArea435Transient
