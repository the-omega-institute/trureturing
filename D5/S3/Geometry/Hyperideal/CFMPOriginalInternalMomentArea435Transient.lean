import D5.S3.Geometry.Hyperideal.CFMPOriginalCofactorSurface435Transient
import D5.S3.Geometry.Hyperideal.CFMPReferenceSimplexDivergence435Transient
import D5.S3.Geometry.Hyperideal.CFMPPlaneBoundaryMoment435Transient

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient CFMPNativePullbackMetric435Transient
open CFMPOriginalInternalFaceBridge435V2Transient
open CFMPActualPlaneIsometry435Transient
open CFMPPlaneMomentDivergence435Transient CFMPPlaneEdgeCofactor435Transient
open CFMPPlaneDualConormal435Transient CFMPReferenceSimplexDivergence435Transient

namespace CFMPOriginalInternalMomentArea435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

def faceV0 (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (n : Fin 20) : W :=
  base l n ᵥ* M

def faceB (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (n : Fin 20) (i : Fin 3) : W := direction l n i 0 ᵥ* M

def faceC (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (n : Fin 20) (i : Fin 3) : W := direction l n i 1 ᵥ* M

def faceImage (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (f : cutBody l → HyperbolicThreeSpace) (n : Fin 20) (i : Fin 3) :
    Set HyperbolicThreeSpace :=
  range (fun q : parameterTriangle =>
    f ⟨xi l n i q.val,xi_mem_cutBody l hl n i q.val q.property⟩)

def areaCoefficient (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (n : Fin 20) (i : Fin 3) : ℝ :=
  |M.det| * Real.sqrt (lorentz
    (CFMPOriginalInternalNormals435Transient.raw M
      (CFMPOriginalFacePairing435Transient.coefficient l n i))
    (CFMPOriginalInternalNormals435Transient.raw M
      (CFMPOriginalFacePairing435Transient.coefficient l n i)))

theorem affine_pairings (V0 b c : W) (a : Fin 3 → ℝ) (z : ℝ × ℝ) :
    radius (V0+z.1 • b+z.2 • c) = Q (pairingEntries V0 b c) z ∧
    lorentz (V0+z.1 • b+z.2 • c) (basisPoint V0 b c a) =
      moment (pairingEntries V0 b c) a z := by
  constructor <;>
    simp [radius,Q,pairingEntries,moment,basisPoint,lorentz,
      Fin.sum_univ_four,smul_eq_mul] <;> ring

theorem density_moment_scalar (C m q : ℝ) (hq : 0 < q) :
    C/(Real.sqrt q)^3*((Real.sqrt q)⁻¹*m) = C*m/q^2 := by
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hden : (Real.sqrt q)^4 = q^2 := by
    calc
      _ = ((Real.sqrt q)^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hq.le]
  calc
    _ = C*m/(Real.sqrt q)^4 := by field_simp [hs];ring
    _ = _ := by rw [hden]

-- The same original realization and the same cofactor density occur in both integrals.
-- Integrability of the native moment remains an explicit hypothesis here.
theorem original_internal_native_moment
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
      areaCoefficient l M n i *
        moment (pairingEntries (faceV0 l M n) (faceB l M n i) (faceC l M n i)) a z /
        (Q (pairingEntries (faceV0 l M n) (faceB l M n i) (faceC l M n i)) z)^2 := by
  obtain ⟨rho,P,r,D,hrho,hP,hpos,hpoint,hgeometry,hmap,hdensity,hsub⟩ :=
    CFMPOriginalCofactorSurface435Transient.original_internal_native_cofactor_surface
      l hl M hM hG f hf n i
  have hs := (hsub
    (fun p => lorentz (lift p)
      (basisPoint (faceV0 l M n) (faceB l M n i) (faceC l M n i) a)) hint).2
  change (∫ p in faceImage l hl f n i,
    lorentz (lift p)
      (basisPoint (faceV0 l M n) (faceB l M n i) (faceC l M n i) a)
    ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) = _ at hs
  rw [hs,triangle_integral]
  apply setIntegral_congr_fun (CFMPSimplexDirection435Transient.triangle_compact 1).measurableSet
  intro z hz
  have hq : pack2 z ∈ parameterTriangle := hz
  have hraw : xi l n i (pack2 z) ᵥ* M =
      faceV0 l M n+z.1 • faceB l M n i+z.2 • faceC l M n i := by
    simp only [xi,Matrix.add_vecMul,Matrix.smul_vecMul,pack2,
      Matrix.cons_val_zero,Matrix.cons_val_one,faceV0,faceB,faceC]
  have hpair := affine_pairings (faceV0 l M n) (faceB l M n i)
    (faceC l M n i) a z
  have hrad := (CFMPOriginalNativeCoordinates435Transient.original_native_coordinates
    l hl M f hf ⟨xi l n i (pack2 z),xi_mem_cutBody l hl n i (pack2 z) hq⟩).1
  have hQ : 0 < Q (pairingEntries (faceV0 l M n) (faceB l M n i)
      (faceC l M n i)) z := by
    rw [hraw,hpair.1] at hrad
    exact hrad
  rw [hdensity (pack2 z) hq,hpoint (pack2 z) hq,
    original_frame_normalized_lift l M hG f hf]
  change (areaCoefficient l M n i /
      (Real.sqrt (radius (xi l n i (pack2 z) ᵥ* M)))^3) *
    lorentz ((Real.sqrt (radius (xi l n i (pack2 z) ᵥ* M)))⁻¹ •
      (xi l n i (pack2 z) ᵥ* M))
      (basisPoint (faceV0 l M n) (faceB l M n i) (faceC l M n i) a) = _
  have hscale (s : ℝ) (U A : W) : lorentz (s • U) A = s*lorentz U A := by
    simp [lorentz,Fin.sum_univ_four,smul_eq_mul]
    ring
  rw [hscale,hraw,hpair.1,hpair.2]
  exact density_moment_scalar _ _ _ hQ

end CFMPOriginalInternalMomentArea435Transient
