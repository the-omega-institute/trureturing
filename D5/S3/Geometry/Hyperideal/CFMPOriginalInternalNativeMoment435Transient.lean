import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalGramArea435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalTriangleBoundary435Transient

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient
open CFMPOriginalInternalFaceBridge435V2Transient CFMPOriginalCellsIndependent435Transient
open CFMPPlaneMomentDivergence435Transient CFMPPlaneEdgeCofactor435Transient
open CFMPPlaneDualConormal435Transient CFMPOriginalInternalMomentArea435Transient
open CFMPOriginalInternalGramArea435Transient CFMPOriginalTriangleBoundary435Transient

namespace CFMPOriginalInternalNativeMoment435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

def vertexIndex (i : Fin 3) : Fin 3 → Fin 4 :=
  ![0,(i.succAbove 0).succ,(i.succAbove 1).succ]

theorem vertexIndex_injective (i : Fin 3) : Function.Injective (vertexIndex i) := by
  fin_cases i
  all_goals
    intro j k h
    fin_cases j <;> fin_cases k <;> norm_num [vertexIndex] at h ⊢

def facePoints (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (i : Fin 3) (j : Fin 3) : cutBody l :=
  ⟨vertices l n (vertexIndex i j),vertex_mem_cutBody l hl n _⟩

theorem facePoints_injective (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (i : Fin 3) : Function.Injective (facePoints l hl n i) := by
  intro j k h
  apply vertexIndex_injective i
  apply (original_cells_independent l hl n).injective
  exact congrArg Subtype.val h

theorem facePoints_frame (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (n : Fin 20) (i : Fin 3) :
    originalV0 M (facePoints l hl n i) = faceV0 l M n ∧
    originalB M (facePoints l hl n i) = faceB l M n i ∧
    originalC M (facePoints l hl n i) = faceC l M n i := by
  exact ⟨rfl,rfl,rfl⟩

-- Each original internal triangle now has actual native area and endpoint distances.
-- Integrability is explicit; no polygon assembly or diagonal cancellation is asserted.
theorem original_internal_native_boundary_moment
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace) (hfinj : Function.Injective f)
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
    2*(∫ p in faceImage l hl f n i,
      lorentz (lift p)
        (basisPoint (faceV0 l M n) (faceB l M n i) (faceC l M n i) a)
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
      ∑ e : Fin 3,
        lorentz (basisPoint (faceV0 l M n) (faceB l M n i) (faceC l M n i) a)
          (dualUnit (faceV0 l M n) (faceB l M n i) (faceC l M n i) e) *
        dist (f (edgeStart (facePoints l hl n i) e))
          (f (edgeEnd (facePoints l hl n i) e)) := by
  rw [original_internal_native_gram_moment l hl M hM hG f hf n i a hint,
    ← integral_const_mul]
  have hframe := facePoints_frame l hl M n i
  have hdet := internal_gram_negative l hl M hM f hf n i
  rw [← hframe.1,← hframe.2.1,← hframe.2.2] at hdet
  have hb := original_triangle_boundary_moment l hl M f hfinj hf
    (facePoints l hl n i) (facePoints_injective l hl n i) hdet a
  dsimp only at hb
  rw [hframe.1,hframe.2.1,hframe.2.2] at hb
  refine Eq.trans ?_ hb
  apply setIntegral_congr_fun (CFMPSimplexDirection435Transient.triangle_compact 1).measurableSet
  intro z hz
  ring

end CFMPOriginalInternalNativeMoment435Transient
