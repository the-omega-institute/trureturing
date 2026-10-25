import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorGramArea435Transient
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
open CFMPOriginalExteriorFaceChart435Transient CFMPOriginalCellsIndependent435Transient
open CFMPPlaneMomentDivergence435Transient CFMPPlaneEdgeCofactor435Transient
open CFMPPlaneDualConormal435Transient CFMPOriginalExteriorMomentArea435Transient
open CFMPOriginalExteriorGramArea435Transient CFMPOriginalTriangleBoundary435Transient

namespace CFMPOriginalExteriorNativeMoment435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

def facePoints (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (j : Fin 3) : cutBody l :=
  ⟨vertices l n j.succ,CFMPOriginalInternalFaceBridge435V2Transient.vertex_mem_cutBody l hl n _⟩

theorem facePoints_injective (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) : Function.Injective (facePoints l hl n) := by
  intro j k h
  apply Fin.succ_injective
  apply (original_cells_independent l hl n).injective
  exact congrArg Subtype.val h

theorem facePoints_frame (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (n : Fin 20) :
    originalV0 M (facePoints l hl n) = faceV0 l M n ∧
    originalB M (facePoints l hl n) = faceB l M n ∧
    originalC M (facePoints l hl n) = faceC l M n := by
  exact ⟨rfl,rfl,rfl⟩

-- Each original exterior triangle uses actual native area and endpoint distances.
-- The sum over physical polygon faces and diagonal cancellation are separate.
theorem original_exterior_native_boundary_moment
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (a : Fin 3 → ℝ) :
    2*(∫ p in faceImage l hl f n,
      lorentz (lift p)
        (basisPoint (faceV0 l M n) (faceB l M n) (faceC l M n) a)
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
      ∑ e : Fin 3,
        lorentz (basisPoint (faceV0 l M n) (faceB l M n) (faceC l M n) a)
          (dualUnit (faceV0 l M n) (faceB l M n) (faceC l M n) e) *
        dist (f (edgeStart (facePoints l hl n) e))
          (f (edgeEnd (facePoints l hl n) e)) := by
  rw [original_exterior_native_gram_moment l hl M hM hG f hf n a,
    ← integral_const_mul]
  have hframe := facePoints_frame l hl M n
  have hdet := exterior_gram_negative l hl M hM hG f hf n
  rw [← hframe.1,← hframe.2.1,← hframe.2.2] at hdet
  have hfinj := CFMPOriginalInternalMomentIntegrable435Transient.original_realization_injective
    l hl M hM f hf
  have hb := original_triangle_boundary_moment l hl M f hfinj hf
    (facePoints l hl n) (facePoints_injective l hl n) hdet a
  dsimp only at hb
  rw [hframe.1,hframe.2.1,hframe.2.2] at hb
  refine Eq.trans ?_ hb
  apply setIntegral_congr_fun (CFMPSimplexDirection435Transient.triangle_compact 1).measurableSet
  intro z hz
  ring

end CFMPOriginalExteriorNativeMoment435Transient

#print axioms CFMPOriginalExteriorNativeMoment435Transient.original_exterior_native_boundary_moment
run_cmd do
  let name := ``CFMPOriginalExteriorNativeMoment435Transient.original_exterior_native_boundary_moment
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP223 target absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP223 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP223 CHECKED CFMPOriginalExteriorNativeMoment435Transient.original_exterior_native_boundary_moment axioms={axioms}"
