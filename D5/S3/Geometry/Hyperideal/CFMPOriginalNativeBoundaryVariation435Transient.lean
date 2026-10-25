import D5.S3.Geometry.Hyperideal.CFMPNativeMassPath435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalBoundaryFlux435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorNativeReferenceFlux435Transient
import D5.S3.Geometry.Hyperideal.CFMPGenuineLengthNeighborhood435Transient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators Topology ContDiff ENNReal Matrix.Norms.Elementwise
open Set Filter MeasureTheory
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPFrameAffineTransport435Transient CFMPActualCellMotion435Transient
open CFMPActualNativeCellMotion435Transient CFMPOriginalCellsIndependent435Transient
open CFMPOriginalFrameDensity435Transient CFMPOriginalNativeCoordinates435Transient
open CFMPAnchoredSmoothFrame435Transient
open CFMPOriginalCellKernel435Transient CFMPCompactKernelIntegral435Transient
open CFMPCompactKernelTube435Transient (delta delta_compact timeDerivative)
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace

open CFMPActualNativeMass435Transient
open D5.S3.Geometry.HyperbolicNormalizedDensity
open D5.S3.Geometry.HyperbolicTopology

open CFMPAnchoredOriginalExteriorFaceMotion435Transient
open CFMPOriginalExteriorFaceChart435Transient CFMPOriginalExteriorNativeNormal435Transient
open CFMPNativePullbackMetric435Transient CFMPNativePlaneNormal435Transient

namespace CFMPOriginalNativeBoundaryVariation435Transient

local instance : MeasurableSpace Coordinates3 := borel _
local instance : BorelSpace Coordinates3 := ⟨rfl⟩
local instance : MeasurableSpace Native3 := borel _
local instance : BorelSpace Native3 := ⟨rfl⟩

theorem original_native_mass_boundary_variation
    (l0 : Fin 6 → ℝ) (hl0 : ∀ i, 0 < l0 i)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (l : ℝ → (Fin 6 → ℝ)) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : ContDiffAt ℝ 1 l t) (hdl : HasDerivAt l dl t) (hbase : l t = l0)
    (hgen : CFMPGenuineLengthNeighborhood435Transient.genuine l0)
    (c : ℝ≥0∞)
    (hcal : (c⁻¹ • rawNativeMeasure).map coordinatesEquiv =
      ((volume : Measure (Ambient ℂ)).comap
        (Subtype.val : Coordinates3 → Ambient ℂ)).withDensity heightDensity)
    (P : ℝ → M4) (g : ∀ s, cutBody (l s) → HyperbolicThreeSpace)
    (hfamily : ∀ᶠ s in 𝓝 t,
      (∀ i j, lorentz (P s i) (P s j) = lengthGram (l s) i j) ∧
      Function.Injective (g s) ∧ IsCompact (range (g s)) ∧
      (∀ w : cutBody (l s), ∃ y : Fin 4 → ℝ,
        y = (radial (l s) w.val) ᵥ* P s ∧ lorentz y y = -1 ∧ 0 < y 3 ∧
        (g s w).coordinates.val = WithLp.toLp 2
          (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))) :
    let F : Fin 20 → parameterTriangle → HyperbolicThreeSpace := fun n q =>
      f ⟨xi l0 n q.val,xi_mem_cutBody l0 hl0 n q.val q.property⟩
    let D : M4 := (fderiv ℝ (frame M0) l0) dl
    let T : Fin 20 → (Fin 3 → ℝ) → Fin 3 → ℝ := fun n =>
      CFMPFrameAffineTransport435Transient.totalFlux M0 (D*M0⁻¹)
        (CFMPOriginalCellsIndependent435Transient.edgeMatrix l0 n)
        (deriv (fun s => CFMPOriginalCellsIndependent435Transient.edgeMatrix (l s) n) t)
        (CFMPOriginalCellsIndependent435Transient.drop
          (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices l0 n 0))
        (deriv (fun s => CFMPOriginalCellsIndependent435Transient.drop
          (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices (l s) n 0)) t)
    let curve : Fin 20 → parameterTriangle → ℝ → Fin 3 → ℝ := fun n q s =>
      nativeMap (ambient (frame M0 (l s)) (facePoint (l s) n q.val))
    let mu := (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)
    ∃ Phi : Fin 20 → HyperbolicThreeSpace → ℝ,
      (∀ n, ContinuousOn (Phi n) (range (F n)) ∧
        IntegrableOn (Phi n) (range (F n)) mu ∧
        ∀ q : parameterTriangle,
          curve n q t = nativeCoordinates (F n q) ∧
          DifferentiableAt ℝ (curve n q) t ∧
          dotProduct (deriv (curve n q) t)
            (coordinateNormal (nativeCoordinates (F n q)) (unit l0 M0 n)) /
              (nativeCoordinates (F n q) 2)^2 = Phi n (F n q)) ∧
      HasDerivAt
        (fun s => ((c⁻¹ • rawNativeMeasure) (range (g s))).toReal)
        (∑ n : Fin 20, ∫ z in range (F n), Phi n z ∂mu) t := by
  dsimp only
  obtain ⟨Phi,htrace,hflux⟩ :=
    CFMPOriginalBoundaryFlux435Transient.anchored_actual_boundary_flux
      l0 hl0 M0 hm0 hg0 f hf l dl t hdl hbase
  refine ⟨Phi,htrace,?_⟩
  have hd := CFMPNativeMassPath435Transient.original_native_mass_path_transport
    l0 hl0 M0 hm0 hg0 f hf l dl t hl hdl hbase hgen c hcal P g hfamily
  convert hd using 1
  exact hflux.symm

end CFMPOriginalNativeBoundaryVariation435Transient
