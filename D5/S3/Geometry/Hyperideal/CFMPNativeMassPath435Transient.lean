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

namespace CFMPNativeMassPath435Transient
local instance : MeasurableSpace Coordinates3 := borel _
local instance : BorelSpace Coordinates3 := ⟨rfl⟩
local instance : MeasurableSpace Native3 := borel _
local instance : BorelSpace Native3 := ⟨rfl⟩

theorem original_native_mass_path_transport
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
    let D : M4 := (fderiv ℝ (frame M0) l0) dl
    let Tn : Fin 20 → (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun n =>
      totalFlux M0 (D*M0⁻¹) (edgeMatrix l0 n)
        (deriv (fun s => edgeMatrix (l s) n) t) (drop (vertices l0 n 0))
        (deriv (fun s => drop (vertices (l s) n 0)) t)
    HasDerivAt
      (fun s => ((c⁻¹ • rawNativeMeasure) (range (g s))).toReal)
      (∑ n : Fin 20, ∫ u in delta, divergence (Tn n) u) t := by
  have hgen0 : CFMPGenuineLengthNeighborhood435Transient.genuine (l t) := by
    simpa only [hbase] using hgen
  have hnear := CFMPGenuineLengthNeighborhood435Transient.path_eventually_genuine
    l t hl.continuousAt hgen0
  have heq : (fun s => ((c⁻¹ • rawNativeMeasure) (range (g s))).toReal)
      =ᶠ[𝓝 t] (fun s => referenceMass (l s)) := by
    filter_upwards [hnear,hfamily] with s hs hfs
    exact original_native_mass_eq_reference c hcal (P s) (l s) hs.1
      hfs.1 (g s) hfs.2.1 hfs.2.2.1 hfs.2.2.2
  have hd := CFMPOriginalCellIntegral435Transient.original_cell_integral_transport
    l0 hl0 M0 hm0 hg0 f hf l dl t hl hdl hbase
  exact hd.congr_of_eventuallyEq heq

end CFMPNativeMassPath435Transient
