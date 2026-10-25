import CFMPOriginalTraceSchlafli240Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalNativeBoundaryVariation435Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Matrix BigOperators Topology ContDiff ENNReal Matrix.Norms.Elementwise
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicTopology D5.S3.Geometry.HyperbolicNormalizedDensity
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPAnchoredSmoothFrame435Transient (J)
open CFMPActualNativeMass435Transient
open CFMPOriginalTraceSchlafli240Transient CFMPOriginalPhysicalEdge237Transient

namespace CFMPOriginalCalibratedSchlafli241Transient

private local instance : MeasurableSpace Coordinates3 := borel _
private local instance : BorelSpace Coordinates3 := ⟨rfl⟩
private local instance : MeasurableSpace Native3 := borel _
private local instance : BorelSpace Native3 := ⟨rfl⟩

theorem original_calibrated_schlafli
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
    HasDerivAt
      (fun s => ((c⁻¹ • rawNativeMeasure) (range (g s))).toReal)
      (-(1/2 : ℝ) * (∑ q : Fin 6, l0 q * deriv (fun s => sourceAngle (l s) q) t)) t := by
  obtain ⟨Phi,htrace,hd⟩ :=
    CFMPOriginalNativeBoundaryVariation435Transient.original_native_mass_boundary_variation
      l0 hl0 M0 hm0 hg0 f hf l dl t hl hdl hbase hgen c hcal P g hfamily
  have hc : ∀ q, -1 < sourceCosine l0 q ∧ sourceCosine l0 q < 1 := hgen.2
  have hflux := anchored_trace_length_angle_sum
    l0 hl0 M0 hm0 hg0 f hf l dl t hdl hbase hc Phi
    (fun n => (htrace n).2.1) (fun n q => ((htrace n).2.2 q).2.2)
  dsimp only [CFMPOriginalExteriorMomentArea435Transient.faceImage] at hflux
  rw [hflux] at hd
  exact hd

end CFMPOriginalCalibratedSchlafli241Transient

run_cmd do
  let name := ``CFMPOriginalCalibratedSchlafli241Transient.original_calibrated_schlafli
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP241 original calibrated Schlaefli absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP241 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP241 CHECKED {name} axioms={axioms}"
