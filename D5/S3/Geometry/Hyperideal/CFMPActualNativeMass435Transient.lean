import D5.S3.Geometry.Hyperideal.CFMPActualCellChangeVariables435Transient
import D5.S3.Geometry.Hyperideal.CFMPNativeMeasureUnsigned435Transient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators ENNReal Matrix Topology Matrix.Norms.Elementwise
open Set Filter MeasureTheory
open CFMPFrameMotion435Transient (M4)
open CFMPOriginalFrameDensity435Transient (originalDensity)
open CFMPCompactKernelTube435Transient (delta)
open CFMPActualCellMotion435Transient (cellPoint)
open CFMPOriginalCellsIndependent435Transient (edgeMatrix)
open CFMPActualGramJacobian435Transient (lift3)
open CFMPTwentyCellIntegralAssembly435Transient (K)
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicNormalizedDensity
open D5.S3.Geometry.HyperbolicTopology

namespace CFMPActualNativeMass435Transient

local instance : MeasurableSpace Coordinates3 := borel _
local instance : BorelSpace Coordinates3 := ⟨rfl⟩
local instance : MeasurableSpace Native3 := borel _
local instance : BorelSpace Native3 := ⟨rfl⟩

def referenceMass (l : Fin 6 → ℝ) : ℝ :=
  ∑ n : Fin 20, ∫ u in delta,
    |(edgeMatrix l n).det| * originalDensity l (cellPoint l n u)

theorem original_native_mass_eq_reference (c : ℝ≥0∞)
    (hcal : (c⁻¹ • rawNativeMeasure).map coordinatesEquiv =
      ((volume : Measure (Ambient ℂ)).comap
        (Subtype.val : Coordinates3 → Ambient ℂ)).withDensity heightDensity)
    (M : M4) (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace) (hfi : Function.Injective f)
    (hcompact : IsCompact (range f))
    (hsource : ∀ v : cutBody l, ∃ y : Fin 4 → ℝ,
      y = (radial l v.val) ᵥ* M ∧ lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)),1/(y 3-y 2))) :
    ((c⁻¹ • rawNativeMeasure) (range f)).toReal = referenceMass l := by
  have hvol := CFMPNativeMeasureUnsigned435Transient.native_volume_unsigned
    c hcal M l hl hg f hfi hcompact hsource
  have heq : (c⁻¹ • rawNativeMeasure) (range f) =
      ENNReal.ofReal (∫ z in K l, originalDensity l z) := by
    rw [hvol,CFMPNativeTwentyCellVolume435Transient.chartDomain_eq_projected_body]
    exact CFMPNativeTwentyCellVolume435Transient.density_lintegral_eq_ofReal_integral l hl
  have hn : 0 ≤ ∫ z in K l, originalDensity l z :=
    integral_nonneg (fun z => CFMPNativeTwentyCellVolume435Transient.density_nonnegative l z)
  rw [heq,ENNReal.toReal_ofReal hn]
  exact CFMPActualCellChangeVariables435Transient.actual_body_reference_integral l hl

-- A scalar equality on a neighborhood transfers the derivative without differentiating a
-- choice of native realizations. A physical boundary flux requires its separate geometric bridge.
theorem scalar_native_mass_transfer (l : ℝ → Fin 6 → ℝ) (t d : ℝ)
    (mass : ℝ → ℝ)
    (heq : mass =ᶠ[𝓝 t] (fun s => referenceMass (l s)))
    (hd : HasDerivAt (fun s => referenceMass (l s)) d t) :
    HasDerivAt mass d t := hd.congr_of_eventuallyEq heq

end CFMPActualNativeMass435Transient
