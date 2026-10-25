import D5.S3.Geometry.Hyperideal.CFMPSimplexFullFlux435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalFaceBridge435V2Transient

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix
open CFMPSimplexDirection435Transient CFMPOriginalInternalFaceBridge435V2Transient
namespace CFMPReferenceSimplexDivergence435Transient

def pack2 (z : ℝ × ℝ) : Fin 2 → ℝ := ![z.1,z.2]

theorem triangle_integral (g : (Fin 2 → ℝ) → ℝ) :
    (∫ q in parameterTriangle, g q) = ∫ z in triangle 1, g (pack2 z) := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have heq : parameterTriangle = e ⁻¹' triangle 1 := by rfl
  have hinv (q : Fin 2 → ℝ) : pack2 (e q) = q := by
    ext i
    fin_cases i <;> rfl
  have hp := ((volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).restrict_preimage
    (triangle_compact 1).measurableSet).integral_comp e.measurableEmbedding
      (fun z => g (pack2 z))
  change (∫ q in e ⁻¹' triangle 1, g (pack2 (e q))) =
    ∫ z in triangle 1, g (pack2 z) at hp
  rw [← heq] at hp
  simpa only [hinv] using hp

end CFMPReferenceSimplexDivergence435Transient
