/- GID: D5/S3/Weil/ZetaBridge/PositivityChartCollapse
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/PositivityChartCollapse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite feature charts of one positive spectral measure have positive Gram kernels. -/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Function.L2Space

/- Library-search audit trail (2026-08-29):
   * D5 search found no existing theorem for positivity of the integral feature kernel.
   * Pinned Mathlib supplies `Matrix.posSemidef_gram` and
     `Matrix.PosSemidef.transpose`; both are applied below.
   * `MeasureTheory.L2.inner_def` and `RCLike.inner_apply` supply the local bridge
     from the abstract Gram matrix to the source's displayed integral kernel.
   * No feature, kernel, measure, or positivity primitive is redeclared. -/

namespace D5.S3.Weil.ZetaBridge.PositivityChartCollapse

open MeasureTheory
open scoped ComplexConjugate ComplexOrder

/-- Every finite family of square-integrable features of one positive measure induces a
positive semidefinite integral Gram kernel. -/
theorem positivity_chart_collapse
    {Ω X : Type*} [MeasurableSpace Ω] [Finite X]
    (ν : Measure Ω) (Φ : X → Ω →₂[ν] ℂ) :
    Matrix.PosSemidef
      ((fun x y => ∫ γ, Φ x γ * conj (Φ y γ) ∂ν) : Matrix X X ℂ) := by
  have hKernel :
      ((fun x y => ∫ γ, Φ x γ * conj (Φ y γ) ∂ν) : Matrix X X ℂ) =
        Matrix.transpose (Matrix.gram ℂ Φ) := by
    ext x y
    rw [Matrix.transpose_apply, Matrix.gram_apply, L2.inner_def]
    simp only [RCLike.inner_apply]
  rw [hKernel]
  exact (Matrix.posSemidef_gram ℂ Φ).transpose

#print axioms positivity_chart_collapse

end D5.S3.Weil.ZetaBridge.PositivityChartCollapse
