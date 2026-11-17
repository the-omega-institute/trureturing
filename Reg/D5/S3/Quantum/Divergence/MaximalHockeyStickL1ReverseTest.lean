import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest

/-! Exact generic source signatures of the exposed representative suppliers.
These bridges retain source quantifiers; no four-slot validation is asserted. -/

noncomputable section
universe u
open MeasureTheory Set Filter
open scoped ComplexOrder
open _root_.D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest

namespace Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest

theorem cost_source_bridge : (type_of% (@cost_congr_ae.{u})) ↔
    ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X} {f : ℝ → ℝ}
      (hf : ConvexOn ℝ (Ioi 0) f) {p q p' q' : X → ℝ},
      p =ᵐ[μ] p' → q =ᵐ[μ] q' →
      closedPerspectiveCost hf μ p q = closedPerspectiveCost hf μ p' q' := Iff.rfl

theorem representative_source_bridge : (type_of% (@measurable_positive_L1_input.{u})) ↔
    ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X}
      (h : X →₁[μ] ℂ), (∀ᵐ x ∂μ, 0 ≤ h x) →
      ∃ (p : X → ℝ) (hp : Integrable p μ), Measurable p ∧
        (∀ᵐ x ∂μ, 0 ≤ p x) ∧
        hp.ofReal.toL1 (fun x => (p x : ℂ)) = h ∧
        p =ᵐ[μ] (fun x => (h x).re) := Iff.rfl

#print axioms cost_source_bridge
#print axioms representative_source_bridge

end Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest
