import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Probability.BirkhoffPointwise
import Reg.Support.DependentFamily

/-! The complete universe-polymorphic ergodic law observes the actual sequence of
real time averages. Only the carrier, transformation and observable parameterize
the readout; the measurable structure, probability, ergodicity and integrability
remain hypotheses of the original law. -/

namespace Reg.D5.S3.Analytic.Probability.BirkhoffPointwise

open _root_.D5.S3.Analytic.Probability.BirkhoffPointwise
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory Filter
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Σ α : Type u, Σ _ : α → α, α → ℝ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x n => birkhoffAverage ℝ p.2.1 p.2.2 n x)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α}, Ergodic T μ → ∀ {g : α → ℝ}, Integrable g μ →
      ∀ᵐ x ∂μ, Tendsto (R.readout () ⟨α, T, g⟩ x) atTop (𝓝 (∫ y, g y ∂μ))

theorem source_bridge :
    (type_of% @birkhoff_pointwise_ergodic.{u}) ↔ arena.{u}.Law actual := Iff.rfl

theorem actual_law : arena.{u}.Law actual := @birkhoff_pointwise_ergodic.{u}

end
end Reg.D5.S3.Analytic.Probability.BirkhoffPointwise
