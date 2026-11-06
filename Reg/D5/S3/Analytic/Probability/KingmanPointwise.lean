import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Probability.KingmanPointwise
import Reg.Support.DependentFamily

/-! Complete source reconstruction and actual laws for the dependent observation families.
Whole-family variation, sensitivity, observational dependence and exact source binding
remain unfinished: https://github.com/the-omega-institute/trureturing/issues/27172. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Probability.KingmanEstimates
open _root_.D5.S3.Analytic.Probability.KingmanPointwise
open _root_.D5.S3.Analytic.Probability.BirkhoffPointwise
open MeasureTheory Filter
open scoped Topology BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Analytic.Probability.KingmanPointwise

abbrev signature : Signature where
  Params := Σ α : Type u, Σ _ : α → α, ℕ → α → ℝ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x n => p.2.2 n x / (n : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {T : α → α}, MeasurePreserving T μ μ → ∀ X : ℕ → α → ℝ,
    (∀ n, Integrable (X n) μ) → (∀ n, ∀ᵐ x ∂μ, 0 ≤ X n x) →
    (∀ m n, ∀ᵐ x ∂μ, X (m + n) x ≤ X m x + X n ((T^[m]) x)) →
    ∃ g : α → ℝ, Integrable g μ ∧ (∀ᵐ x ∂μ, g (T x) = g x) ∧
      ∀ᵐ x ∂μ, Tendsto (R.readout () ⟨α, T, X⟩ x) atTop (nhds (g x))

theorem source_bridge :
    (type_of% @kingman_subadditive.{u}) ↔ arena.{u}.Law actual := Iff.rfl

theorem actual_law : arena.{u}.Law actual := source_bridge.mp @kingman_subadditive.{u}

end Reg.D5.S3.Analytic.Probability.KingmanPointwise

end
