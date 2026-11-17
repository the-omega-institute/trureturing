import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Probability.KingmanEstimates
import Reg.Support.DependentFamily

/-! Complete source reconstruction and actual laws for the dependent observation families.
Whole-family variation, sensitivity, observational dependence and exact source binding
remain unfinished: https://github.com/the-omega-institute/trureturing/issues/27172. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Probability.KingmanEstimates
open _root_.D5.S3.Analytic.Probability.BirkhoffPointwise
open MeasureTheory Filter
open scoped Topology BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Analytic.Probability.KingmanEstimates.Greedy

structure Params where
  F : ℕ → ℕ → ℝ
  B : ℕ → Prop
  decB : DecidablePred B
  c : ℝ
  N : ℕ

abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ × ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p M => by
    letI := p.decB
    exact (p.F 0 M, M * p.c + (∑ k ∈ Finset.range M, if p.B k then p.F k 1 else 0) +
      (∑ k ∈ Finset.range M, if M ≤ k + p.N then p.F k 1 else 0)))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (F : ℕ → ℕ → ℝ), (∀ k n, 0 ≤ F k n) → (∀ k, F k 0 = 0) →
    (∀ k m n, F k (m + n) ≤ F k m + F (k + m) n) →
    ∀ (B : ℕ → Prop) (dB : DecidablePred B) (c : ℝ), 0 ≤ c → ∀ N : ℕ,
    (∀ k, ¬ B k → ∃ n, 1 ≤ n ∧ n ≤ N ∧ F k n ≤ n * c) →
    ∀ M : ℕ, (R.readout () ⟨F, B, dB, c, N⟩ M).1 ≤
      (R.readout () ⟨F, B, dB, c, N⟩ M).2

theorem source_bridge : (type_of% @greedy_block_bound) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := source_bridge.mp @greedy_block_bound

end Reg.D5.S3.Analytic.Probability.KingmanEstimates.Greedy

namespace Reg.D5.S3.Analytic.Probability.KingmanEstimates.StationaryTail

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
  realize signature (fun _ p x n => p.2.2 ((p.2.1^[n]) x) / (n : ℝ))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α}, MeasurePreserving T μ μ → ∀ {φ : α → ℝ},
    Measurable φ → Integrable φ μ → (∀ x, 0 ≤ φ x) →
    ∀ᵐ x ∂μ, Tendsto (R.readout () ⟨α, T, φ⟩ x) atTop (nhds 0)

theorem source_bridge :
    (type_of% @ae_tendsto_comp_iterate_div_nat.{u}) ↔ arena.{u}.Law actual := Iff.rfl

theorem actual_law : arena.{u}.Law actual := source_bridge.mp @ae_tendsto_comp_iterate_div_nat.{u}

end Reg.D5.S3.Analytic.Probability.KingmanEstimates.StationaryTail

namespace Reg.D5.S3.Analytic.Probability.KingmanEstimates.WeakMaximal

structure Params where
  α : Type u
  m : MeasurableSpace α
  T : α → α
  φ : α → ℝ
  c : ℝ

abbrev signature : Signature where
  Params := Params.{u}
  State p := p.α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => x ∈ @DickSet p.α p.m p.T p.φ p.c)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [m : MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α}, MeasurePreserving T μ μ → ∀ {φ : α → ℝ},
    Measurable φ → Integrable φ μ → (∀ x, 0 ≤ φ x) → ∀ {c : ℝ}, 0 < c →
    μ {x | R.readout () ⟨α, m, T, φ, c⟩ x} ≤ ENNReal.ofReal ((∫ x, φ x ∂μ) / c)

theorem source_bridge :
    (type_of% @measure_kingmanDick_le.{u}) ↔ arena.{u}.Law actual := Iff.rfl

theorem actual_law : arena.{u}.Law actual := source_bridge.mp @measure_kingmanDick_le.{u}

end Reg.D5.S3.Analytic.Probability.KingmanEstimates.WeakMaximal

end
