import D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
import Reg.Support.DependentFamily

noncomputable section
open scoped BigOperators
open _root_.D5.S3.Divergence.ClassicalDPI
open _root_.D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer

universe u v w

structure Parameters where
  State : Type u
  Observation : Type v
  Action : Type w
  finiteState : Fintype State
  finiteObservation : Fintype Observation
  finiteAction : Fintype Action
  prior : State → ℝ
  loss : State → Action → ℝ
  experiment : State → Observation → ℝ

abbrev signature : Signature where
  Params := Parameters.{u,v,w}
  State p := p.Observation → p.Action → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p d =>
    @finiteBayesCost p.State p.Observation p.Action p.finiteState
      p.finiteObservation p.finiteAction p.prior p.loss p.experiment d)
    (fun e => nomatch e)

def minimumArena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ p : Parameters.{u,v,w},
    letI := p.finiteAction
    Nonempty p.Action → ∃ d : FiniteMarkovKernel p.Observation p.Action,
      ∀ k : FiniteMarkovKernel p.Observation p.Action,
        R.readout () p d.1 ≤ R.readout () p k.1

theorem minimum_actual : minimumArena.{u,v,w}.Law actual := by
  intro p
  letI := p.finiteState
  letI := p.finiteObservation
  letI := p.finiteAction
  intro hA
  letI := hA
  exact finite_bayes_cost_minimizer p.prior p.loss p.experiment

def expansionArena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ p : Parameters.{u,v,w},
    letI := p.finiteState
    letI := p.finiteObservation
    letI := p.finiteAction
    ∀ d : p.Observation → p.Action → ℝ,
      R.readout () p d =
        ∑ a, ∑ b, d a b * ∑ i, p.prior i * p.experiment i a * p.loss i b

theorem expansion_actual : expansionArena.{u,v,w}.Law actual := by
  intro p
  letI := p.finiteState
  letI := p.finiteObservation
  letI := p.finiteAction
  exact finite_bayes_cost_expansion p.prior p.loss p.experiment

/- The complete original source laws above do not provide whole-family
variation, sensitivity, observational dependence, or current source binding.
The unfinished registration is disclosed in issue 33758. -/

end Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
