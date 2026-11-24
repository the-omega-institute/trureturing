import D5.S3.Estimation.DecisionRisk.BoundedRiskSimulatorTransport
import Reg.Support.DependentFamily

noncomputable section
open scoped BigOperators
open _root_.D5.S3.Divergence.ClassicalDPI
open _root_.D5.S3.Estimation.DecisionRisk.BoundedRiskSimulatorTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Estimation.DecisionRisk.BoundedRiskSimulatorTransport

universe u v w

structure StochasticParameters where
  Input : Type u
  Middle : Type v
  Output : Type w
  finiteMiddle : Fintype Middle
  finiteOutput : Fintype Output

abbrev stochasticSignature : Signature where
  Params := StochasticParameters.{u,v,w}
  State p := (p.Input → p.Middle → ℝ) × (p.Middle → p.Output → ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Input → p.Output → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def stochasticActual : Realization stochasticSignature :=
  realize stochasticSignature (fun _ p s i o =>
    @channelOutput p.Middle p.Output p.finiteMiddle s.2 (s.1 i) o)
    (fun e => nomatch e)

def stochasticArena : Arena where
  signature := stochasticSignature.{u,v,w}
  Law R := ∀ p : StochasticParameters.{u,v,w},
    letI := p.finiteMiddle
    letI := p.finiteOutput
    ∀ first second, IsRowStochastic first → IsRowStochastic second →
      IsRowStochastic (R.readout () p (first, second))

theorem stochastic_actual : stochasticArena.{u,v,w}.Law stochasticActual := by
  intro p
  letI := p.finiteMiddle
  letI := p.finiteOutput
  intro first second hf hs
  exact row_stochastic_channel_comp first second hf hs

structure AssociativeParameters where
  Input : Type u
  Middle : Type v
  Output : Type w
  finiteInput : Fintype Input
  finiteMiddle : Fintype Middle

abbrev associativeSignature : Signature where
  Params := AssociativeParameters.{u,v,w}
  State p := (p.Input → p.Middle → ℝ) ×
    (p.Middle → p.Output → ℝ) × (p.Input → ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Output → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def associativeActual : Realization associativeSignature :=
  realize associativeSignature (fun _ p s =>
    @channelOutput p.Input p.Output p.finiteInput
      (fun i o => @channelOutput p.Middle p.Output p.finiteMiddle s.2.1 (s.1 i) o)
      s.2.2) (fun e => nomatch e)

def associativeArena : Arena where
  signature := associativeSignature.{u,v,w}
  Law R := ∀ p : AssociativeParameters.{u,v,w},
    letI := p.finiteInput
    letI := p.finiteMiddle
    ∀ first second mass,
      R.readout () p (first, second, mass) =
        channelOutput second (channelOutput first mass)

theorem associative_actual : associativeArena.{u,v,w}.Law associativeActual := by
  intro p
  letI := p.finiteInput
  letI := p.finiteMiddle
  exact channel_output_comp

/- The two original source laws require whole-family variation, sensitivity,
observational dependence and compiler source binding before registration is
complete. Their unfinished audits are disclosed in issue 33758. -/

end Reg.D5.S3.Estimation.DecisionRisk.BoundedRiskSimulatorTransport
