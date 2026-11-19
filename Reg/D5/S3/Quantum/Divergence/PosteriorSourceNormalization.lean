import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.PosteriorSourceNormalization
import Reg.Support.DependentFamily

/-! Source-faithful audit operands for the arbitrary-source posterior cost identity. -/

open MeasureTheory Set Filter LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open _root_.D5.S3.Quantum.Divergence.PosteriorSourceNormalization

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Divergence.PosteriorSourceNormalization

/-- The full original source data, with no finite-cost or finite-measure restriction. -/
structure SourceInputs (X : Type u) [MeasurableSpace X] where
  mu : Measure X
  p : X → ℝ
  q : X → ℝ
  hpm : Measurable p
  hqm : Measurable q
  hpn : ∀ᵐ x ∂mu, 0 ≤ p x
  hqn : ∀ᵐ x ∂mu, 0 ≤ q x

abbrev signature : Signature where
  Params := Σ X : Type u, MeasurableSpace X
  State a := @SourceInputs a.1 a.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure K
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ a s => by
    letI := a.2
    exact posteriorMeasure s.mu s.p s.q)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (a : signature.Params) (s : @SourceInputs a.1 a.2),
    ∀ (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ioi 0) f),
    @closedPerspectiveCost f hf a.1 a.2
      (@SourceInputs.mu _ a.2 s) (@SourceInputs.p _ a.2 s) (@SourceInputs.q _ a.2 s) =
      closedPerspectiveCost hf (R.readout () a s) (fun t => t.val) (fun t => 1 - t.val)

/-- The equivalence retains the complete original theorem telescope. -/
theorem source_bridge :
    (type_of% (@closedPerspectiveCost_posterior.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h a s
    letI : MeasurableSpace a.1 := a.2
    intro f hf
    exact h s.hpm s.hqm s.hpn s.hqn hf
  · intro h X mX mu p q hpm hqm hpn hqn f hf
    exact h ⟨X, mX⟩ ⟨mu, p, q, hpm, hqm, hpn, hqn⟩ f hf

#print axioms source_bridge

end Reg.D5.S3.Quantum.Divergence.PosteriorSourceNormalization
