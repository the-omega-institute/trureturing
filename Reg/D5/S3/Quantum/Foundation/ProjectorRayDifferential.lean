import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Foundation.ProjectorRayDifferential

/-!
Full-telescope source reconstruction for the local ray-distance speed theorem.
The parameter family retains the original amplitude carrier and both instances;
the state retains the original base amplitude and velocity. The law retains
the actual curve, derivative and neighbourhood unit-norm hypotheses.

This is source-binding preparation, not a validated Contract.Registration.
Whole-family intervention, sensitivity, actual observational dependence and
compiler occurrence/coordinate evidence remain required. A constant readout or
a signature that discards the amplitude carrier cannot replace these operands.
The unfinished binding is tracked at
https://github.com/the-omega-institute/trureturing/issues/28177.
-/

noncomputable section
open Filter
open scoped Topology
universe u

namespace Reg.D5.S3.Quantum.Foundation.ProjectorRayDifferential

open _root_.D5.S3.Quantum.Foundation.ProjectorRayDifferential
open _root_.D5.S3.QuantumBounds.FubiniStudyRecordTime (fsAngle)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Parameters where
  E : Type u
  group : NormedAddCommGroup E
  space : letI := group; InnerProductSpace ℂ E

attribute [instance] Parameters.group Parameters.space

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.E × p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s =>
    Real.sqrt (‖s.2‖ ^ 2 - ‖inner ℂ s.1 s.2‖ ^ 2))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : Parameters.{u}) (f : ℝ → p.E) (ψ v : p.E),
    ‖ψ‖ = 1 → f 0 = ψ → HasDerivAt f v 0 →
    (∀ᶠ t in 𝓝 (0 : ℝ), ‖f t‖ = 1) →
    Tendsto (fun t : ℝ => fsAngle ψ (f t) / |t|) (𝓝[≠] 0)
      (𝓝 (R.readout () p (ψ, v)))

theorem source_bridge : (type_of% (@fs_angle_speed.{u})) ↔
    arena.{u}.Law actual := by
  constructor
  · intro h p f ψ v hψ h₀ hf hunit
    exact h hψ h₀ hf hunit
  · intro h E group space f ψ v hψ h₀ hf hunit
    exact h ⟨E, group, space⟩ f ψ v hψ h₀ hf hunit

theorem actual_positive : arena.{u}.Law actual :=
  source_bridge.mp (@fs_angle_speed.{u})

end Reg.D5.S3.Quantum.Foundation.ProjectorRayDifferential
