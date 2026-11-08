import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace Reg.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => B x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ hRH : RiemannHypothesis,
    (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ x : ℝ in atTop,
      1 < Chebyshev.theta x ∧ |D x * V.readout () () x + 2| < firstLiMass + epsilon) ∧
    (∀ epsilon : ℝ, 0 < epsilon → ∀ Y : ℝ,
      ∃ x : ℝ, max 2 Y ≤ x ∧ 1 < Chebyshev.theta x ∧
        |D x * V.readout () () x + 2 + firstLiMass| < epsilon) ∧
    Filter.liminf (fun x : ℝ => D x * V.readout () () x) atTop = -2 - firstLiMass

private theorem actual_law : arena.Law actual := by
  exact @actual_B_lower_endpoint

private theorem source_bridge :
    (type_of% (@actual_B_lower_endpoint)) ↔ arena.Law actual := Iff.rfl

/- This source law and its equivalence bridge do not constitute a completed
   four-slot audit. No Contract.Registration is declared here. The missing evidence
   is a lawful enrolled-template readout, whole-family variation and sensitivity,
   actual observational dependence, sourceSelection and current binding evidence.
   Refuting this RH-conditional law for a rejected family entails RH: when RH is
   false the law holds for every family. An anchor equality would change the
   source law and is therefore not added. -/

end Reg.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
