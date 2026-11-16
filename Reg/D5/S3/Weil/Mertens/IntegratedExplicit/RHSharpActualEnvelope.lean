import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

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
  realize signature (fun _ _ x => G x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ hRH : RiemannHypothesis,
    (∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ y : ℝ in atTop, |V.readout () () y| < firstLiMass + epsilon) ∧
    (∀ epsilon : ℝ, 0 < epsilon → ∀ Y : ℝ,
      ∃ n : ℕ, Y ≤ (n : ℝ) ∧ |V.readout () () (n : ℝ) - firstLiMass| < epsilon)

private theorem actual_law : arena.Law actual := by
  exact @actual_G_control

private theorem source_bridge :
    (type_of% (@actual_G_control)) ↔ arena.Law actual := Iff.rfl

/- A Contract.Registration requires a lawful enrolled-template readout,
   whole-family variation, sensitivity, observational dependence, sourceSelection,
   and current binding evidence. In particular, refuting the entire conditional
   law for a rejected family entails RH: without RH this universal implication
   holds for every family. No extra anchor equality is added to the source law. -/

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
