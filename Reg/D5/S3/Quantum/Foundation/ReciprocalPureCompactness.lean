import D5.S3.Quantum.Foundation.ReciprocalPureCompactness
import Reg.D5.S3.Quantum.Foundation.ReciprocalEndpointExposure
noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.ReciprocalPureCompactness
open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.ReciprocalPureCompactness
open Reg.D5.S3.Quantum.Foundation.ReciprocalEndpointExposure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev pureCompactSignature : Signature where
  Params := Inputs.{v}
  State P := pure P.cone P.unit × pure P.cone P.unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def pureCompactActual : Realization pureCompactSignature.{v} :=
  realize pureCompactSignature
    (fun _ P z => comparison P.cone P.unit z.1 z.2) (fun a => nomatch a)

abbrev pureCompactArena : Arena where
  signature := pureCompactSignature.{v}
  Law O := ∀ P : Inputs.{v}, IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    (∀ p q : pure P.cone P.unit, O.readout () P (p,q) = O.readout () P (q,p)) →
    IsCompact (pure P.cone P.unit)

abbrev pureCompactSource : Prop := type_of% (@reciprocal_pure_compact.{v})

theorem pure_compact_source_bridge : pureCompactSource.{v} ↔
    pureCompactArena.{v}.Law pureCompactActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u hc hs hg hPR
    exact h (@Inputs.mk V add space finite C u) hc hs hg hPR

theorem pure_compact_actual_positive : pureCompactArena.{v}.Law pureCompactActual.{v} :=
  pure_compact_source_bridge.mp (@reciprocal_pure_compact.{v})

end Reg.D5.S3.Quantum.Foundation.ReciprocalPureCompactness
