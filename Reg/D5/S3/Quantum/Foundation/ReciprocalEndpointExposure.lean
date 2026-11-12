import D5.S3.Quantum.Foundation.ReciprocalEndpointExposure
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The exact original endpoint telescope and actual source bridge.
States are all original pure points, with no finite replacement. Whole-family
sensitivity, observational dependence and source selection are not supplied. -/

noncomputable section
universe v
namespace Reg.D5.S3.Quantum.Foundation.ReciprocalEndpointExposure

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.ReciprocalEndpointExposure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := pure P.cone P.unit
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def outcome (P : Inputs.{v}) (p : pure P.cone P.unit) : Prop :=
  ∃ h : P.V →ₗ[ℝ] ℝ, proper P.cone P.unit h ∧
    {y | y ∈ base P.cone P.unit ∧ h y = 0} = {(p : P.V)} ∧
    confirms P.cone P.unit p (P.unit - h) ∧
    {y | y ∈ base P.cone P.unit ∧ (P.unit - h) y = 1} = {(p : P.V)} ∧
    IsExposed ℝ (base P.cone P.unit) {(p : P.V)}

def actual : Realization signature.{v} :=
  realize signature (fun _ P p => outcome P p) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    ∀ p : pure P.cone P.unit,
      (∀ x : pure P.cone P.unit,
        comparison P.cone P.unit p x ≤ comparison P.cone P.unit x p) →
      O.readout 0 P p

abbrev source : Prop := type_of% (@reciprocal_endpoint_exposure.{v})

theorem source_bridge : source.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u hc hs hg p hrec
    exact h (@Inputs.mk V add space finite C u) hc hs hg p hrec

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@reciprocal_endpoint_exposure.{v})

abbrev pending := Registration arena.{v} source.{v}

#print axioms source_bridge
#print axioms actual_positive

end Reg.D5.S3.Quantum.Foundation.ReciprocalEndpointExposure
