import D5.S3.Quantum.Foundation.OriginalBlindCounterfactual
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Original source reconstruction with the linear readout as a dependent observation.
Whole-family variation, sensitivity, observational dependence and source selection
are separate obligations for a four-slot registration. -/

noncomputable section
universe u v

namespace Reg.D5.S3.Quantum.Foundation.OriginalBlindCounterfactual

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.OriginalBlindCounterfactual
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type u
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  O : Type v
  [addO : AddCommGroup O]
  [moduleO : Module ℝ O]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  readout : V →ₗ[ℝ] O

attribute [instance] Inputs.add Inputs.space Inputs.finite Inputs.addO Inputs.moduleO

abbrev signature : Signature where
  Params := Inputs.{u,v}
  State P := P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.O
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ P x => P.readout x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ P : Inputs.{u,v},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ →
    ∀ z : P.V, z ≠ 0 → u z = 0 → R.readout () P z = 0 →
    ∃ (w : P.V) (e : ℝ) (f : P.V →ₗ[ℝ] ℝ),
      w ∈ base C u ∧ w ∈ interior (C : Set P.V) ∧ 0 < e ∧ proper C u f ∧
      w + e • z ∈ base C u ∧ w - e • z ∈ base C u ∧
      w + e • z ∈ interior (C : Set P.V) ∧ w - e • z ∈ interior (C : Set P.V) ∧
      w + e • z ≠ w - e • z ∧ R.readout () P (w + e • z) = R.readout () P (w - e • z) ∧
      0 < f (w + e • z) - f (w - e • z)

abbrev sourceScope : Prop := type_of% (@original_blind_direction_counterfactual.{u,v})

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law actual.{u,v} := by
  constructor
  · intro h P
    exact fun hc hu hg z hz huz hTz =>
      @h P.V P.add P.space P.finite P.O P.addO P.moduleO
        P.cone P.unit hc hu hg P.readout z hz huz hTz
  · intro h V add space finite O addO moduleO C u hc hu hg T z hz huz hTz
    exact h (@Inputs.mk V add space finite O addO moduleO C u T) hc hu hg z hz huz hTz

theorem actual_positive : arena.{u,v}.Law actual.{u,v} :=
  source_bridge.mp (@original_blind_direction_counterfactual.{u,v})

end Reg.D5.S3.Quantum.Foundation.OriginalBlindCounterfactual
