import D5.S3.Topology.OrderUnitExpFlow
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact arbitrary-carrier source reconstruction and actual-positive evidence.
The four-slot registration additionally needs variation, sensitivity, dependence,
lawful template selection and source-coordinate occurrence evidence:
https://github.com/the-omega-institute/trureturing/issues/28368. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Topology.OrderUnitExpFlow

open _root_.D5.S3.Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  E : Type u
  [normed : NormedAddCommGroup E]
  [space : NormedSpace ℝ E]
  [complete : CompleteSpace E]
  model : OrderUnitNorm.Data E
  operator : E →L[ℝ] E
  contact : ∀ β : E →L[ℝ] ℝ, (∀ c ∈ model.cone, 0 ≤ β c) →
    ∀ c ∈ model.cone, β c = 0 → β (operator c) = 0

attribute [instance] Inputs.normed Inputs.space Inputs.complete

abbrev Orbit (P : Inputs.{u}) := ℝ → P.E → P.E

abbrev sourceOrbit (P : Inputs.{u}) : Orbit P :=
  fun t c => NormedSpace.exp (t • P.operator) c

abbrev signature : Signature where
  Params := Inputs.{u}
  State := Orbit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ => Orbit
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ orbit => orbit) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ P t c, c ∈ P.model.cone →
    R.readout () P (sourceOrbit P) t c ∈ P.model.cone

abbrev sourceScope : Prop := type_of% (@OrderUnitExpFlow.zero_contact_exp.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P t c hc
    exact h P.model P.operator P.contact t c hc
  · intro h E normed space complete A H hzero t c hc
    exact h
      { E := E
        normed := normed
        space := space
        complete := complete
        model := A
        operator := H
        contact := hzero } t c hc

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@OrderUnitExpFlow.zero_contact_exp.{u})

end Reg.D5.S3.Topology.OrderUnitExpFlow
