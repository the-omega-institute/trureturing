import D5.S3.Topology.OrderUnitZeroFace
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full source reconstruction and actual-positive evidence. Whole-family
intervention, sensitivity and observational-dependence evidence are not
supplied by this partial audit. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Topology.OrderUnitZeroFace

open _root_.D5.S3.Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  E : Type u
  [normed : NormedAddCommGroup E]
  [space : NormedSpace ℝ E]
  model : OrderUnitNorm.Data E
  operator : E →ₗ[ℝ] E
  face : ∀ φ : E →L[ℝ] ℝ, (∀ x ∈ model.cone, 0 ≤ φ x) →
    ∀ x ∈ model.cone, φ x = 0 → φ (operator x) = 0
  second : operator (operator model.unit) = 0

attribute [instance] Inputs.normed Inputs.space

abbrev signature : Signature where
  Params := Inputs.{u}
  State := fun _ => Unit
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ P => P.E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun role P _ => if role then P.operator P.model.unit else 0)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ P z, R.readout true P z = R.readout false P z

abbrev sourceScope : Prop := type_of% (@OrderUnitZeroFace.unit_eq_zero.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P z
    exact h P.model P.operator P.face P.second
  · intro h E normed space A T hface hsecond
    exact h
      { E := E
        normed := normed
        space := space
        model := A
        operator := T
        face := hface
        second := hsecond } ()

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@OrderUnitZeroFace.unit_eq_zero.{u})

end Reg.D5.S3.Topology.OrderUnitZeroFace
