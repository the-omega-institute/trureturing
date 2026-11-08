import D5.S3.Topology.OrderNormSupport
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact source reconstruction and actual-positive evidence for positive norm support. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Topology.OrderNormSupport

open _root_.D5.S3.Topology.OrderUnitNorm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev supportSourceScope.{u} := type_of% (@Data.positive_norm_support.{u})

structure SupportState.{u} (p : Inputs.{u}) where
  a : p.E
  nonzero : letI := p.normed; a ≠ 0

abbrev supportClaim.{u} (p : Inputs.{u}) (z : SupportState p) : Prop :=
  letI := p.normed
  letI := p.space
  ∃ β : p.E →ₗ[ℝ] ℝ, (∀ x ∈ p.data.cone, 0 ≤ β x) ∧ β p.data.unit = 1 ∧
    (∀ x, |β x| ≤ p.data.orderNorm x) ∧ |β z.a| = p.data.orderNorm z.a

abbrev supportSignature.{u} : Signature where
  Params := Inputs.{u}
  State := SupportState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def supportActual.{u} : Realization supportSignature.{u} :=
  realize supportSignature (fun _ p z => supportClaim p z) (fun e => nomatch e)

abbrev supportArena.{u} : Arena where
  signature := supportSignature.{u}
  Law R := ∀ p z, R.readout () p z

theorem support_source_bridge.{u} : supportSourceScope.{u} ↔
    supportArena.{u}.Law supportActual.{u} := by
  constructor
  · intro h p z
    letI := p.normed
    letI := p.space
    exact h p.data z.a z.nonzero
  · intro h E normed space A a ha
    exact h ⟨E, normed, space, A⟩ ⟨a, ha⟩

theorem support_actual_positive.{u} : supportArena.{u}.Law supportActual.{u} :=
  support_source_bridge.mp (@Data.positive_norm_support.{u})

end Reg.D5.S3.Topology.OrderNormSupport
