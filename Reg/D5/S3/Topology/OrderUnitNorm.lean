import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.OrderUnitNorm

/-!
# Original order-unit norm source binding

The norm-core family retains every original real normed vector space and its
closed salient cone and interior unit. Its state and output are the entire
candidate real-valued norm function, with identity readout. This binds the
actual source norm without changing the cone or assuming a norm axiom.

The interface source scope retains the complete original theorem, including
its original operator and all real times. Source applications and a source
bridge are partial evidence. Whole-family variation, sensitivity,
observational dependence, and raw source-coordinate reconstruction and
occurrence ties are required for a four-slot registration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Topology.OrderUnitNorm

open _root_.D5.S3.Topology.OrderUnitNorm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev coreSourceScope.{u} := type_of% (@Data.norm_core.{u})

abbrev interfaceSourceScope.{u} :=
  type_of% (@Data.original_order_unit_norm_interface.{u})

structure Inputs.{u} where
  E : Type u
  normed : NormedAddCommGroup E
  space : @NormedSpace ℝ E _ normed
  data : @Data E normed space

abbrev candidate.{u} (P : Inputs.{u}) := P.E → ℝ

abbrev signature.{u} : Signature where
  Params := Inputs.{u}
  State := candidate
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ => candidate
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u} : Realization signature.{u} :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)

abbrev coreLaw.{u} (P : Inputs.{u}) (f : candidate P) : Prop :=
  letI := P.normed
  letI := P.space
  @NormedSpace.Core ℝ P.E _ inferInstance inferInstance ⟨f⟩

abbrev arena.{u} : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u}, coreLaw P (R.readout () P P.data.orderNorm)

theorem core_source_bridge.{u} : coreSourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact h P.data
  · intro h E normed space A
    exact h ⟨E, normed, space, A⟩

theorem core_actual_positive.{u} : arena.{u}.Law actual.{u} :=
  core_source_bridge.mp (@Data.norm_core.{u})

theorem interface_source_application.{u} : interfaceSourceScope.{u} :=
  @Data.original_order_unit_norm_interface.{u}

#print axioms core_source_bridge
#print axioms core_actual_positive
#print axioms interface_source_application

end Reg.D5.S3.Topology.OrderUnitNorm
