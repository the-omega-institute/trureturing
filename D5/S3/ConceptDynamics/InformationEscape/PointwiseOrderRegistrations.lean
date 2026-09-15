/- GID: D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positive_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positiveRealization
   digest: Strict and weak substitution bounds retain their source statements in one shared catalog. -/

import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S1.Words.Powers.GoldenDesubstitution
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations

open PointwiseRegistrationTemplates LeanInformationAudit
open D5.S1.Words.Powers D5.S0.Tower.GoldenGapWord

def objectArena : Arena := Arena.ofFintype Bool
def strictArena := pointwiseOrderArena objectArena Nat true
def weakArena := pointwiseOrderArena objectArena Nat false
theorem strict_slotSensitive : FiniteSlotSensitivity strictArena :=
  pointwiseOrder_sensitivity _ true false 0 1 (by decide)
theorem weak_slotSensitive : FiniteSlotSensitivity weakArena :=
  pointwiseOrder_sensitivity _ false false 0 1 (by decide)

def positiveRealization := pointwiseOrderRealization (fun _ : Bool => 0) (fun b => (subst b).length)
theorem positive_bridge : LegacyPrimitiveRealization strictArena
    (∀ b : Bool, 0 < (subst b).length) positiveRealization := pointwiseOrderLegacy _ true _ _
theorem positive_lawSensitive : strictArena.Law positiveRealization ∧
    ¬ strictArena.Law (pointwiseOrderRealization (fun _ : Bool => 0) (fun _ => 0)) :=
  ⟨positive_bridge.equivalence.mp substLength_pos, fun h => Nat.lt_irrefl 0 (h false)⟩
register_information_theorem substLength_pos in strictArena
  object_arena objectArena catalog substitutionBounds
  primitives positiveRealization.toPrimitiveBundle realization positive_bridge
  variation positive_lawSensitive sensitivity strict_slotSensitive
example : substLength_pos.«D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds».__information_unit.Statement =
    (∀ b : Bool, 0 < (subst b).length) := rfl
#print axioms positive_bridge
#print axioms positive_lawSensitive
expect_information_occurrence substLength_pos in objectArena
  from "D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations"

def upperRealization := pointwiseOrderRealization (fun b : Bool => (subst b).length) (fun _ => 2)
theorem upper_bridge : LegacyPrimitiveRealization weakArena
    (∀ b : Bool, (subst b).length ≤ 2) upperRealization := pointwiseOrderLegacy _ false _ _
theorem upper_lawSensitive : weakArena.Law upperRealization ∧
    ¬ weakArena.Law (pointwiseOrderRealization (fun _ : Bool => 1) (fun _ => 0)) :=
  ⟨upper_bridge.equivalence.mp substLength_le_two, fun h => (by decide : ¬ 1 ≤ 0) (h false)⟩
register_information_theorem substLength_le_two in weakArena
  object_arena objectArena catalog substitutionBounds
  primitives upperRealization.toPrimitiveBundle realization upper_bridge
  variation upper_lawSensitive sensitivity weak_slotSensitive
example : substLength_le_two.«D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds».__information_unit.Statement =
    (∀ b : Bool, (subst b).length ≤ 2) := rfl
#print axioms upper_bridge
#print axioms upper_lawSensitive
expect_information_occurrence substLength_le_two in objectArena
  from "D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations"

#print axioms strict_slotSensitive
#print axioms weak_slotSensitive
#seal_information_theory

open Lean in
run_meta do
  let env ← getEnv
  for entry in InformationRegistry.entries env do
    if entry.registrationModuleName == env.header.mainModule then
      let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName env.header.mainModule)
      let some (.lit (.strVal diagnostic)) := info.value?
        | throwError "registration diagnostic is not a literal"
      if diagnostic.isEmpty then
        logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0],readout[1]]"
      else
        logWarning diagnostic

end D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
