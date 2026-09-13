/- GID: D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitive_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitiveRealization
   digest: Two frozen cardinality equations share an ADMIT counting template with unchanged statements. -/

import D5.S3.ConceptDynamics.InformationEscape.CardinalityRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S3.ObserverMemory.FiniteForgettingCertificate
import D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.CardinalityRegistrations

open CardinalityRegistrationTemplates LeanInformationAudit

section Cognitive
open D5.S3.ObserverMemory.FiniteForgettingCertificate

def cognitiveArena := cardinalityArena (Arena.ofFintype CognitiveState) 6
def cognitiveRealization := cardinalityRealization (fun _ : CognitiveState => true)
theorem cognitive_bridge : LegacyPrimitiveRealization cognitiveArena
    (Fintype.card CognitiveState = 6) cognitiveRealization :=
  cardinalityLegacy CognitiveState 6
theorem cognitive_lawSensitive : cognitiveArena.Law cognitiveRealization ∧
    ¬ cognitiveArena.Law (cardinalityRealization (fun _ => false)) := by
  refine ⟨cognitive_bridge.equivalence.mp cognitive_state_card, ?_⟩
  simp [cognitiveArena, cardinalityArena, cardinalityRealization, Arena.ofFintype]
theorem cognitive_slotSensitive : FiniteSlotSensitivity cognitiveArena :=
  cardinality_sensitivity CognitiveState 6 cognitive_state_card (by decide)
register_information_theorem cognitive_state_card in cognitiveArena
  primitives cognitiveRealization.toPrimitiveBundle realization cognitive_bridge
  variation cognitive_lawSensitive sensitivity cognitive_slotSensitive
example : cognitive_state_card.__information_unit.Statement =
    (Fintype.card CognitiveState = 6) := rfl
#print axioms cognitive_bridge
#print axioms cognitive_lawSensitive
#print axioms cognitive_slotSensitive
expect_information_occurrence cognitive_state_card in cognitiveArena
  from "D5.S3.ConceptDynamics.InformationEscape.CardinalityRegistrations"
end Cognitive

section SourceGroups
open D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

def sourceGroupsArena := cardinalityArena (Arena.ofFintype PhysicalSourceGroup) 6
def sourceGroupsRealization := cardinalityRealization (fun _ : PhysicalSourceGroup => true)
theorem sourceGroups_bridge : LegacyPrimitiveRealization sourceGroupsArena
    (Fintype.card PhysicalSourceGroup = 6) sourceGroupsRealization :=
  cardinalityLegacy PhysicalSourceGroup 6
theorem sourceGroups_lawSensitive : sourceGroupsArena.Law sourceGroupsRealization ∧
    ¬ sourceGroupsArena.Law (cardinalityRealization (fun _ => false)) := by
  refine ⟨sourceGroups_bridge.equivalence.mp card_source_groups, ?_⟩
  simp [sourceGroupsArena, cardinalityArena, cardinalityRealization, Arena.ofFintype]
theorem sourceGroups_slotSensitive : FiniteSlotSensitivity sourceGroupsArena :=
  cardinality_sensitivity PhysicalSourceGroup 6 card_source_groups (by decide)
register_information_theorem card_source_groups in sourceGroupsArena
  primitives sourceGroupsRealization.toPrimitiveBundle realization sourceGroups_bridge
  variation sourceGroups_lawSensitive sensitivity sourceGroups_slotSensitive
example : card_source_groups.__information_unit.Statement =
    (Fintype.card PhysicalSourceGroup = 6) := rfl
#print axioms sourceGroups_bridge
#print axioms sourceGroups_lawSensitive
#print axioms sourceGroups_slotSensitive
expect_information_occurrence card_source_groups in sourceGroupsArena
  from "D5.S3.ConceptDynamics.InformationEscape.CardinalityRegistrations"
end SourceGroups


#seal_information_theory

open Lean in
run_meta do
  let env ← getEnv
  for entry in InformationRegistry.entries env do
    if entry.registrationModuleName == env.header.mainModule then
      let diagnosticName := RegistrationGates.diagnosticName entry.unitName env.header.mainModule
      let info ← getConstInfo diagnosticName
      let some (.lit (.strVal diagnostic)) := info.value?
        | throwError "registration diagnostic is not a literal"
      if diagnostic.isEmpty then
        logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0]]"
      else
        logWarning diagnostic

end D5.S3.ConceptDynamics.InformationEscape.CardinalityRegistrations
