/- GID: D5/S3/ConceptDynamics/InformationEscape/ReifierTriggerAdmit
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/ReifierTriggerAdmit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two frozen pointwise statements exercise the content-plane reifier without specialization. -/

import D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S0.Tower.DBonacci.Substitution
import D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.ReifierTriggerAdmit

open PointwiseRegistrationTemplates LeanInformationAudit
open D5.S0.Tower.DBonacci.Substitution
open D5.S0.Tower.Tribonacci.Substitution (TribonacciGapLetter gapLetterSubstitution)
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates

-- These are registrations of the fixed source statements, so generality is I.
-- Utility is none: this probe registers existing theorems and proves no new instance.
def substitutionArena := pointwiseEqArena (Arena.ofFintype (Fin 3)) (List TribonacciGapLetter)
def recenterArena := pointwiseEqArena (Arena.ofFintype (Fin 3)) Point

register_information_theorem gapLabelSubstitution_three_compatible via (ReifierTemplates.pointwise
  (fun label : Fin 3 => (gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel) (fun label => gapLetterSubstitution (tribonacciGapLetterOfLabel label.1))) in substitutionArena output_evidence (nontrivial_of_ne [] [.small] (by decide))
register_information_theorem recenter_direction via (ReifierTemplates.pointwise
  (fun d : Fin 3 => recenter d (direction d)) (fun _ => (0, 0))) in recenterArena

expect_information_occurrence gapLabelSubstitution_three_compatible in substitutionArena
  from "D5.S3.ConceptDynamics.InformationEscape.ReifierTriggerAdmit"
expect_information_occurrence recenter_direction in recenterArena
  from "D5.S3.ConceptDynamics.InformationEscape.ReifierTriggerAdmit"

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

end D5.S3.ConceptDynamics.InformationEscape.ReifierTriggerAdmit
