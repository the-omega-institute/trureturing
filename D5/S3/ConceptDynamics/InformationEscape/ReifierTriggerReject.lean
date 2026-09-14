/- GID: D5/S3/ConceptDynamics/InformationEscape/ReifierTriggerReject
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/ReifierTriggerReject
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A specialized readout must be rejected before a frozen theorem can be registered. -/

import D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S0.Tower.DBonacci.Substitution
import D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.ReifierTriggerReject

open PointwiseRegistrationTemplates LeanInformationAudit
open D5.S0.Tower.DBonacci.Substitution
open D5.S0.Tower.Tribonacci.Substitution (TribonacciGapLetter gapLetterSubstitution)
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates

-- These are registrations of the fixed source statements, so generality is I.
-- Utility is none: this probe registers existing theorems and proves no new instance.
def substitutionArena := pointwiseEqArena (Arena.ofFintype (Fin 3)) (List TribonacciGapLetter)

-- The descriptor fixes label 0 while the frozen theorem quantifies over every label.
register_information_theorem gapLabelSubstitution_three_compatible via (ReifierTemplates.pointwise
  (fun _ : Fin 3 => (gapLabelSubstitution 3 0).map tribonacciGapLetterOfLabel) (fun _ => gapLetterSubstitution (tribonacciGapLetterOfLabel 0))) in substitutionArena output_evidence (nontrivial_of_ne [] [.small] (by decide))

-- Keep the command error visible while checking transactional rollback.
open Lean in
run_meta do
  let env ← getEnv
  let ownEntries := (InformationRegistry.entries env).filter
    (fun entry => entry.registrationModuleName == env.header.mainModule)
  unless ownEntries.isEmpty do
    throwError "rejected command inserted a registry row"
  let owner := ``gapLabelSubstitution_three_compatible
  let unit := localCompanionName env owner theoremUnitSuffix
  for name in #[unit, localCompanionName env owner primitiveRealizationSuffix,
      unit.str "__variation", unit.str "__sensitivity", unit.str "__nondegenerate",
      RegistrationGates.diagnosticName unit env.header.mainModule] do
    if env.contains name then
      throwError "rejected command leaked generated declaration {name}"
  logInfo "REIFIER_REJECT_ROLLBACK_CHECKED registry_rows=0 generated_declarations=0"

end D5.S3.ConceptDynamics.InformationEscape.ReifierTriggerReject
