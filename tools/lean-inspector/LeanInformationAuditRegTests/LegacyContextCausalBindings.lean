import Reg.Catalogs.InformationRoot
import Reg.Catalogs.TemplateShadow
import Reg.Catalogs.SharedInformationRoot
import Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot
import Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration
import Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.LegacyContextCausalBindings

run_meta do
  let modules := #[
    `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot,
    `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow,
    `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot,
    `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow,
    `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration,
    `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration]
  let env ← getEnv
  let inventory := (TemplateBinding.inventory env).filter
    (fun e => modules.contains e.key.registrationModule)
  unless inventory.size == 6 do throwError "expected exactly six historical occurrences"
  for owner in modules do
    let owned := inventory.filter (·.key.registrationModule == owner)
    unless owned.size == 1 do throwError "historical occurrence lost or duplicated: {owner}"
  for event in inventory do
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "missing original declaration"
    let record ← TemplateBinding.assess event (some claim)
    let .declaredValidated _ := record.result
      | throwError "original binding failed: {(← TemplateBinding.recordJson record).compress}"
    unless record.escape.fromObject.isSome &&
        record.escape.continuation.any (·.kind == "open") do
      throwError "original occurrence lacks escape evidence"
  logInfo "[PASS] six distinct historical occurrences: two contexts and four causal bindings validated"

run_cmd do
  for root in #[`Reg.Catalogs.InformationRoot, `Reg.Catalogs.TemplateShadow,
      `Reg.Catalogs.SharedInformationRoot] do
    let records := SealRecords.forRoot (← getEnv) root
    let artifact ← Elab.Command.liftTermElabM <| serializeSealArtifact records
    logInfo m!"LEGACY_CURRENT_SEAL {root} {Sha256.hex artifact.toUTF8}"

end LeanInformationAuditRegTests.LegacyContextCausalBindings
