import Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.InformationRoot
import Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot
import Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow
import Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot
import Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.InformationRoot
import Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.LegacyAssignedTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape

def alteredLaw (a : PrimitiveLawArena) : PrimitiveLawArena := { a with Law := fun _ => True }

run_meta do
  let expected := #[
    (`Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.InformationRoot, `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power,
      `Reg.Support.LegacyAgenda.arena),
    (`Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow, `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power,
      `Reg.Support.LegacyAgenda.arena),
    (`Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot, `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification,
      `Reg.Support.LegacyResidue.arena),
    (`Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow, `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification,
      `Reg.Support.LegacyResidue.arena),
    (`Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot, `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design,
      `Reg.Support.LegacyStaticDesign.arena),
    (`Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow, `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design,
      `Reg.Support.LegacyStaticDesign.arena),
    (`Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.InformationRoot, `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state,
      `Reg.Support.LegacyGluing.arena),
    (`Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow, `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state,
      `Reg.Support.LegacyGluing.arena)]
  let env ← getEnv
  let mut selected := #[]
  for (owner, theoremName, arena) in expected do
    let events := (TemplateBinding.inventory env).filter (·.key.registrationModule == owner)
    let #[event] := events | throwError "expected one retained occurrence for {owner}"
    unless event.key.theoremName == theoremName && event.key.objectArena == arena &&
        event.key.root == owner do throwError "assigned occurrence retargeted"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "missing assigned claim"
    let record ← TemplateBinding.assess event (some claim)
    let .declaredValidated certificate := record.result
      | throwError "assigned registration unfinished: {(← TemplateBinding.recordJson record).compress}"
    unless record.escape.fromObject.isSome &&
        record.escape.continuation.any (·.kind == "open") do throwError "missing escape slots"
    unless !certificate.evidenceRef.isEmpty do throwError "missing current certificate"
    let lawArena ← mkAppM ``ObjectDomainArena.toPrimitiveLawArena #[mkConst arena]
    let altered ← mkAppM ``alteredLaw #[lawArena]
    let sensitivityType ← mkAppM ``FiniteSlotSensitivity #[altered]
    if ← RegistrationGates.checked (arena.getPrefix ++ `sensitivity) sensitivityType then
      throwError "actual sensitivity certificate accepted for a constant-true Law"
    let absent ← TemplateBinding.assess event none
    unless absent.result matches .undeclared do throwError "missing descriptor accepted"
    let changed ← TemplateBinding.assess
      { event with key := { event.key with objectArena := `ChangedLaw } } (some claim)
    if changed.result matches .declaredValidated _ then throwError "altered Law arena accepted"
    let changed ← TemplateBinding.assess
      { event with key := { event.key with theoremName := ``True.intro } } (some claim)
    if changed.result matches .declaredValidated _ then throwError "changed original theorem accepted"
    logInfo m!"[PASS] assigned occurrence {owner} evidence_ref={certificate.evidenceRef}"
    selected := selected.push (owner, #[event.key])
  let wire := Json.arr (← TemplateBinding.reportJson selected)
  IO.FS.writeFile ((← Repository.root) / ".lake/build/legacy-assigned-transport.json")
    (wire.compress ++ "\n")
  logInfo "[PASS] eight distinct assigned occurrences, absent declaration and altered Law/source rejection"

end LeanInformationAuditRegTests.LegacyAssignedTransport
