import D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates
import LeanInformationAudit.Syntax

namespace LeanInformationAudit.Tests.DeclaredP1
open Lean Meta Elab Command RegistrationReifier
open D5.S3.ConceptDynamics.InformationEscape PointwiseRegistrationTemplates

def arena := pointwiseEqArena (Arena.ofFintype Bool) Bool
theorem clean (x : Bool) : x.not.not = x := Bool.not_not _
register_information_theorem clean
  via (ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in arena
  readout via (missingTemplate (fun x : Bool => x))

theorem hidden (x : Bool) : (have _p := clean; x.not.not) = x := Bool.not_not _

run_meta do
  let some entry := InformationRegistry.find? (← getEnv) ``clean
    | throwError "setup: P1 source missing"
  validateDerivedCertificate entry
  closedTruthExcluded entry
  let some record := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == ``clean) | throwError "setup: P1 binding record missing"
  let valid := match record.result with
    | .declaredUnresolved message => (message.splitOn "rule=dtr.missing_template").length == 2
    | _ => false
  logInfo m!"[{if valid && entry.derivedCertificate.isSome then "PASS" else "FAIL"}] p1_faithful_registration_accepted"
  let before ← RegistrationGates.observedWholeReadoutCalls
  let diagnostic ← RegistrationGates.validateFinite entry
  let after ← RegistrationGates.observedWholeReadoutCalls
  logInfo m!"[{if before == after && diagnostic.isNone then "PASS" else "FAIL"}] p1_argument_audit_without_template_scan"

elab "observe_p1_argument_insertion" : command => do
  let saved ← get
  modify fun state => { state with messages := {} }
  elabCommand (← `(command| register_information_theorem hidden
    via (ReifierTemplates.pointwise
      (fun x : Bool => have _p := clean; x.not.not) (fun x => x)) in arena))
  let inserted := InformationRegistry.hasTheorem (← getEnv) ``hidden
  let errors := (← get).messages.toList.filter (·.severity == .error)
  let message ← if errors.length == 1 then errors[0]!.data.toString else pure ""
  let rejected := message.startsWith "P1.SemanticRejected: IE-C050 " &&
    (message.splitOn "reason=unclassified_form rule=dtr.argument_audit").length == 2
  set saved
  logInfo m!"[{if !inserted && rejected then "PASS" else "FAIL"}] p1_semantic_insert_still_throws"
  unless !inserted && rejected do logInfo m!"actual={message} inserted={inserted}"

observe_p1_argument_insertion

run_meta do
  let saved ← getEnv
  let some original := InformationRegistry.find? saved ``clean | throwError "setup: P1 source"
  let some certificate := original.derivedCertificate | throwError "setup: P1 certificate"
  let entry ← derive { original with
      unitName := original.unitName.str "dirtyDiagnostic"
      realizationName := original.realizationName.str "dirtyDiagnostic"
      derivedCertificate := none } certificate.arena certificate.descriptor
  RegistrationGates.publishDiagnostic entry.unitName (some "IE-C048 fixture retained rejection")
  let rejected ← try
    closedTruthExcluded entry
    pure false
  catch error =>
    pure ((← error.toMessageData.toString) ==
      "P1.SemanticRejected: incomplete or unbound registration diagnostic")
  setEnv saved
  logInfo m!"[{if rejected then "PASS" else "FAIL"}] p1_persisted_diagnostic_still_checked"

end LeanInformationAudit.Tests.DeclaredP1
