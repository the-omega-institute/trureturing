import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates
import D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates

namespace LeanInformationAudit.Tests.DeclaredBindings
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

register_information_template cutRealization

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ x : Bool, r.readout () x = x.not.not

instance : DecidableEq arena.State := instDecidableEqBool

information_theorem validated in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

information_theorem unresolved in arena
  readout via (missingTemplate (fun x : Bool => x))
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

information_theorem undeclared in arena
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

run_meta do
  let records := TemplateBinding.records (← getEnv)
  let some valid := records.find? (·.occurrence.key.theoremName == ``validated)
    | throwError "setup: missing native record"
  let some missing := records.find? (·.occurrence.key.theoremName == ``unresolved)
    | throwError "setup: missing unresolved record"
  let some absent := records.find? (·.occurrence.key.theoremName == ``undeclared)
    | throwError "setup: missing undeclared record"
  let validOk := match valid.result with | .declaredValidated _ => true | _ => false
  let missingOk := match missing.result with
    | .declaredUnresolved diagnostic => (diagnostic.splitOn "rule=dtr.missing_template").length == 2
    | _ => false
  let absentOk := match absent.result with | .undeclared => true | _ => false
  logInfo m!"[{if validOk then "PASS" else "FAIL"}] validated_record_has_certificate"
  if let .declaredUnresolved diagnostic := valid.result then logInfo diagnostic
  logInfo m!"[{if missingOk then "PASS" else "FAIL"}] unresolved_record_without_module_failure"
  logInfo m!"[{if absentOk && missingOk then "PASS" else "FAIL"}] uncertified_states_have_no_certificate"

declare_information_template_binding undeclared in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))

run_meta do
  let joined ← TemplateBinding.assessJoined
  let some overlay := joined.find? (·.occurrence.key.theoremName == ``undeclared)
    | throwError "setup: missing joined record"
  let valid := match overlay.result with | .declaredValidated _ => true | _ => false
  logInfo m!"[{if valid then "PASS" else "FAIL"}] sidecar_join_precedes_assessment"

end LeanInformationAudit.Tests.DeclaredBindings
