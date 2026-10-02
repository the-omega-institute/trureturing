import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates
import D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

namespace LeanInformationAudit.Tests.DeclaredBindings
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

test_assess in register_information_template cutRealization

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ x : Bool, r.readout () x = x.not.not

instance : DecidableEq arena.State := instDecidableEqBool

test_assess in information_theorem validated in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

test_assess in information_theorem unresolved in arena
  readout via (missingTemplate (fun x : Bool => x))
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

test_assess in information_theorem undeclared in arena
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
  (if validOk then logInfo else logError) m!"[{if validOk then "PASS" else "FAIL"}] validated_record_has_certificate"
  if let .declaredUnresolved diagnostic := valid.result then logInfo diagnostic
  (if missingOk then logInfo else logError) m!"[{if missingOk then "PASS" else "FAIL"}] unresolved_record_without_module_failure"
  (if absentOk && missingOk then logInfo else logError) m!"[{if absentOk && missingOk then "PASS" else "FAIL"}] uncertified_states_have_no_certificate"


end LeanInformationAudit.Tests.DeclaredBindings
