import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

namespace LeanInformationAudit.Tests.DependentFamilyFixedControl
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ x : Bool, r.readout () x = x

local instance : DecidableEq arena.State := instDecidableEqBool

def reads : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun x : Bool => x)

register_information_template cutRealization

information_theorem fixed in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  primitives reads escape from (Bool) escape continues (open)
  : ∀ x : Bool, x = x := fun _ => rfl

run_cmd do
  let some row := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == ``fixed) | throwError "missing fixed control"
  match row.result with
  | .declaredValidated certificate =>
    unless certificate.escape.fromObject.isSome && certificate.escape.family.isNone do
      throwError "fixed-State evidence changed mode"
    logInfo "[PASS] native_fixed_state_four_slots"
  | .declaredUnresolved diagnostic => throwError diagnostic
  | _ => throwError "fixed-State control undeclared"

end LeanInformationAudit.Tests.DependentFamilyFixedControl
