import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates
import LeanInformationAudit.Tests.RegistrationGates.InventoryAssertions

namespace LeanInformationAudit.Tests.DeclaredEvidence
open Lean Meta Elab Command TemplateAudit TemplateBinding
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ x : Bool, r.readout () x = x.not.not

instance : DecidableEq arena.State := instDecidableEqBool

-- The observer captures errors from the real command elaborator, including a
-- mutant that throws instead of committing unresolved metadata.
private def commandException (action : CommandElabM Unit) : CommandElabM (Option Exception) :=
  fun context state => do
    try action context state; return none
    catch error => return some error

elab "observe_declared_evidence" : command => do
  let initial ← get
  let name := initial.env.header.mainModule.str "probe"
  let target := mkIdent (`_root_ ++ name)
  let forms ← pure #[
    ("validated_record_has_certificate", 0, ← `(command| information_theorem $target in arena
      readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
      primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
      : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm)),
    ("unresolved_record_without_module_failure", 1, ← `(command| information_theorem $target in arena
      readout via (missingTemplate (fun x : Bool => x))
      primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
      : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm)),
    ("uncertified_states_have_no_certificate", 2, ← `(command| information_theorem $target in arena
      primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
      : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm))]
  let mut observations : Array String := #[]
  for (label, kind, form) in forms do
    set initial
    modify fun state => { state with messages := {} }
    let .ok () ← enroll ``cutRealization | throwError "setup: independent template enrollment failed"
    let caught ← commandException (elabCommand form)
    let env ← getEnv
    let inventoryOk ← if kind == 2 then
        liftTermElabM <| Tests.assertUndeclaredInventory env env.header.mainModule 1
      else pure true
    let retained := (records env).find? (·.occurrence.key.theoremName == name)
    let event := (inventory env).find? (·.key.theoremName == name)
    let result := match retained.map (·.result), kind with
      | some (.declaredValidated certificate), 0 => certificate.evidenceRef.length == 64
      | some (.declaredUnresolved message), 1 =>
        (message.splitOn "rule=dtr.missing_template").length == 2
      | some .undeclared, 2 => true
      | _, _ => false
    let ok := inventoryOk && caught.isNone && !(← get).messages.hasErrors && event.isSome && result &&
      InformationRegistry.hasTheorem env name
    set initial
    observations := observations.push s!"[{if ok then "PASS" else "FAIL"}] {label}"

  for observation in observations do logInfo observation

  -- Inject after the nested command has published its event, binding record,
  -- certificate and generated declarations, and after enrollment has committed.
  let before ← get
  let staged ← IO.mkRef false
  let caught ← commandException <| registrationTransaction do
    let .ok () ← enroll ``cutRealization | throwError "setup: rollback enrollment failed"
    elabCommand forms[0]!.2.2
    staged.set <| InformationRegistry.hasTheorem (← getEnv) name &&
      (inventory (← getEnv)).any (·.key.theoremName == name) &&
      (records (← getEnv)).any (fun row => row.occurrence.key.theoremName == name &&
        match row.result with | .declaredValidated _ => true | _ => false)
    throwError "declared evidence rollback injection"
  let after ← getEnv
  let clean := caught.isSome && (← staged.get) && !after.contains name &&
    !InformationRegistry.hasTheorem after name &&
    !(inventory after).any (·.key.theoremName == name) &&
    !(records after).any (·.occurrence.key.theoremName == name) &&
    !(selectedPlan after ``cutRealization).isOk
  set before
  (if clean then logInfo else logError) m!"[{if clean then "PASS" else "FAIL"}] binding_transaction_rolls_back"

observe_declared_evidence

end LeanInformationAudit.Tests.DeclaredEvidence
