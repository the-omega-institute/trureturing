import LeanInformationAudit.Tests.RegistrationGates.DeclaredEvidence

namespace LeanInformationAudit.Tests.DeclaredRollback
open Lean Meta Elab Command TemplateAudit TemplateBinding
open LeanInformationAudit.Tests.DeclaredEvidence
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

elab "observe_unresolved_transaction_commit" : command => do
  let saved ← get
  let name := saved.env.header.mainModule.str "commits"
  let target := mkIdent (`_root_ ++ name)
  registrationTransaction do
    let .ok () ← enroll ``cutRealization | throwError "setup: transaction template missing"
    elabCommand (← `(command| information_theorem $target in arena
      readout via (missingTemplate (fun x : Bool => x))
      primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
      : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm))
  let env ← getEnv
  let unresolved := (records env).any fun row => row.occurrence.key.theoremName == name &&
    match row.result with | .declaredUnresolved _ => true | _ => false
  let ok := !(← get).messages.hasErrors && env.contains name &&
    InformationRegistry.hasTheorem env name && unresolved &&
    (inventory env).any (·.key.theoremName == name) && (selectedPlan env ``cutRealization).isOk
  set saved
  logInfo m!"[{if ok then "PASS" else "FAIL"}] unresolved_evidence_transaction_commits"

observe_unresolved_transaction_commit

end LeanInformationAudit.Tests.DeclaredRollback
