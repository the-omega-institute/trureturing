import LeanInformationAudit.DispositionEvidence

namespace LeanInformationAudit.Tests.DeclaredStructural
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape

def template (A : StructuralArena) (sig : StructuralPrimitiveSignature)
    (f : ∀ i, A.State → sig.Output i) : StructuralPrimitiveRealization A sig := ⟨f⟩

register_information_template template

abbrev arena : StructuralArena := ⟨Bool⟩
def signature : StructuralPrimitiveSignature := ⟨Unit, inferInstance, fun _ => Bool⟩
def law : StructuralPrimitiveLawArena arena where
  signature := signature
  Law r := ∀ x : Bool, r.readout () x = x

structural_theorem declared in law
  readout via (template arena signature (fun _ x => x))
  realization (template arena signature (fun _ x => x)) := by intro x; rfl

structural_theorem undeclared in law
  realization (template arena signature (fun _ x => x)) := by intro x; rfl

run_meta do
  let rows := TemplateBinding.records (← getEnv)
  let some declared := rows.find? (·.occurrence.key.theoremName == ``declared)
    | throwError "setup: structural declared inventory missing"
  let some undeclared := rows.find? (·.occurrence.key.theoremName == ``undeclared)
    | throwError "setup: structural undeclared inventory missing"
  let valid := match declared.result with | .declaredValidated _ => true | _ => false
  let absent := match undeclared.result with | .undeclared => true | _ => false
  (if valid && absent then logInfo else logError) m!"[{if valid && absent then "PASS" else "FAIL"}] structural_registration_route_recorded"
  if let .declaredUnresolved error := declared.result then logInfo error

end LeanInformationAudit.Tests.DeclaredStructural
