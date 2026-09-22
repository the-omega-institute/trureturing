import LeanInformationAudit.Tests.RegistrationGates.DeclaredComparison

namespace LeanInformationAudit.Tests.DeclaredProjection
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def literalProjection : PrimitiveRealization (cutSignature Bool Bool) :=
  ⟨(⟨fun _ => (fun x : Bool => x), Fin.elim0⟩ :
      PrimitiveRealization (cutSignature Bool Bool)).readout, Fin.elim0⟩

def discardedAnchor : Fin 0 → Bool :=
  let _h := DeclaredBindings.validated
  Fin.elim0

def dirtyProjection : PrimitiveRealization (cutSignature Bool Bool) :=
  ⟨(⟨fun _ => (fun x : Bool => x), discardedAnchor⟩ :
      PrimitiveRealization (cutSignature Bool Bool)).readout, Fin.elim0⟩

@[implemented_by DeclaredComparison.directApplication]
def runtimeOverride : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun x : Bool => x)

private def observe (event : TemplateOccurrenceEvent) (actual : Name)
    (descriptor : Expr) (label : String) (diagnostic : Option String := none) : MetaM Unit := do
  let claim : TemplateBindingClaim := {
    key := event.key
    arena := event.arena
    descriptor := some descriptor
    owner := (← getEnv).header.mainModule }
  let record ← TemplateBinding.assess { event with realizationName := actual } (some claim)
  let (ok, result) := match record.result, diagnostic with
    | .declaredValidated _, none => (true, "validated")
    | .declaredUnresolved message, some expected =>
      ((message.splitOn expected).length == 2, message)
    | .declaredUnresolved message, none => (false, message)
    | _, _ => (false, "unexpected alternative")
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"
  unless ok do logInfo m!"actual={result}"

run_meta do
  let some event := (TemplateBinding.inventory (← getEnv)).find?
      (·.key.theoremName == `LeanInformationAudit.Tests.DeclaredBindings.validated)
    | throwError "setup: missing retained occurrence"
  let .defnInfo direct ← getConstInfo ``DeclaredComparison.directApplication
    | throwError "setup: missing descriptor"
  observe event ``DeclaredComparison.projectedRecord direct.value "selected_projection_receiver_accepted"
  observe event ``literalProjection direct.value "literal_projection_receiver_accepted"
  observe event ``dirtyProjection direct.value "discarded_projection_field_audited"
    (some "reason=forbidden_dependency rule=dtr.argument_audit site=")
  observe event ``runtimeOverride direct.value "extraction_runtime_override_rejected"
    (some "reason=unclassified_form rule=dtr.extraction_kind site=")

end LeanInformationAudit.Tests.DeclaredProjection
