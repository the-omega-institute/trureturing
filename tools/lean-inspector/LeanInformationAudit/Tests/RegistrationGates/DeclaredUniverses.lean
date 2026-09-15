import LeanInformationAudit.Tests.RegistrationGates.DeclaredBindings

namespace LeanInformationAudit.Tests.DeclaredUniverses
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def template.{u, v} (f : Bool → Bool) : PrimitiveRealization (cutSignature Bool Bool) :=
  let First : Type u := PUnit.{u + 1}
  let Second : Type v := PUnit.{v + 1}
  cutRealization f

register_information_template template

def descriptor.{u, v} : PrimitiveRealization (cutSignature Bool Bool) :=
  template.{u, v} (fun x : Bool => x)

def renamed.{a, b} : PrimitiveRealization (cutSignature Bool Bool) :=
  template.{a, b} (fun x : Bool => x)

def permuted.{a, b} : PrimitiveRealization (cutSignature Bool Bool) :=
  template.{b, a} (fun x : Bool => x)

def short.{a} : PrimitiveRealization (cutSignature Bool Bool) :=
  template.{a, a} (fun x : Bool => x)

-- An explicit, rigid two-universe statement supplies the occurrence context.
-- The assessor fixture changes only the extraction declaration in that context;
-- no synthetic record is inserted into the persistent inventory.
theorem statement.{u, v} : ∀ (_ : PUnit.{u + 1}) (_ : PUnit.{v + 1}) (x : Bool),
    x = x.not.not := by
  intro _ _ x
  exact (Bool.not_not x).symm

private def observe (event : TemplateOccurrenceEvent) (actual : Name)
    (descriptor : Expr) (label : String) (expected : Option String := none) : MetaM Unit := do
  let record ← TemplateBinding.assess { event with realizationName := actual } (some {
    key := event.key, arena := event.arena, descriptor := some descriptor,
    owner := (← getEnv).header.mainModule })
  let ok := match record.result, expected with
    | .declaredValidated certificate, none => !certificate.evidenceRef.isEmpty
    | .declaredUnresolved diagnostic, some rule =>
      (diagnostic.splitOn s!"reason=unclassified_form rule={rule} site=").length == 2
    | _, _ => false
  logInfo m!"[{if ok then "PASS" else "FAIL"}] {label}"
  unless ok do
    if let .declaredUnresolved diagnostic := record.result then logInfo diagnostic

run_meta do
  let some source := (TemplateBinding.inventory (← getEnv)).find?
      (·.key.theoremName == `LeanInformationAudit.Tests.DeclaredBindings.validated)
    | throwError "setup: missing source occurrence"
  let statement ← getConstInfo ``statement
  let .defnInfo declared ← getConstInfo ``descriptor | throwError "setup: descriptor"
  unless statement.levelParams == [`u, `v] && declared.levelParams == [`u, `v] do
    throwError "setup: independent rigid universe telescope"
  let .ok (identity, _) := TemplateAudit.rawIdentity statement.levelParams statement.type
    | throwError "setup: statement identity"
  let event := { source with
    key := { source.key with theoremName := statement.name }
    statement := statement.type, levelParams := statement.levelParams, statementIdentity := identity }
  observe event ``descriptor declared.value "same_universe_names_accepted"
  observe event ``renamed declared.value "positional_universe_renaming_accepted"
  observe event ``permuted declared.value "positional_universe_permutation_rejected"
    (some "dtr.realization_mismatch")
  observe event ``short declared.value "positional_universe_arity_rejected"
    (some "dtr.extraction_universes")

end LeanInformationAudit.Tests.DeclaredUniverses
