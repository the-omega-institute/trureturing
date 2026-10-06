import LeanInformationAudit.CompiledAssessment

namespace LeanInformationAudit.TemplateBinding
open Lean TemplateAudit

/-- Pure join validation grants no insertion or certification capability.
Both publication and authoritative assessment consume this same relation. -/
def joinClaims (events : Array (Name × TemplateOccurrenceEvent))
    (claims : Array (Name × TemplateBindingClaim)) :
    Except String (Array (TemplateOccurrenceEvent × Option TemplateBindingClaim)) := do
  let mut indexed : Std.HashMap TemplateOccurrenceKey TemplateOccurrenceEvent := {}
  for (producer, event) in events do
    unless producer == event.key.registrationModule do throw "incomplete_closure:dtr.event_owner"
    if indexed.contains event.key then throw "incomplete_closure:dtr.duplicate_occurrence"
    indexed := indexed.insert event.key event
  let mut selected : Std.HashMap TemplateOccurrenceKey TemplateBindingClaim := {}
  for (producer, claim) in claims do
    unless producer == claim.owner && claim.owner == claim.key.registrationModule do throw "incomplete_closure:dtr.claim_owner"
    unless indexed.contains claim.key do throw "unclassified_form:dtr.dangling_claim"
    if selected.contains claim.key then throw "unclassified_form:dtr.duplicate_claim"
    if let some event := indexed[claim.key]? then
      unless claim.arena.equal event.arena do throw "unclassified_form:dtr.claim_occurrence"
    selected := selected.insert claim.key claim
  return events.map fun (_, event) => (event, selected[event.key]?)

def sourcePath := TemplateAudit.sourcePath

def keyJson (key : TemplateOccurrenceKey) : Json := Json.mkObj [
  ("root", toJson key.root.toString), ("registration_module", toJson key.registrationModule.toString),
  ("theorem", toJson key.theoremName.toString), ("object_arena", toJson key.objectArena.toString),
  ("catalog", toJson key.catalog.toString)]

private def certificateJson (certificate : TemplateBindingCertificate) : Json := Json.mkObj <| [
  ("key", keyJson certificate.key), ("evidence_ref", toJson certificate.evidenceRef),
  ("plan_identity", toJson certificate.planIdentity),
  ("descriptor_identity", toJson certificate.descriptorIdentity),
  ("actual_identity", toJson certificate.actualIdentity),
  ("argument_inputs", Json.arr (certificate.argumentInputs.map CompiledAssessment.dependencyJson)),
  ("extraction_inputs", Json.arr (certificate.extractionInputs.map CompiledAssessment.dependencyJson))] ++
  (certificate.sourceBinding.toList.map fun source => ("source_binding", source))

private def escapeFromJson (origin : EscapeFromIdentity) : Json := Json.mkObj [
  ("name", toJson origin.name.toString), ("type_identity", toJson origin.typeIdentity),
  ("object_identity", toJson origin.objectIdentity)]

private def escapeContinuationJson (residual : EscapeContinuationIdentity) : Json := Json.mkObj [
  ("kind", toJson residual.kind),
  ("declaration_name", toJson (residual.declarationName.map Name.toString)),
  ("statement_identity", toJson residual.statementIdentity),
  ("chain_name", toJson (residual.chainName.map Name.toString))]

/-- Shared record wire for the inspector and census authoritative snapshots. -/
def recordJson [Applicative m] (record : BindingRecord) : m Json := do
  let (state, diagnostic, certificate) := match record.result with
    | .undeclared => ("undeclared", toJson (CompiledAssessment.missingDeclarationDiagnostic record.occurrence.key), Json.null)
    | .declaredUnresolved diagnostic => ("declared_unresolved", toJson diagnostic, Json.null)
    | .declaredValidated certificate => ("declared_validated", Json.null, certificateJson certificate)
  return Json.mkObj [
    ("key", keyJson record.occurrence.key),
    ("registration_source_path", toJson record.occurrence.registrationSource),
    ("statement_identity", toJson record.occurrence.statementIdentity),
    ("unit_name", toJson record.occurrence.unitName.toString),
    ("realization_name", toJson record.occurrence.realizationName.toString),
    ("escape_from", record.escape.fromObject.map escapeFromJson |>.getD Json.null),
    ("escape_continues", record.escape.continuation.map escapeContinuationJson |>.getD Json.null),
    ("bridge_kind", toJson record.escape.bridgeKind),
    ("binding_source_path", record.bindingOwner.map (toJson ∘ sourcePath) |>.getD Json.null),
    ("state", toJson state), ("diagnostic", diagnostic), ("certificate", certificate)]

end LeanInformationAudit.TemplateBinding
