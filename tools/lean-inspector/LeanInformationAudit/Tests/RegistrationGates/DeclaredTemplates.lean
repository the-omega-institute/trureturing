import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
import LeanInformationAudit.Syntax
import LeanInformationAudit.Tests.SourceIsolation

namespace LeanInformationAudit.Tests.DeclaredTemplates
open Lean Meta Elab Command TemplateAudit
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

-- A homogeneous signature avoids proof-to-data Eq.rec transports. The existing
-- heterogeneous separation signature is an explicit unsupported control below.
def symbolicSignature (X Y : Type) [DecidableEq Y] : PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Y
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def symbolicPointwise {X Y : Type} [DecidableEq Y] (f g : X → Y) :
    PrimitiveRealization (symbolicSignature X Y) where
  readout := fun b x => Bool.rec (f x) (g x) b
  anchor := Fin.elim0

def boolCases {X : Type} (f g : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => Bool.rec (f x) (g x) (f x))

def propositionSlot (P : Prop) {X : Type} (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) := cutRealization f

def wrongInterface (x : Bool) : Bool := x

def closedDecision {X : Type} : PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun _ => decide True)

def recursiveBody {X : Type} (f : X → Bool) (n : Nat) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => Nat.rec (f x) (fun _ b => b) n)

/-- Each oracle captures the actual enrollment result, then restores the whole
command state. A setup/compiler failure is separate from an expected [FAIL]. -/
elab "observe_declared_template_enrollment" : command => do
  let cases : Array (String × Name × Option String) := #[
    ("symbolic_pointwise_telescope_accepted",
      ``symbolicPointwise, none),
    ("constructive_bool_cases_accepted", ``boolCases, none),
    ("existing_pointwise_eq_cast_is_unsupported",
      `D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.pointwiseEqRealization,
      some "unclassified_form:E4.recursion:Eq.rec"),
    ("telescope_prop_slot_rejected", ``propositionSlot, some "unclassified_form:E1.proposition_slot"),
    ("telescope_wrong_interface_rejected", ``wrongInterface, some "unclassified_form:E1.return_interface"),
    ("body_closed_decision_rejected", ``closedDecision, some "unclassified_form:E3.closed_decision"),
    ("body_recursive_definition_rejected", ``recursiveBody, some "unclassified_form:E4.recursion:Nat.rec")]
  for (label, name, expected) in cases do
    let state ← get
    let result ← enroll name
    let actual := match result with | .ok () => none | .error text => some text
    let present := (selectedPlan (← getEnv) name).isOk
    set state
    let ok := actual == expected && present == expected.isNone
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label} result={repr actual}"

observe_declared_template_enrollment

elab "observe_declared_template_plan_identity" : command => do
  let saved ← get
  let .ok () ← enroll ``symbolicPointwise | throwError "identity fixture enrollment failed"
  let .ok plan := selectedPlan (← getEnv) ``symbolicPointwise
    | throwError "identity fixture plan missing"
  unless !plan.sourceInputs.isEmpty && plan.sourceInputs.all (fun input => input.path.endsWith ".lean") do
    throwError "[FAIL] enrollment_inputs_exclude_global_configuration"
  let .ok bytes := planEncoding plan | throwError "identity fixture encoding failed"
  (if bytes.size == plan.serializedBytes && Sha256.hex bytes == plan.planIdentity then logInfo else logError) m!"[{if bytes.size == plan.serializedBytes && Sha256.hex bytes == plan.planIdentity then "PASS" else "FAIL"}] complete_plan_encoding_binds_all_nodes bytes={bytes.size} work={plan.chargedWork}"
  let variants := #[
    ("summary_changed_body_rejected", { plan with bodyIdentity := String.ofList (List.replicate 64 'a') }),
    ("summary_wrong_owner_rejected", { plan with enrollmentOwner := `WrongOwner })]
  for (label, variant) in variants do
    let .ok payload := planEncoding variant | throwError "setup: mutation payload encoding failed"
    let frame : TemplatePlanFrame := { key := plan.name.toString.toUTF8, payload, identity := plan.planIdentity }
    let index := ({} : TemplateIndex).addFrame frame (← getEnv) plan.enrollmentOwner
    let result := index.lookup plan.name (pure () : Id Unit)
    (if result matches .error "incomplete_closure:E7.import_identity" then logInfo else logError) m!"[{if result matches .error "incomplete_closure:E7.import_identity" then "PASS" else "FAIL"}] {label}"
  let frame : TemplatePlanFrame := { key := plan.name.toString.toUTF8, payload := bytes, identity := plan.planIdentity }
  let valid := ({} : TemplateIndex).addFrame frame (← getEnv) plan.enrollmentOwner
  (if (valid.lookup plan.name (pure () : Id Unit)).isOk then logInfo else logError) m!"[{if (valid.lookup plan.name (pure () : Id Unit)).isOk then "PASS" else "FAIL"}] fresh_source_bound_plan_accepted"
  LeanInformationAudit.Tests.withPrivateSources do
    let manifestPath := "lean-report-inputs.json"
    let .ok manifest := Json.parse (← IO.FS.readFile manifestPath)
      | throwError "setup: invalid manifest"
    let .ok fields := manifest.getObj? | throwError "setup: invalid manifest fields"
    let .ok version := manifest.getObjValAs? Nat "report_cache_release_semantic_version"
      | throwError "setup: missing cache release version"
    IO.FS.writeFile manifestPath ((Json.mkObj (fields.toList.map fun (key, value) =>
      (key, if key == "report_cache_release_semantic_version" then toJson (version + 1) else value))).compress)
    let retained := ({} : TemplateIndex).addFrame frame (← getEnv) plan.enrollmentOwner
    unless (retained.lookup plan.name (pure () : Id Unit)).isOk do
      throwError "[FAIL] manifest_version_preserves_enrollment_encoding_and_verdict"
    setEnv saved.env
    let .ok () ← enroll ``symbolicPointwise | throwError "setup: bumped manifest enrollment failed"
    let .ok fresh := selectedPlan (← getEnv) ``symbolicPointwise
      | throwError "setup: fresh plan missing"
    let .ok freshBytes := planEncoding fresh | throwError "setup: fresh encoding failed"
    unless freshBytes == bytes && fresh.planIdentity == plan.planIdentity do
      throwError "[FAIL] manifest_version_preserves_enrollment_encoding_and_verdict"
    logInfo "[PASS] manifest_version_preserves_enrollment_encoding_and_verdict"
  setEnv saved.env

observe_declared_template_plan_identity

end LeanInformationAudit.Tests.DeclaredTemplates
