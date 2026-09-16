import LeanInformationAudit.Tests.RegistrationGates.DeclaredBindings

namespace LeanInformationAudit.Tests.DeclaredComparison
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def sameShape (f : Bool → Bool) : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization f

abbrev definitionAlias := @cutRealization

namespace Lexical
export RegistrationTemplates (cutRealization)
end Lexical

def lexicalApplication : PrimitiveRealization (cutSignature Bool Bool) :=
  @Lexical.cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)

def directApplication : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)

def otherFunction : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool Bool.not

def otherEquality : DecidableEq Bool := instDecidableEqBool

def otherInstance : PrimitiveRealization (@cutSignature Bool Bool otherEquality) :=
  @cutRealization Bool Bool otherEquality (fun x : Bool => x)

-- The explicit universe is retained in the body while the result interface
-- stays the same. Both applications below elaborate independently.
def universeTemplate.{u} (f : Bool → Bool) : PrimitiveRealization (cutSignature Bool Bool) :=
  let Carrier : Type u := PUnit.{u + 1}
  cutRealization f

register_information_template universeTemplate

def universeLow : PrimitiveRealization (cutSignature Bool Bool) :=
  universeTemplate.{0} (fun x : Bool => x)

def universeHigh : PrimitiveRealization (cutSignature Bool Bool) :=
  universeTemplate.{1} (fun x : Bool => x)

def literalRecord : PrimitiveRealization (cutSignature Bool Bool) :=
  ⟨fun _ => (fun x : Bool => x), Fin.elim0⟩

def forwardedApplication : PrimitiveRealization (cutSignature Bool Bool) :=
  sameShape (fun x : Bool => x)

def dropping (ignored : Bool) (f : Bool → Bool) :
    PrimitiveRealization (cutSignature Bool Bool) := cutRealization f

def droppedApplication : PrimitiveRealization (cutSignature Bool Bool) :=
  dropping true (fun x : Bool => x)

def letApplication : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (let f : Bool → Bool := fun x => x; f)

def etaApplication : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun x : Bool => (fun y : Bool => y) x)

def projectedRecord : PrimitiveRealization (cutSignature Bool Bool) :=
  ⟨(@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)).readout,
    (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)).anchor⟩

def unregisteredDescriptor : PrimitiveRealization (cutSignature Bool Bool) :=
  sameShape (fun x : Bool => x)

def aliasDescriptor : PrimitiveRealization (cutSignature Bool Bool) :=
  @definitionAlias Bool Bool instDecidableEqBool (fun x : Bool => x)

def unusedCarrier (ignored : Type) (f : Bool → Bool) :
    PrimitiveRealization (cutSignature Bool Bool) := cutRealization f
register_information_template unusedCarrier

def discardProof (_ : ∀ x : Bool, x = x.not.not) : Arena := Arena.ofFintype Bool
def discardIndependent (_ : True) : Arena := Arena.ofFintype Bool

def rawCarrierBad : PrimitiveRealization (cutSignature Bool Bool) :=
  unusedCarrier (Option (Arena.State (discardProof DeclaredBindings.validated))) (fun x => x)
def rawCarrierProdBad : PrimitiveRealization (cutSignature Bool Bool) :=
  unusedCarrier (Bool × Arena.State (discardProof DeclaredBindings.validated)) (fun x => x)
def rawCarrierClean : PrimitiveRealization (cutSignature Bool Bool) :=
  unusedCarrier (Option (Arena.State (discardIndependent True.intro))) (fun x => x)
def decisionArgument : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun _ : Bool => decide ((0 : Nat) < 24))
def decisionBody (ignored : Bool) : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun _ : Bool => decide ((0 : Nat) < 24))

private def bodyOf (name : Name) : MetaM Expr := do
  let .defnInfo info ← getConstInfo name | throwError "setup: missing fixture definition"
  return info.value

private def observe (event : TemplateOccurrenceEvent) (actual : Name)
    (descriptor : Expr) (label : String) (rule : Option String := none) : MetaM Unit := do
  let claim : TemplateBindingClaim := {
    key := event.key
    arena := event.arena
    descriptor := some descriptor
    owner := (← getEnv).header.mainModule }
  let record ← TemplateBinding.assess { event with realizationName := actual }
    (some claim)
  let (ok, diagnostic) := match record.result, rule with
    | .declaredValidated certificate, none => (!certificate.evidenceRef.isEmpty, "validated")
    | .declaredUnresolved diagnostic, some rule =>
      ((diagnostic.splitOn s!"reason=unclassified_form rule={rule} site=").length == 2, diagnostic)
    | .declaredUnresolved diagnostic, none => (false, diagnostic)
    | _, _ => (false, "unexpected result alternative")
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"
  unless ok do logInfo m!"actual={diagnostic}"

elab "check_body_argument_grammar" : command => do
  let saved ← get
  let result ← TemplateAudit.enroll ``decisionBody
  let ok := result matches .error "unclassified_form:E3.closed_decision"
  set saved
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] body_argument_closed_decision_same_rule"
check_body_argument_grammar

-- Each observer calls the common assessor. The source event comes from an
-- actual successful command; no result is inserted into a producer extension.
run_meta do
  let env ← getEnv
  let some event := (TemplateBinding.inventory env).find?
      (·.key.theoremName == `LeanInformationAudit.Tests.DeclaredBindings.validated)
    | throwError "setup: missing independently registered occurrence"
  for (name, expected) in #[(``rawCarrierBad, "forbidden_dependency"),
      (``rawCarrierProdBad, "forbidden_dependency"), (``rawCarrierClean, "validated"),
      (``decisionArgument, "unclassified_form")] do
    let descriptor ← bodyOf name
    let claim : TemplateBindingClaim := {
      key := event.key
      arena := event.arena
      descriptor := some descriptor
      owner := env.header.mainModule }
    let record ← TemplateBinding.assess { event with realizationName := name } (some claim)
    let ok := match record.result with
      | .declaredValidated _ => expected == "validated"
      | .declaredUnresolved diagnostic =>
        (diagnostic.splitOn s!"reason={expected} rule=").length == 2
      | _ => false
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] declared_raw_argument_{name.getString!}"
    if let .declaredUnresolved diagnostic := record.result then logInfo diagnostic
  let direct ← bodyOf ``directApplication
  observe event ``directApplication direct "identical_full_application_accepted"
  observe event ``directApplication (← bodyOf ``lexicalApplication)
    "registered_lexical_alias_accepted"
  observe event ``directApplication (← bodyOf ``unregisteredDescriptor)
    "unregistered_same_shape_rejected" (some "dtr.unregistered_template")
  observe event ``directApplication (← bodyOf ``aliasDescriptor)
    "definition_alias_rejected" (some "dtr.unregistered_template")
  observe event ``otherFunction direct
    "explicit_argument_mismatch_rejected" (some "dtr.realization_mismatch")
  observe event ``otherInstance direct
    "implicit_instance_mismatch_rejected" (some "dtr.signature_mismatch")
  observe event ``universeLow (← bodyOf ``universeLow) "identical_rigid_universes_accepted"
  observe event ``universeHigh (← bodyOf ``universeLow)
    "rigid_universe_mismatch_rejected" (some "dtr.realization_mismatch")
  observe event ``literalRecord direct "frozen_constructor_record_accepted"
  observe event ``forwardedApplication direct "saturated_forwarder_accepted"
  observe event ``projectedRecord direct "fixed_record_projection_accepted"
  observe event ``droppedApplication direct
    "discarded_argument_wrapper_rejected" (some "dtr.realization_mismatch")
  observe event ``letApplication direct "let_wrapper_rejected" (some "dtr.realization_mismatch")
  observe event ``etaApplication direct "eta_wrapper_rejected" (some "dtr.realization_mismatch")
  let saved ← getEnv
  let name := `LeanInformationAudit.Tests.DeclaredComparison.metadataApplication
  let metadata := KVMap.empty.insert `decoration (DataValue.ofString "retained")
  let type ← inferType direct
  addDecl (.defnDecl {
    name
    levelParams := []
    type
    value := .mdata metadata direct
    hints := .abbrev
    safety := .safe })
  observe event name direct "metadata_mismatch_rejected" (some "dtr.realization_mismatch")
  setEnv saved

end LeanInformationAudit.Tests.DeclaredComparison
