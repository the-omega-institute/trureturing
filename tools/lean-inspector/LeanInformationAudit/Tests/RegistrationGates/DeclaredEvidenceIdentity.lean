import LeanInformationAudit.Tests.RegistrationGates.DeclaredBindings

namespace LeanInformationAudit.Tests.DeclaredEvidenceIdentity
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def proofTemplate (f : Bool → Bool) (_h : True) :
    PrimitiveRealization (cutSignature Bool Bool) := cutRealization f

register_information_template proofTemplate

private def observe (label : String) (ok : Bool) : MetaM Unit :=
  logInfo m!"[{if ok then "PASS" else "FAIL"}] {label}"

private def declare (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe })

private def certificate (event : TemplateOccurrenceEvent) (descriptor : Expr) :
    MetaM TemplateBindingCertificate := do
  let record ← TemplateBinding.assess event (some {
    key := event.key, arena := event.arena, descriptor := some descriptor,
    owner := (← getEnv).header.mainModule })
  match record.result with
  | .declaredValidated result => return result
  | .declaredUnresolved diagnostic => throwError "setup: {diagnostic}"
  | .undeclared => throwError "setup: independent binding was undeclared"

run_meta do
  let saved ← getEnv
  let some event := (TemplateBinding.inventory saved).find?
      (·.key.theoremName == `LeanInformationAudit.Tests.DeclaredBindings.validated)
    | throwError "setup: missing retained registration event"
  let functionName := `LeanInformationAudit.Tests.DeclaredEvidenceIdentity.inputFunction
  let actualName := `LeanInformationAudit.Tests.DeclaredEvidenceIdentity.actual
  let bool := mkConst ``Bool
  let functionType ← mkArrow bool bool
  let identity := mkLambda `x .default bool (.bvar 0)
  let descriptor ← mkAppM ``cutRealization #[identity]
  let realizationType ← inferType descriptor
  let buildArgument := fun value => do
    setEnv saved
    declare functionName functionType value
    let descriptor ← mkAppM ``cutRealization #[mkConst functionName]
    declare actualName realizationType descriptor
    certificate { event with realizationName := actualName } descriptor
  let first ← buildArgument identity
  let repeated ← buildArgument identity
  let changed ← buildArgument (mkConst ``Bool.not)
  observe "identical_dependency_reuses_evidence" (first.evidenceRef == repeated.evidenceRef)
  observe "argument_dependency_changes_evidence" (first.evidenceRef != changed.evidenceRef)

  let helperName := `LeanInformationAudit.Tests.DeclaredEvidenceIdentity.forwarder
  let secondName := `LeanInformationAudit.Tests.DeclaredEvidenceIdentity.secondForwarder
  let buildExtraction := fun nested => do
    setEnv saved
    let helperType ← mkArrow functionType realizationType
    let helperBody ← withLocalDeclD `f functionType fun f => do
      mkLambdaFVars #[f] (← mkAppM ``cutRealization #[f])
    declare secondName helperType helperBody
    let body := if nested then
      mkLambda `f .default functionType (mkApp (mkConst secondName) (.bvar 0)) else helperBody
    declare helperName helperType body
    declare actualName realizationType (mkApp (mkConst helperName) identity)
    certificate { event with realizationName := actualName } descriptor
  let direct ← buildExtraction false
  let nested ← buildExtraction true
  observe "extraction_dependency_changes_evidence" (direct.evidenceRef != nested.evidenceRef)
  let proofName := `LeanInformationAudit.Tests.DeclaredEvidenceIdentity.independentProof
  let buildProof := fun value => do
    setEnv saved
    declare proofName (mkConst ``True) value
    let descriptor ← mkAppM ``proofTemplate #[identity, mkConst proofName]
    declare actualName realizationType descriptor
    certificate { event with realizationName := actualName } descriptor
  let firstProof ← buildProof (mkConst ``True.intro)
  let secondProof ← buildProof (.letE `h (mkConst ``True) (mkConst ``True.intro) (.bvar 0) false)
  let firstInput := firstProof.argumentInputs.find? (·.name == proofName)
  let secondInput := secondProof.argumentInputs.find? (·.name == proofName)
  observe "unchanged_proof_type_retained"
    (firstInput.isSome && secondInput.isSome &&
      !firstInput.get!.typeIdentity.isEmpty && firstInput.get!.typeIdentity == secondInput.get!.typeIdentity)
  observe "independent_proof_body_omitted"
    (firstInput.isSome && secondInput.isSome &&
      firstInput.get!.bodyIdentity.isEmpty && secondInput.get!.bodyIdentity.isEmpty &&
      firstProof.evidenceRef == secondProof.evidenceRef)
  setEnv saved

end LeanInformationAudit.Tests.DeclaredEvidenceIdentity
