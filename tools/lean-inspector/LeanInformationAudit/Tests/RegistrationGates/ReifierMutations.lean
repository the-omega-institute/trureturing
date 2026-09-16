import D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates
import LeanInformationAudit.Syntax

namespace LeanInformationAudit.Tests.ReifierMutations
open Lean Meta Elab Command RegistrationReifier
open D5.S3.ConceptDynamics.InformationEscape PointwiseRegistrationTemplates

-- Assertion failures are errors in the canonical build; all observations still run.
private def observe (label : String) (check : MetaM Bool) : MetaM Unit := do
  let ok ← check
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

def arena := pointwiseEqArena (Arena.ofFintype Bool) Bool
theorem clean (x : Bool) : x.not.not = x := Bool.not_not _
register_information_theorem clean
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in arena

run_meta do
  let a := Expr.letE `unused (mkConst ``True) (mkConst ``True.intro) (mkConst ``Bool.true) true
  observe "preserved_let" (exact a a)
  observe "collapsed_let" (not <$> exact a (mkConst ``Bool.true))
  let f := Expr.forallE `x (mkConst ``Bool) (mkConst ``True) .default
  observe "binder_information" (not <$> exact f (.forallE `x (mkConst ``Bool) (mkConst ``True) .implicit))
  let pair := mkAppN (mkConst ``Prod.mk [.zero, .zero])
    #[mkConst ``Bool, mkConst ``Bool, mkConst ``Bool.false, mkConst ``Bool.true]
  observe "projection_argument" (not <$> exact (.proj ``Prod 0 pair)
    (.proj ``Prod 0 (mkAppN pair.getAppFn (pair.getAppArgs.set! 3 (mkConst ``Bool.false)))))
  let some entry := InformationRegistry.find? (← getEnv) ``clean | throwError "missing control"
  validateDerivedCertificate entry
  observe "valid_certificate" (pure entry.derivedCertificate.isSome)
  let some cert := entry.derivedCertificate | throwError "missing certificate"
  let copied := { entry with registrationModuleName := `CopiedModule }
  for (label, candidate) in #[("copied_certificate", copied),
      ("rebound_certificate", { copied with derivedCertificate := some {
        cert with occurrence := occurrenceBinding copied } })] do
    let rejected ← try validateDerivedCertificate candidate; pure false catch e =>
      if !(← e.toMessageData.toString).startsWith "P1.CertificateBindingMismatch" then throw e
      pure true
    observe label (pure rejected)

theorem reflexive (x : Bool) : x = x := rfl
theorem hidden (x : Bool) : (have _p := clean; x.not.not) = x := Bool.not_not _

elab "observe_semantic_insertion" : command => do
  let forms ← pure #[
    ("reflexive_closed_truth", ``reflexive, ← `(command| register_information_theorem reflexive
      via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => x) (fun x => x)) in arena)),
    ("provenance_hidden_proof", ``hidden, ← `(command| register_information_theorem hidden
      via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => have _p := clean; x.not.not) (fun x => x)) in arena))]
  for (label, name, form) in forms do
    let initial ← get
    modify fun s => { s with messages := {} }
    elabCommand form
    let inserted := InformationRegistry.hasTheorem (← getEnv) name
    let errors := (← get).messages.toList.filter (·.severity == .error)
    let mut rejected := false
    if errors.length == 1 then
      let message ← errors[0]!.data.toString
      rejected := message.startsWith "P1.SemanticRejected: IE-C050 " &&
        (message.splitOn "reason=unclassified_form").length == 2 &&
        (if label == "reflexive_closed_truth" then
          (message.splitOn "rule=p1.reflexive_source").length == 2
         else (message.splitOn "rule=dtr.argument_audit").length == 2)
    set initial
    if !inserted && !rejected then throwError "unexpected semantic probe diagnostic: {label}"
    (if !inserted && rejected then logInfo else logError) m!"[{if !inserted && rejected then "PASS" else "FAIL"}] {label}"

observe_semantic_insertion
end LeanInformationAudit.Tests.ReifierMutations
