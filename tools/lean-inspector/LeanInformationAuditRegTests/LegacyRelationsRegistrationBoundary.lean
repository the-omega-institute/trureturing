import Reg.Catalogs.InformationRoot
import Reg.Catalogs.TemplateShadow
import LeanInformationAuditRegTests.ExplicitSourceOperands

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.LegacyRelationsRegistrationBoundary

private def assigned (owner : Name) : Bool := #[
  `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot,
  `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow,
  `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot,
  `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow,
  `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit].contains owner

private def rejects (rule : String) (event : TemplateOccurrenceEvent)
    (claim : TemplateBindingClaim) : MetaM Unit := do
  let record ← TemplateBinding.assess event (some claim)
  let .declaredUnresolved diagnostic := record.result | throwError "invalid source accepted: {rule}"
  unless diagnostic.contains rule do throwError "expected {rule}, got {diagnostic}"

run_meta do
  let env ← getEnv
  let events := (TemplateBinding.inventory env).filter (assigned ∘ (·.key.registrationModule))
  unless events.size == 5 do throwError "expected exactly five original occurrences"
  for event in events do
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "missing original declaration claim"
    let record ← TemplateBinding.assess event (some claim)
    let .declaredValidated certificate := record.result
      | throwError "original registration failed: {(← TemplateBinding.recordJson record).compress}"
    unless certificate.sourceBinding.isSome && record.escape.fromObject.isSome &&
        record.escape.continuation.any (·.kind == "open") do
      throwError "missing original four-slot evidence"
    logInfo m!"[PASS] original four slots: {event.key.registrationModule}; evidence={certificate.evidenceRef}"
    rejects "source.selection_missing" event {claim with escapeInput :=
      {claim.escapeInput with sourceSelection := none}}
    let selection := claim.escapeInput.sourceSelection.get!
    rejects "source.owner" event {claim with escapeInput :=
      {claim.escapeInput with sourceSelection := some {selection with owner := `Wrong}}}
    rejects "source.absent_occurrence" event {claim with escapeInput :=
      {claim.escapeInput with sourceSelection := some {selection with
        readouts := selection.readouts.set! 0 {selection.readouts[0]! with path := #["absent"]}}}}
    if event.key.theoremName ==
        `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary then
      -- Both paths exist, have the same type and remain distinct. Their exact
      -- source functions, rather than their type or name shape, must correspond.
      let swapped := selection.readouts.set! 0 selection.readouts[1]! |>.set! 1 selection.readouts[0]!
      rejects "source.actual_observation" event {claim with escapeInput :=
        {claim.escapeInput with sourceSelection := some {selection with readouts := swapped}}}
    let source ← getConstInfo event.key.theoremName
    let (scope, _) ← (SourceScope.resolve source selection).run 524288
    let failure ← try
      discard <| (SourceScope.reconstruct scope.expanded (mkConst ``True)).run 524288
      pure false
      catch _ => pure true
    unless failure do throwError "weakened Law accepted"
    let result ← try TemplateBinding.validateEvent {event with
        unitName := `Reg.Support.LegacyRelations.System.registration}; pure false
      catch _ => pure true
    unless result do throwError "wrong occurrence unit accepted"
  let some event := events.find? (fun e => e.key.registrationModule ==
    `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot)
    | throwError "missing preemption occurrence"
  let family := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily
  let support := `Reg.Support.LegacyRelations.Preemption
  let arena := mkConst (support ++ `arena)
  let signature := mkConst (support ++ `signature)
  let actual := mkConst (support ++ `actual)
  let bridge := `D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization
  let rejectFinite := fun (rule : String) (candidate : TemplateOccurrenceEvent)
      (a r : Expr) (b : Name) => do
    let reason ← try
      discard <| (SourceFinite.validate candidate a signature r b).run 524288
      pure "accepted"
    catch error => error.toMessageData.toString
    unless reason.contains rule do throwError "expected {rule}, got {reason}"
  rejectFinite "source.finite_bridge" event arena actual (support ++ `registration)
  rejectFinite "source.finite_arena" {event with arena := mkConst ``Unit} arena actual bridge
  rejectFinite "source.finite_statement" {event with statement := mkConst ``True} arena actual bridge
  rejectFinite "source.finite_actual" event arena (mkConst (support ++ `without_cutCause)) bridge
  rejectFinite "source.finite_anchor" event arena
    (mkApp (mkConst (support ++ `without_anchor))
      (mkConst `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.aThenB)) bridge
  let weakLaw ← withLocalDeclD `r (← mkAppM (family ++ `Realization) #[signature]) fun r =>
    mkLambdaFVars #[r] (mkConst ``True)
  let weakArena ← mkAppM (family ++ `Arena.mk) #[signature, weakLaw]
  rejectFinite "source.finite_full_law" event weakArena actual bridge
  rejectFinite "source.finite_unit" {event with unitName := support ++ `actual} arena actual bridge
  let unsafeReason ← try
    discard <| SourceOperands.check event.key.theoremName #[mkConst ``Nat.decEq]
      524288 none none (some event.arena)
    pure "accepted"
    catch error => error.toMessageData.toString
  unless unsafeReason.contains "source.unsafe_or_external" do
    throwError "finite provenance accepted a direct unsafe operand: {unsafeReason}"
  logInfo "[PASS] seven finite projection mutations and direct unsafe operand rejection"
  let preserved := (TemplateBinding.inventory env).filter fun event =>
    #[`Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot,
      `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.TemplateShadow,
      `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot,
      `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow].contains
        event.key.registrationModule
  unless preserved.size == 4 do throwError "four predecessor occurrences missing"
  for event in preserved do
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "predecessor claim missing"
    let record ← TemplateBinding.assess event (some claim)
    unless record.result matches .declaredValidated _ do
      throwError "predecessor registration regressed"
  logInfo "[PASS] all five originals, four predecessor registrations and both catalogs"

end LeanInformationAuditRegTests.LegacyRelationsRegistrationBoundary
