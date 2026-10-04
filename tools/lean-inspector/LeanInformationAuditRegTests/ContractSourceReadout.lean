import Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
import Reg.D5.S1.Words.Attractors.FiniteWordAttractors
import LeanInformationAudit.Tests.Assessment
import LeanInformationAuditRegTests.ContractAssertions

test_imported_assessment

namespace LeanInformationAuditRegTests.ContractSourceReadout
open Lean Meta Elab Term LeanInformationAudit
open LeanInformationAuditRegTests.ContractGuards
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

private def period :=
  ``D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.period_classification
private def attractor := ``D5.S1.Words.Attractors.attractor_minimum

run_meta do
  for (label, target) in #[("period", period), ("attractor", attractor)] do
    let env ← getEnv
    let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == target)
      | throwError "setup: source occurrence missing"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "setup: source claim missing"
    let record ← TemplateBinding.assess event (some claim)
    assertTest s!"source_readout.{label}_validated" (match record.result with
      | .declaredValidated certificate => certificate.sourceBinding.isSome
      | _ => false)
    if let .declaredUnresolved diagnostic := record.result then logInfo diagnostic
    let opened ← TemplateBinding.assess event
      (some { claim with descriptor := some (.bvar 0) })
    assertTest s!"source_readout.{label}_open_rejected" (match opened.result with
      | .declaredUnresolved diagnostic => (diagnostic.splitOn "dtr.descriptor_open").length > 1
      | _ => false)
  let unsafeRejected ← try
    discard <| SourceOperands.check period #[mkConst ``Nat.pow] 524288
    pure false
  catch error =>
    pure (((← error.toMessageData.toString).splitOn "source.unsafe_or_external").length > 1)
  assertTest "source_readout.external_operand_rejected" unsafeRejected

run_elab do
  let env ← getEnv
  let some (_, claim) := (TemplateBinding.ownedClaims env).find?
    (·.2.key.theoremName == attractor) | throwError "setup: attractor claim"
  let some typed := claim.descriptor | throwError "setup: attractor descriptor"
  let old ← elabTerm (← `(term|
    realize
      _root_.Reg.D5.S1.Words.Attractors.FiniteWordAttractors.HelperAudits.Minimum.signature
      (fun _ _ w => _root_.D5.S1.Words.Attractors.gamma w) (fun e => nomatch e))) none
  synthesizeSyntheticMVarsNoPostponing
  let old ← instantiateMVars old
  assertTest "source_readout.attractor_old_unconstrained_universe"
    (old.hasLevelMVar && !old.hasExprMVar && !old.hasFVar && !old.hasLooseBVars)
  logInfo m!"ATTRACTOR_CLOSURE expr_mvar={old.hasExprMVar} level_mvar={old.hasLevelMVar} \
    fvar={old.hasFVar} loose_bvar={old.hasLooseBVars}"
  assertTest "source_readout.attractor_compiled_closed"
    (!typed.hasMVar && !typed.hasFVar && !typed.hasLooseBVars)
  withOptions (fun o => o.setBool `pp.all true) do
    logInfo m!"ATTRACTOR_DESCRIPTOR_OLD {old}"
  assertTest "source_readout.attractor_same_meaning" (← isDefEq old typed)
  let resolved ← instantiateMVars old
  assertTest "source_readout.attractor_resolved_closed"
    (!resolved.hasMVar && !resolved.hasFVar && !resolved.hasLooseBVars)
  withOptions (fun o => o.setBool `pp.all true) do
    logInfo m!"ATTRACTOR_DESCRIPTOR_RESOLVED {resolved}"
    logInfo m!"ATTRACTOR_DESCRIPTOR_TYPED {typed}"

end LeanInformationAuditRegTests.ContractSourceReadout
