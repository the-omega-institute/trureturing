import Reg.D5.S3.Combinatorics.Graph.OctahedralCochainSharpness
import Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair
import LeanInformationAuditRegTests.SourceIdentity

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.GraphSourceContract

set_option trace.InformationRegistration.check true

private def assessOriginals (enabled : Bool) : MetaM Unit :=
    withOptions (smartUnfolding.set · enabled) do
  let names := #[
    `D5.S3.Combinatorics.Graph.OctahedralCochainSharpness.antipodal_repair_sharpness,
    `D5.S3.Combinatorics.Graph.TripartiteH1Repair.ker_d1_eq_im_d0,
    `D5.S3.Combinatorics.Graph.TripartiteH1Repair.sharp_three_edge_witness,
    `D5.S3.Combinatorics.Graph.TripartiteH1Repair.universal_repair]
  let options ← getOptions
  for name in names do
    let env ← getEnv
    let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == name)
      | throwError "missing original event: {name}"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "missing original claim: {name}"
    let before := (TemplateBinding.observedAssessments env).size
    let start ← IO.getNumHeartbeats
    let record ← TemplateBinding.assess event (some claim)
    let cost := (← IO.getNumHeartbeats) - start
    unless (TemplateBinding.observedAssessments (← getEnv)).size == before + 1 do
      throwError "assessment unexpectedly reused cached verdict: {name}"
    let .declaredValidated certificate := record.result
      | throwError "original failed: {(← TemplateBinding.recordJson record).compress}"
    let some (_, original) := (TemplateBinding.importedRecords env).find?
        (·.2.occurrence.key == event.key)
      | throwError "missing native original record: {name}"
    let .declaredValidated native := original.result
      | throwError "native original was not validated: {name}"
    unless certificate.evidenceRef == native.evidenceRef do
      throwError "cache/option order changed evidence identity: {name}"
    unless certificate.sourceBinding.isSome && record.escape.fromObject.isSome &&
        record.escape.bridgeKind == "source-equivalence" &&
        record.escape.continuation.any (·.kind == "open") do
      throwError "missing original four slots: {name}"
    unless (← getOptions) == options do throwError "assessment leaked options"
    -- Full source contamination must still reject; the beta form explicitly
    -- reaches the modified branch instead of the raw equality shortcut.
    TemplateAudit.withCumulativeBudget do
      let statement := (← getConstInfo name).type
      let disguised := mkApp (.lam `p (mkSort .zero) (.bvar 0) .default) statement
      let initial ← RegistrationGates.argumentIdentityState name 524288
      let (_, identity) ← (RegistrationGates.argumentIdentityNode env disguised
        (deferStatementApart := true)).run initial
      unless identity.unclassified.isSome && !identity.forbidden && !identity.incomplete do
        throwError "original identity control missed conversion: {name}"
      let discarded := mkApp (.lam `ignored (mkSort .zero) (mkNatLit 0) .default) disguised
      for operand in #[statement, disguised, discarded] do
        let diagnostic ← try
          discard <| SourceOperands.check name #[operand] 524288
          pure "accepted"
        catch error => error.toMessageData.toString
        unless diagnostic.contains "forbidden_dependency:source.operand_identity" do
          throwError "original identity control: {name}: {diagnostic}"
      logInfo m!"[PASS] graph_identity_and_raw_taint {name}"
    logInfo m!"GRAPH_ASSESSMENT option={enabled} theorem={name} internal_heartbeats={cost} evidence_ref={certificate.evidenceRef}"

run_meta withFreshCache do
  assessOriginals true
  assessOriginals false
  assessOriginals true
run_meta withFreshCache do
  assessOriginals false
  assessOriginals true
  assessOriginals false

end LeanInformationAuditRegTests.GraphSourceContract
