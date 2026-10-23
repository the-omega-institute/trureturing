import LeanInformationAuditRegAnalysis.SearchReduction.Commands

open Lean Meta Elab Command LeanInformationAudit.SearchReduction

set_option Elab.async false
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  for good in ["by_close", "by_lookup Nat.add_comm", "by_member Nat.add_comm"] do
    unless (Parser.runParserCategory env `obvious_certificate good).isOk do
      throwError "certificate grammar rejected {good}"
  for (label, bad) in [
      ("term-slot", "by_close (by trivial)"),
      ("explicit-witness", "by_lookup ⟨42,rfl⟩"),
      ("lemma-list", "by_lookup [Nat.add_comm, Nat.add_assoc]"),
      ("tactic-slot", "by omega"),
      ("direction-slot", "by_lookup Nat.add_comm reverse")] do
    unless !(Parser.runParserCategory env `obvious_certificate bad).isOk do
      throwError "mutation accepted: {label}"
    logInfo s!"CERT_MUTATION rejected {label}"
  let a : CertificateNomination := ⟨.lookup `Nat.add_comm, "LLM/frozen-model/template/1"⟩
  let b : CertificateNomination := ⟨.close, "R-hit"⟩
  unless nominationCertificates #[a,b,a] == nominationCertificates #[b,a] do
    throwError "nomination order or repetition changed certificate pool"
  liftTermElabM do
    let failed ← certifyLocal (mkConst ``False)
    unless failed.cost == .unknown && failed.proof?.isNone do
      throwError "mutation accepted: attack_failure_cost_one"
    logInfo "CERT_MUTATION rejected attack_failure_cost_one"
    let closed ← replayCertificate (mkConst ``True) [] .close
    unless closed.cost == .zero && closed.proof?.isSome do
      throwError "frozen closure certificate failed"
    let capped ← boundedRebuildBranch do
      IO.addHeartbeats (localBudget * 1000 + 1000000)
      checkSystem "certificate-test/capped"
      return {cost := .zero}
    unless capped.cost == .unknown && capped.proof?.isNone do
      throwError "mutation accepted: capped_zero"
    logInfo "CERT_MUTATION rejected capped_zero"
    for name in [`CertificateTests.target, `CertificateTests.structure,
        `CertificateTests.polluted, `Nat.exists_mul_self] do
      let result ← replayCertificate (mkConst ``False) [] (.lookup name)
      unless result.cost == .unknown && result.proof?.isNone do
        throwError "mutation accepted: unregistered-or-out-of-scope {name}"
    logInfo "CERT_MUTATION rejected unregistered-or-out-of-scope"

#search_reduction_certificates [by_close, by_lookup Nat.add_comm, by_member Nat.add_comm]
#search_reduction_nominations "LLM/frozen-model/template/1" [Nat.add_comm, Nat.add_assoc]
