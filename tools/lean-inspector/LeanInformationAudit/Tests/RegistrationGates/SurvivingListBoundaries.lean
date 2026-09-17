import LeanInformationAudit.Tests.RegistrationGates.AllowlistRules

open Lean LeanInformationAudit.RegistrationGates ListMetadataFixtures

-- These assertions identify the independent rejection of proposition-valued
-- list carriers. Removing an equality-only List metadata fence must not turn
-- the remaining rejection into an unexplained or silently untested path.
run_cmd Elab.Command.liftCoreM do
  for (label, holder) in [
      ("PropositionNodupPayload", ``propositionRealization),
      ("LetPropositionNodupPayload", ``letPropositionRealization),
      ("IndexedPropositionNodupPayload", ``indexedRealization),
      ("PropositionMemPayload", ``propositionMemRealization)] do
    let firstTrace := (← getTraces).size
    let actual ← withOptions (·.set `trace.InformationProvenance.check true) <|
      provenanceErrorCurrent (← getEnv).header.mainModule `catalog ``existsTarget holder
    let mut carrierPath := false
    for entry in (← getTraces).toArray[firstTrace:] do
      let message ← entry.msg.toString
      if message.contains "unclassified_abstract_carrier family=List" then
        carrierPath := true
        logInfo m!"[PATH] {label}: {message}"
    logInfo m!"[FULL] {label}: {actual}"
    if actual.any (·.contains "reason=unclassified_form") && carrierPath then
      logInfo m!"[PASS] {label}CarrierPath"
    else logError m!"[FAIL] {label}CarrierPath: expected List carrier rejection; actual={actual}"
