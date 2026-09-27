import LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries
open Lean LeanInformationAudit.RegistrationGates
namespace Round7Extraction
def malformed : Nat := 0
run_cmd Elab.Command.liftCoreM do
  let fresh ← getEnv
  for (label, holder, limit) in [("ExtractionZeroFuel", ``AllowlistBoundaries.template, 0),
      ("MalformedPositiveFuel", ``malformed, provenanceExpressionLimit.get (← getOptions))] do
    withEnv fresh do
      let start := (← getTraces).size
      let actual ← withOptions (fun o => (o.set `provenanceExpressionLimit limit).set
        `trace.InformationProvenance.check true) <|
        provenanceErrorCurrent fresh.header.mainModule `catalog ``AllowlistBoundaries.target holder
      logInfo m!"[FULL] {label}: {actual}"
      let mut cause := false
      for entry in (← getTraces).toArray[start:] do
        let message ← entry.msg.toString
        logInfo m!"[TRACE] {label}: {message}"
        if message.contains "cause=" && message.contains "operation=" &&
            message.contains "first=" && message.contains "site=" then cause := true
      if cause then logInfo m!"[PASS] {label}Cause: exhaustion address and origin"
      else logError m!"[FAIL] {label}Cause: missing cause/operation/first/site"
      let (extracted, work) := ReadoutFamily.extract fresh holder limit
      logInfo m!"[EXTRACTION] {label}: fuel={limit} work={work} found={extracted.isSome} holder={holder}"
      if actual.any (·.contains "reason=incomplete_closure provenance=null") then
        logInfo m!"[PASS] {label}: diagnostic shape"
      else logError m!"[FAIL] {label}: expected incomplete_closure/null; actual={actual}"
end Round7Extraction
