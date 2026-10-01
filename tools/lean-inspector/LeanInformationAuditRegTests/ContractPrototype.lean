/- L0 原型 -/
import LeanInformationAudit.ContractPrototype.Equivalence
import LeanInformationAudit.ContractPrototype.CatalogEquivalence
import LeanInformationAudit.ContractPrototype.UnresolvedEquivalence
import Reg.ContractPrototype.Readout
import Reg.ContractPrototype.DualReadout
import Reg.ContractPrototype.Source
import Reg.ContractPrototype.FiniteSource
import Reg.ContractPrototype.Inline
import Reg.ContractPrototype.Occurrence
import Reg.ContractPrototype.Witness
import Reg.ContractPrototype.IffCatalog
import Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling
import Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain
import Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw
import Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
import Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
import Reg.D5.S3.Resource.VandermondeHyperbolicRefutation
import Reg.Catalogs.IffRegistrations

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit

private def pairs : Array (Name × Name) := #[
  (`Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, `Reg.ContractPrototype.Readout),
  (`Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain, `Reg.ContractPrototype.DualReadout),
  (`Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, `Reg.ContractPrototype.Source),
  (`Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, `Reg.ContractPrototype.FiniteSource),
  (`Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion, `Reg.ContractPrototype.Inline),
  (`Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative, `Reg.ContractPrototype.Occurrence),
  (`Reg.D5.S3.Resource.VandermondeHyperbolicRefutation, `Reg.ContractPrototype.Witness),
  (`Reg.Catalogs.IffRegistrations, `Reg.ContractPrototype.IffCatalog),
  (`Reg.Support.DependentFamily, `Reg.ContractPrototype.Templates.DependentFamily),
  (`Reg.Support.SharedArenaPeers, `Reg.ContractPrototype.Templates.Intervention),
  (`Reg.Support.IffRegistrations, `Reg.ContractPrototype.Templates.Iff)]

private def phase (name : String) : IO Unit := do
  if let some path ← IO.getEnv "STRATALINT_CONTRACT_PROTOTYPE_PHASE" then
    IO.FS.writeFile path name

private def reportAt (reports : Array (Json × Array Name × Environment)) (index : Nat) :
    MetaM (Json × Array Name × Environment) := do
  let some value := reports[index]? | throwError "missing report index {index}"
  return value

/-- Sample phase boundaries with the same process-tree reader as the existing
resource profiler. The periodic profiler supplies interior samples. -/
private def rssSample : IO (Option Nat) := do
  let some profiler ← IO.getEnv "STRATALINT_CONTRACT_PROTOTYPE_PROFILER" | return none
  let pid ← IO.Process.getPID
  let reading ← IO.Process.output {
    cmd := "python3"
    args := #["-B", "-c",
      "import pathlib,sys; sys.path.insert(0,str(pathlib.Path(sys.argv[1]).parent)); " ++
        "from resources import process_tree; print(max(process_tree(int(sys.argv[2])).values(),default=0))",
      profiler, toString pid] }
  unless reading.exitCode == 0 do throw <| IO.userError reading.stderr
  let some value := reading.stdout.trimAscii.toString.toNat?
    | throw <| IO.userError "invalid profiler RSS sample"
  return some value

run_cmd do
  let env := (← getEnv).setExporting false
  setEnv env
  let targets := pairs.flatMap fun (a,b) => #[a,b]
  phase "recorder_capture"
  let recorderBefore ← rssSample
  let started ← IO.monoNanosNow
  let recorderCount := (RegistrationInputs.owned env).size + (TemplateEnrollmentInputs.owned env).size +
    (SealInputs.owned env).size + (RootCatalogs.owned env).size + (ExpectedOccurrenceManifest.owned env).size
  let recorderNs := (← IO.monoNanosNow) - started
  let recorderAfter ← rssSample
  let (snapshot, reports, discoveryBefore, discoveryAfter) ← liftTermElabM do
    phase "typed_discovery"
    let discoveryBefore ← rssSample
    let snapshot ← ContractPrototype.discover targets
    let discoveryAfter ← rssSample
    phase "assessment"
    let owners := snapshot.registrations.map Prod.fst ++ snapshot.enrollments.map Prod.fst ++
      snapshot.seals.map Prod.fst ++ snapshot.roots.map Prod.fst ++ snapshot.expected.map Prod.fst
    let reports ← assessReportTargets targets (owners ++ recordedInputOwners env) fun target => do
      phase ("assessment:" ++ target.toString)
      if owners.any (reachableModules env target).contains then
        ContractPrototype.replay target snapshot
      else assessRecordedRegistrations target
      return registeredKeys (← getEnv) target
    return (snapshot, reports, discoveryBefore, discoveryAfter)
  phase "equivalence"
  let comparisons ← liftTermElabM do
    let mut checked := #[]
    let mapping := pairs.push (`Reg.Support.LegacyRelations.System, `Reg.ContractPrototype.SystemFamily)
    for index in [:7] do
      let (oldTarget, newTarget) := pairs[index]!
      let some (_, _, oldEnv) := reports[2 * index]? | throwError "missing original report"
      let some (_, _, newEnv) := reports[2 * index + 1]? | throwError "missing prototype report"
      let oldRecords := (TemplateBinding.records oldEnv).filter (·.occurrence.key.registrationModule == oldTarget)
      let newRecords := (TemplateBinding.records newEnv).filter (·.occurrence.key.registrationModule == newTarget)
      unless oldRecords.size == 1 && newRecords.size == 1 do
        throwError "sample expected one record: {oldTarget}/{newTarget}"
      let result ← try
        if oldRecords[0]!.result matches .declaredUnresolved _ then
          ContractPrototype.UnresolvedEquivalence.verifyRecord
            oldEnv newEnv mapping oldRecords[0]! newRecords[0]!
        else
          ContractPrototype.Equivalence.verifyRecord oldEnv newEnv mapping oldRecords[0]! newRecords[0]!
      catch error =>
        pure <| Json.mkObj [("status", toJson "failed"), ("error", toJson (← error.toMessageData.toString))]
      checked := checked.push <| Json.mkObj [("original", toJson oldTarget.toString),
        ("prototype", toJson newTarget.toString), ("result", result)]
    return checked
  let catalogComparisons ← liftTermElabM do
    let mapping := pairs.push (`Reg.Support.LegacyRelations.System, `Reg.ContractPrototype.SystemFamily)
    let mut checked := #[]
    let templates : Array (Nat × Name) := #[
      (8, `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize),
      (9, `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.interventionFiniteRealization),
      (9, `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.observationFiniteRealization),
      (10, `D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization)]
    for (index, template) in templates do
      let (_, _, oldEnv) ← reportAt reports (2 * index)
      let (_, _, newEnv) ← reportAt reports (2 * index + 1)
      let result ← ContractPrototype.CatalogEquivalence.verifyTemplate
        oldEnv newEnv mapping template template
      checked := checked.push <| Json.mkObj [("variant", toJson "template"),
        ("template", toJson template.toString), ("result", result)]
    let (_, _, oldEnv) ← reportAt reports 14
    let (_, _, newEnv) ← reportAt reports 15
    let root ← ContractPrototype.CatalogEquivalence.verifyRoot oldEnv newEnv mapping pairs[7]!.1 pairs[7]!.2
    let sealResult ← ContractPrototype.CatalogEquivalence.verifySeal
      oldEnv newEnv mapping pairs[7]!.1 pairs[7]!.2
    return checked ++ #[Json.mkObj [("variant", toJson "root"), ("result", root)],
      Json.mkObj [("variant", toJson "seal"), ("result", sealResult)]]
  let rows ← reports.zip targets |>.mapM fun ((binding, generated, assessed), target) => do
    let sealed ← liftTermElabM do
      setEnv assessed
      serializeSealArtifact (SealRecords.forRoot assessed target)
    return Json.mkObj [("target", toJson target.toString), ("binding", binding),
      ("generated", toJson (generated.map Name.toString)), ("seal", ← ofExcept (Json.parse sealed))]
  let closures := pairs.map fun (_, target) => Id.run do
    let names := (reachableModules env target).toArray.qsort Name.quickLt
    let forbidden := names.filter fun name =>
      (`LeanInformationAudit).isPrefixOf name ||
      ((`LeanInformationAuditInterface).isPrefixOf name &&
        !(`LeanInformationAuditInterface.Contract).isPrefixOf name)
    return Json.mkObj [("target", toJson target.toString), ("module_count", toJson names.size),
      ("forbidden", toJson (forbidden.map Name.toString)), ("modules", toJson (names.map Name.toString))]
  unless closures.all (fun row => (row.getObjValAs? (Array String) "forbidden").toOption == some #[]) do
    throwError "prototype imports judge code"
  phase "single_target_consistency"
  let isolated ← liftTermElabM do
    let mut checked := #[]
    for index in [:pairs.size] do
      let target := pairs[index]!.2
      withCurrHeartbeats do
        setEnv env
        let single ← ContractPrototype.reports #[target]
        let (singleBinding, singleGenerated, singleEnv) ← reportAt single 0
        let (batchBinding, batchGenerated, batchEnv) ← reportAt reports (2 * index + 1)
        unless singleBinding == batchBinding && singleGenerated == batchGenerated do
          throwError "prototype single/batch mismatch: {target}"
        setEnv singleEnv
        let singleSeal ← serializeSealArtifact (SealRecords.forRoot singleEnv target)
        setEnv batchEnv
        let batchSeal ← serializeSealArtifact (SealRecords.forRoot batchEnv target)
        unless singleSeal == batchSeal do throwError "prototype single/batch seal mismatch: {target}"
      checked := checked.push target.toString
    setEnv env
    return checked
  let result := Json.mkObj [("rows", toJson rows), ("closures", toJson closures),
    ("comparisons", toJson comparisons), ("catalog_comparisons", toJson catalogComparisons),
    ("single_batch_equal", toJson isolated),
    ("discovery", Json.mkObj [("scanned", toJson snapshot.scanned), ("hits", toJson snapshot.hits),
      ("elapsed_ms", toJson snapshot.elapsedMs), ("rss_before_bytes", toJson discoveryBefore),
      ("rss_after_bytes", toJson discoveryAfter)]),
    ("recorder_capture", Json.mkObj [("records", toJson recorderCount), ("elapsed_ns", toJson recorderNs),
      ("rss_before_bytes", toJson recorderBefore), ("rss_after_bytes", toJson recorderAfter)])]
  let output ← IO.getEnv "STRATALINT_CONTRACT_PROTOTYPE_OUTPUT"
  match output with
  | some path => IO.FS.writeFile path (result.pretty ++ "\n")
  | none => logInfo m!"{result.compress}"
  unless comparisons.all (fun row =>
      (row.getObjVal? "result" >>= (·.getObjValAs? Bool "verified")).toOption == some true) do
    throwError "prototype registration equivalence failed"
