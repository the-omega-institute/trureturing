/- L0 原型 -/
import LeanInformationAudit.ContractPrototype.Equivalence
import LeanInformationAuditRegTests.ContractMapping
import LeanInformationAuditRegTests.ContractIndependent
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
import Reg.ContractPrototype.ValidWitness
import Reg.ContractPrototype.Controls.Witness
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
  (`Reg.Support.IffRegistrations, `Reg.ContractPrototype.Templates.Iff),
  (`Reg.ContractPrototype.Controls.Witness, `Reg.ContractPrototype.ValidWitness)]

private def authorizedMapping : ContractPrototype.Equivalence.NameMapping :=
  pairs ++ #[
    (`Reg.Support.LegacyRelations.System, `Reg.ContractPrototype.SystemFamily),
    (`Reg.Support.BoundedRunSpace, `Reg.ContractPrototype.Templates.Cut),
    (`Reg.Support.CounterexampleRecord, `Reg.ContractPrototype.Templates.Counterexample)]

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
    let mapping := authorizedMapping
    for index in #[0,1,2,3,4,5,6,11] do
      let (oldTarget, newTarget) := pairs[index]!
      let (_, _, oldEnv) ← reportAt reports (2 * index)
      let (_, _, newEnv) ← reportAt reports (2 * index + 1)
      let oldRecords := (TemplateBinding.records oldEnv).filter (·.occurrence.key.registrationModule == oldTarget)
      let newRecords := (TemplateBinding.records newEnv).filter (·.occurrence.key.registrationModule == newTarget)
      unless !oldRecords.isEmpty do
        throwError "contract.pairing:empty_source:{oldTarget}"
      if index == 11 then
        unless oldRecords.size == 3 do throwError "witness_multi_registration_count"
        for record in oldRecords do
          if record.occurrence.key.theoremName == `Reg.ContractPrototype.Fixtures.Witness.third then
            unless record.result matches .undeclared do throwError "witness_missing_control_state"
          else
            unless record.result matches .declaredValidated _ do
              throwError "witness_positive_control_not_validated"
            let expectedKind := if record.occurrence.key.theoremName ==
                `Reg.ContractPrototype.Fixtures.Witness.result then "witness" else "open"
            unless record.escape.bridgeKind == "witness" &&
                record.escape.continuation.map (·.kind) == some expectedKind do
              throwError "witness_continuation_control_kind"
      let recordMapping ← ContractPrototype.Equivalence.privateMapping oldEnv newEnv mapping
      let paired ← ContractPrototype.Equivalence.pairRecords recordMapping oldRecords newRecords
      let authorization := LeanInformationAuditRegTests.ContractMapping.inlineAuthorization mapping
      for (oldRecord, newRecord) in paired do
        phase ("equivalence:" ++ oldRecord.occurrence.key.theoremName.toString)
        let result ← withCurrHeartbeats <| match oldRecord.result with
          | .declaredUnresolved _ =>
            ContractPrototype.UnresolvedEquivalence.verifyRecord oldEnv newEnv authorization oldRecord newRecord
          | .undeclared =>
            ContractPrototype.Equivalence.verifyMissingRecord oldEnv newEnv authorization oldRecord newRecord
          | .declaredValidated _ =>
            ContractPrototype.Equivalence.verifyRecord oldEnv newEnv authorization oldRecord newRecord
        checked := checked.push <| Json.mkObj [("original", toJson oldTarget.toString),
          ("prototype", toJson newTarget.toString), ("result", result)]
    return checked
  let mappingTests ← liftTermElabM do
    let (_, _, oldEnv) ← reportAt reports 8
    let (_, _, newEnv) ← reportAt reports 9
    let oldRecord := ((TemplateBinding.records oldEnv).filter
      (·.occurrence.key.registrationModule == pairs[4]!.1))[0]!
    let newRecord := ((TemplateBinding.records newEnv).filter
      (·.occurrence.key.registrationModule == pairs[4]!.2))[0]!
    LeanInformationAuditRegTests.ContractMapping.run oldEnv newEnv
      (authorizedMapping)
      oldRecord newRecord
  let catalogComparisons ← liftTermElabM do
    let mapping := authorizedMapping
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
    let (_, _, extraOld) ← reportAt reports 22
    let (_, _, extraNew) ← reportAt reports 23
    let extraRoot ← ContractPrototype.CatalogEquivalence.verifyRoot
      extraOld extraNew mapping pairs[11]!.1 pairs[11]!.2
    return checked ++ #[Json.mkObj [("variant", toJson "distinct_snapshots"), ("result", extraRoot)],
      Json.mkObj [("variant", toJson "root"), ("result", root)],
      Json.mkObj [("variant", toJson "seal"), ("result", sealResult)]]
  let rows ← reports.zip targets |>.mapM fun ((binding, generated, assessed), target) => do
    let (sealed, inventory) ← liftTermElabM do
      setEnv assessed
      let sealed ← serializeSealArtifact (SealRecords.forRoot assessed target)
      let inventory ← LeanInformationAuditRegTests.ContractIndependent.generatedInventory generated
      return (sealed, inventory)
    return Json.mkObj [("target", toJson target.toString), ("binding", binding),
      ("generated", toJson (generated.map Name.toString)), ("generated_declarations", inventory),
      ("seal_bytes", toJson sealed), ("seal", ← ofExcept (Json.parse sealed))]
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
  let result := Json.mkObj [("rows", toJson rows), ("closures", toJson closures),
    ("mapping_tests", toJson mappingTests), ("comparisons", toJson comparisons), ("catalog_comparisons", toJson catalogComparisons),
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
