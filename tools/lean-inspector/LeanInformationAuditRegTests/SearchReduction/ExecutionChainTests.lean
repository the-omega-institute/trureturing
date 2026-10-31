import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.ExecutionChainCandidates

/-! D′ execution chains, using isolated test populations and boundary charges.
The production κ/G allocations, loop, replayer, graph evaluator and publisher
are unchanged. This is not production candidate-population calibration. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.ExecutionChainCandidates
set_option Elab.async false

private def testVersion := "Dprime-execution-v1/frozen-allocations/injected-charges"

private unsafe def testIndex (label : String) (easy : Bool) : MetaM DiskLookup.Index := do
  let directory : System.FilePath :=
    s!"build/lean-inspector/search-reduction-test-index/Dprime-v1-{label}-{← IO.monoNanosNow}"
  IO.FS.createDirAll directory
  let env ← getEnv
  let target := mkApp (mkConst ``Target) (mkNatLit 7)
  let helper := mkApp (mkConst ``Helper) (mkNatLit 7)
  let targetKeys ← DiscrTree.mkPath target
  let helperKeys ← DiscrTree.mkPath helper
  let mut tree : DiscrTree DiskLookup.Entry := {}
  let names := #[(``slow, targetKeys), (``viaHelper, targetKeys),
    (``helperSlow, helperKeys)] ++ (if easy then #[(``easy, targetKeys)] else #[])
  for ((name, keys), ordinal) in names.zipIdx do
    let some owner := env.getModuleIdxFor? name | throwError "DPRIME missing fixture owner"
    let entry : DiskLookup.Entry := {
      module := env.header.moduleNames[owner.toNat]!.toString,
      name := name.toString,
      parts := (name.toString.splitOn ".").toArray.map (fun part => (part, 0)), ordinal}
    tree := tree.insertKeyValue keys entry
  pickle (directory / "primary.pickle") ({tree} : DiskLookup.PickledShard)
  -- Empty full-statement membership is explicit and complete in this test domain.
  for bucket in [:256] do
    pickle (directory / s!"members-{bucket}.pickle") ({} : DiskLookup.MembershipPage)
  let identity := hash (testVersion, directory.toString)
  return {
    directory,
    header := {
      scope := "test", basis := testVersion, mathlib := mathlibRevision,
      inputs := identity, storage := ".", root := "", digest := identity,
      complete := true, modules := 1, declarations := names.size,
      indexed := names.size, missing := #[]},
    membership? := some {
      inputs := identity, storage := directory.fileName.get!,
      complete := true, indexed := 0},
    manifest := #[(hash targetKeys[0]!, #["primary.pickle"]),
      (hash helperKeys[0]!, #["primary.pickle"])]}

private unsafe def testTable (mode : String) (easy := true) : MetaM LookupTable := do
  let index ← testIndex mode easy
  let budget ← IO.mkRef ({} : LookupBudgetState)
  return {
    environment := ← getEnv, disk? := some index, fixture := true,
    budget? := some budget,
    boundaryTest? := some fun entry goal => goal.withContext do
      if entry.leanName == ``slow && mode == "kappa" then
        IO.addHeartbeats (lookupCandidateBudget * 1000 + 1)
        checkSystem "DPRIME_KAPPA injected-candidate-charge"
      if entry.leanName == ``slow && mode == "G" then
        budget.modify fun state => {state with coverage := lookupCoverageBudget * 1000}
      if entry.leanName == ``helperSlow && mode == "reverse" then
        let reverse := (← getLCtx).any fun decl => decl.type.isAppOf ``Target
        if reverse then
          IO.addHeartbeats (lookupCandidateBudget * 1000 + 1)
          checkSystem "DPRIME_REVERSE injected-candidate-charge"}

private def testGraph : ProofGraph := {
  root := 0,
  vertices := [
    {id := 0, type := mkApp (mkConst ``Target) (mkNatLit 7)},
    {id := 1, type := mkApp (mkConst ``Helper) (mkNatLit 7),
      structureSeed := true,
      structureProof? := some (mkApp (mkConst ``Helper.intro) (mkNatLit 7))}],
  edges := [{conclusion := 1}, {conclusion := 0, premises := [1]}]}

private def otherGuards (r : GraphReading) : GraphReading :=
  {r with
    isolated := true, structureChecked := true, structureClean := true,
    presentationComplete := true}

private def pairPool : Array CertificateNomination := #[⟨.lookup ``viaHelper, testVersion⟩]

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let table ← testTable "kappa"
  let target := mkApp (mkConst ``Target) (mkNatLit 7)
  let result ← localRebuild target [] (some table) "DPRIME-kappa-successor"
  unless result.lookup.searchKappa && result.lookup.visited ≥ 2 &&
      result.lookup.source? == some ``easy && result.cost == .zero &&
      result.query.price == some 0 && result.proof?.isSome do
    throwError "DPRIME_KAPPA successor kernel Hit lost: {result.detail}"
  checkLocalProof target result.proof?.get!
  logInfo s!"DPRIME_CHAIN kappa-successor PASS version={testVersion} \
    visited={result.lookup.visited} kappa=true kernel_hit=true price=0"

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let table ← testTable "G"
  let cold ← otherGuards <$> evaluateGraph testGraph (some table) pairPool
  let stops := cold.queryRecords.filter (·.encounteredCoveragePrefixG)
  unless !stops.isEmpty && stops.all (fun q =>
      q.terminal == .miss .coveragePrefixG && q.terminal.price == some 1 &&
      q.terminal.guardRun != .exhausted) && budgetBasis cold &&
      better cold.paired.upper cold.baseline.upper do
    throwError "DPRIME_G coverage branch lost stop, price, basis or guard status"
  let target := mkApp (mkConst ``Target) (mkNatLit 7)
  let label ← replayCertificate target [] (.lookup ``easy) (some table)
  unless label.cost == .zero && label.proof?.isSome do
    throwError "DPRIME_G target B-only label failed"
  checkLocalProof target label.proof?.get!
  let control ← otherGuards <$> evaluateGraph testGraph (some table)
    (pairPool.push ⟨.lookup ``easy, testVersion ++ "/target-pool-control"⟩)
  unless classifyDisposition control == .bindOnly && upperIsZero control.baseline &&
      !strictDrop control.baseline control.paired do
    throwError "DPRIME_G target certificate did not erase Delta"
  logInfo s!"DPRIME_CHAIN coverage-pool PASS version={testVersion} \
    stops={stops.length} price=1 basis=budget budget_guard=incomplete \
    target_pool=bind-only Delta=false"

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let table ← testTable "reverse" false
  let reading ← otherGuards <$> evaluateGraph testGraph (some table) pairPool
  let reverse := reading.queryRecords.filter (·.role.startsWith "target-part-reverse:")
  unless !reverse.isEmpty && reading.reverseNegativeCalls > 0 &&
      reverse.any (fun q => q.encounteredSearchKappa &&
        q.terminal == .miss .searchKappa && q.terminal.guardRun != .exhausted) &&
      reading.baseline.upper != .finite 0 && finite reading.baseline.upper &&
      better reading.paired.upper reading.baseline.upper &&
      reading.graph.complete && reading.presentationComplete && reading.isolated &&
      reading.structureChecked && reading.structureClean &&
      !reading.targetPartComplete && classifyDisposition reading == .incomplete do
    throwError "DPRIME_REVERSE truncated scheduled guard acquired a positive verdict"
  let observation : Observation := {
    target := `DprimeReverseTarget, base := reading.baselineProbe.outcome,
    paired := reading.pairedProbe.outcome, verdict := .insufficient, graph? := some reading}
  let text := (observationJson observation).compress
  unless (text.splitOn "target-part").length > 1 do
    throwError "DPRIME_REVERSE incomplete lost its named blocker"
  try
    publish `DprimeReversePublication observation
      (targetHeader? := some ([], mkApp (mkConst ``Target) (mkNatLit 7)))
  catch ex =>
    throwError "DPRIME_REVERSE publication changed incomplete guard: {← ex.toMessageData.toString}"
  let published ← evalConst Disposition `DprimeReversePublication.publishedDisposition
  unless published == .incomplete do
    throwError "DPRIME_REVERSE publisher ignored unfinished guard"
  logInfo s!"DPRIME_CHAIN reverse-incomplete PASS version={testVersion} \
    reverse_calls={reading.reverseNegativeCalls} U_B={reprStr reading.baseline.upper} \
    U_P={reprStr reading.paired.upper} other_guards=complete stop=searchKappa \
    disposition=incomplete blocker=target-part published=incomplete"
