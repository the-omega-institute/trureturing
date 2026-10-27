import Mathlib.Util.SynthesizeUsing
import LeanInformationAuditRegAnalysis.SearchReduction.Isolation
import LeanInformationAuditRegAnalysis.SearchReduction.Information
import LeanInformationAuditRegAnalysis.SearchReduction.CacheDependencies

/-! Compiled Lean probe commands and a print-only JSON projection. -/

namespace LeanInformationAudit.SearchReduction
open Lean Meta Elab Command Tactic
open LeanInformationAudit.SearchReduction (Run Verdict)

-- Checked declarations retain expression storage until the compiler exits.
private initialize probeRegions : IO.Ref (Array CompactedRegion) ← IO.mkRef #[]

/-- Request payloads share one immutable Lean import. Target declarations and
result values are added only to a fresh persistent-environment fork. -/
private initialize requestEnvironment : IO.Ref (Option Environment) ← IO.mkRef none

/-- Module bytes are immutable. The common import state contains only Mathlib;
source and baseline fork it before independently initializing extension state. -/
private unsafe def importSource (owners : Array Import) : IO (Environment × ImportState × ImportState) := do
  enableInitializersExecution
  withImporting do
    let (_, shared) ← (importModulesCore #[{module := `Mathlib}]).run default
    let (_, sourceState) ← (importModulesCore owners).run shared
    let source ← finalizeImport sourceState owners options 0
      (leakEnv := false) (loadExts := true)
    return (source, shared, sourceState)

/-- The nested negative replay shares this probe's immutable module bytes.
The reference is cleared before returning; it never caches across targets. -/
private initialize activeProbe : IO.Ref (Option (Environment × ImportState)) ← IO.mkRef none
private initialize activeReferenceRequest : IO.Ref (Option Request) ← IO.mkRef none
private initialize activeReferenceFixture : IO.Ref Bool ← IO.mkRef false

private initialize submittedCertificates : IO.Ref (Array CertificateNomination) ← IO.mkRef #[]
private initialize submittedEdgeCertificates : IO.Ref (Array (Name × CertificateNomination)) ← IO.mkRef #[]

syntax (name := certificatePoolCmd) "#search_reduction_certificates "
  "[" obvious_certificate,* "]" : command

@[command_elab certificatePoolCmd] def elabCertificatePool : CommandElab := fun stx => do
  let `(#search_reduction_certificates [$cs:obvious_certificate,*]) := stx
    | throwUnsupportedSyntax
  let certificates ← cs.getElems.mapM fun c =>
    match parseObviousCertificate c with
    | .ok value => pure ({certificate := value, provenance := "author"} : CertificateNomination)
    | .error message => throwError "{message}"
  submittedCertificates.set certificates
  submittedEdgeCertificates.set #[]

syntax (name := edgeCertificatePoolCmd) "#search_reduction_edge_certificates " ident
  "[" obvious_certificate,* "]" : command

@[command_elab edgeCertificatePoolCmd] def elabEdgeCertificatePool : CommandElab := fun stx => do
  let `(#search_reduction_edge_certificates $owner:ident [$cs:obvious_certificate,*]) := stx
    | throwUnsupportedSyntax
  let certificates ← cs.getElems.mapM fun c =>
    match parseObviousCertificate c with
    | .ok value => pure (owner.getId, ({certificate := value, provenance := "author"} : CertificateNomination))
    | .error message => throwError "{message}"
  submittedEdgeCertificates.modify (· ++ certificates)

syntax (name := nominationPoolCmd) "#search_reduction_nominations " str "[" ident,* "]" : command

@[command_elab nominationPoolCmd] def elabNominationPool : CommandElab := fun stx => do
  let `(#search_reduction_nominations $source:str [$names:ident,*]) := stx
    | throwUnsupportedSyntax
  submittedCertificates.modify (· ++ nominateNames (names.getElems.map (·.getId)) source.getString)

/-- Replays use an already loaded source snapshot and restore an enclosing
probe context even when the negative guard raises an exception. -/
def withReferenceProbeContext {m : Type → Type} [Monad m]
    [MonadLiftT (ST IO.RealWorld) m]
    [MonadFinally m] {α : Type} (source : Environment) (shared : ImportState)
    (action : m α) (request? : Option Request := none) (fixture : Bool := false) : m α := do
  let previous ← activeProbe.get
  let previousRequest ← activeReferenceRequest.get
  let previousFixture ← activeReferenceFixture.get
  activeProbe.set (some (source, shared))
  activeReferenceRequest.set request?
  activeReferenceFixture.set fixture
  try action
  finally
    activeProbe.set previous
    activeReferenceRequest.set previousRequest
    activeReferenceFixture.set previousFixture


private def runJson : Run → Json
  | .found => toJson "found"
  | .exhausted => toJson "exhausted"
  | .incomplete failure => Json.mkObj [("incomplete", toJson (reprStr failure))]

private def verdictName : Verdict → String
  | .bindOnly => "bind-only[G,R_lookup,k; scope=B_T]"
  | .nonBindOnly => "non-bind-only[G,R_lookup,k; scope=B_T]"
  | .insufficient => "insufficient-evidence"

private def attemptJson (a : Attempt) : Json := Json.mkObj [
  ("strategy", toJson a.strategy), ("outcome", runJson a.outcome),
  ("axioms", toJson (a.axioms.map Name.toString)), ("detail", toJson a.detail),
  ("internal_heartbeats", toJson a.heartbeats)]

private def boundJson : Bound → Json
  | .finite n => toJson n
  | .top => toJson "infinity"

private def intervalJson (i : Interval) : Json := Json.mkObj [
  ("lower", boundJson i.lower), ("upper", boundJson i.upper)]

private def dispositionName : Disposition → String
  | .bindOnly => "bind-only"
  | .reductionR => "reduction_R"
  | .noGainR => "no-gain_R"
  | .reject => "reject"
  | .incomplete => "incomplete"

private def queryJson (q : RQuery) : Json := Json.mkObj [
  ("terminal", toJson (match q with
    | .hit _ => "Hit" | .miss _ => "Miss_R" | .fault _ => "Fault" | .notRun => "NotRun")),
  ("stop", toJson (match q with | .miss stop => some (reprStr stop) | _ => none)),
  ("fault", toJson (match q with | .fault reason => some reason | _ => none)),
  ("certificate", toJson (match q with | .hit cert => some cert.render | _ => none)),
  ("v18_price", toJson q.priceV18), ("v19_price", toJson q.price),
  ("guard_completion", runJson q.guardRun)]

private def mappingJson (r : GraphReading) : Json := Json.mkObj [
  ("verdict", toJson (dispositionName (classifyDisposition r))),
  ("legacy_verdict", toJson (reprStr (classifyGraph r))),
  ("closure", toJson ((classifyClosure r).map fun c =>
    match c with | .zero => "zero" | .partial_ => "partial")),
  ("baseline_interval", intervalJson r.baseline), ("paired_interval", intervalJson r.paired),
  ("basis", toJson (if budgetBasis r then "budget" else "exhaustive")),
  ("admission", toJson (if budgetBasis r then "Observe-only; not a section 3.2 admission basis"
    else "separate section 3.2 review required"))]

/-- Deterministic first blocker. Additional diagnostics never replace this
unique operation-level reason or turn an incomplete guard into no-gain. -/
private def blockerJson (r : Observation) : Json := Id.run do
  let block (guard query stop remedy : String) := Json.mkObj [
    ("guard", toJson guard), ("query_or_check_pair", toJson query),
    ("stop", toJson stop), ("remedy", toJson remedy),
    ("disposition", toJson "reduction not certified; no admission")]
  let some g := r.graph? | return block "isolation" r.target.toString r.reason "complete the named isolation operation"
  if classifyDisposition g != .incomplete then return Json.null
  if !g.isolated then return block "isolation" r.target.toString r.reason "complete isolation"
  if !g.presentationComplete then
    return block "single-source-presentation" r.target.toString r.presentationDetail "complete this presentation check"
  if !g.structureChecked || !g.structureClean then
    return block "wide-S-and-source-isolation" r.target.toString r.reason "complete the named reconstruction or restatement unit"
  if !g.graph.complete then
    return block "graph-extraction" r.target.toString (reprStr g.graph.issues) "resolve the named extraction operation"
  if !g.targetPartComplete then
    for id in g.selectedSeeds do
      if let some v := g.graph.vertices.find? (·.id == id) then
        if let .incomplete _ := targetPartDecision v.independentLookup v.reverseLookup then
          return block "target-part" s!"{r.target}:seed:{id}"
            s!"independent={v.independentLookupDetail};reverse={v.reverseLookupDetail}"
            "supply a permitted positive certificate or complete the reverse exhaustive guard"
  for q in g.queryRecords do
    if q.terminal.price.isNone then
      return block "R-pricing" s!"{q.role}:{q.target}" (reprStr q.terminal) "complete this faulted or unscheduled query"
  return block "numerical-evidence" r.target.toString "intervals do not decide reduction or no-gain"
    "complete the remaining named author-edge queries"

private def graphJson (r : GraphReading) : Json := Json.mkObj [
  ("lookup_backend", toJson "B_T implication without imports; full B0 alpha membership; typed R v19 terminals"),
  ("A1", mappingJson (priceMappingV18 r)), ("B", mappingJson r),
  ("basis", toJson (if budgetBasis r then "budget" else "exhaustive")),
  ("query_records", toJson (r.queryRecords.map fun q => Json.mkObj [
    ("role", toJson q.role), ("target_hash", toJson q.target),
    ("premise_hashes", toJson q.premises), ("execution", queryJson q.terminal),
    ("encountered_search_kappa", toJson q.encounteredSearchKappa),
    ("encountered_coverage_prefix_G", toJson q.encounteredCoveragePrefixG),
    ("encountered_faults", toJson q.encounteredFaults)])),
  ("certificate_language", toJson certificateLanguageVersion),
  ("certificate_pool_digest", toJson (hash (reprStr
    (nominationCertificates r.certificatePool, canonicalCertificateBindings r.certificateBindings)))),
  ("given_ablation", toJson "optional; unset SEARCH_REDUCTION_GIVEN_ABLATION reuses checked cut certificates only"),
  ("star_fallback", toJson "excluded"),
  ("negative_R_requests", toJson r.negativeCalls),
  ("target_part_reverse_R_requests", toJson r.reverseNegativeCalls),
  ("paired_negative_R_requests", toJson (0 : Nat)),
  ("lookup_enabled", toJson r.lookupEnabled),
  ("lookup_basis_complete", toJson r.lookupBasisComplete),
  ("sharing_configuration", toJson sharingConfiguration),
  ("k", toJson r.k), ("vertices", toJson r.graph.vertices.length),
  ("edges", toJson r.graph.edges.length),
  ("baseline_edges", toJson (r.graph.edges.filter (fun edge => edgeActive edge)).length),
  ("paired_edges", toJson (r.graph.edges.filter (fun edge => edgeActive edge true)).length),
  ("complete", toJson r.graph.complete),
  ("issues", toJson r.graph.issues),
  ("declarations", toJson (r.graph.vertices.map fun v => Json.mkObj [
    ("id", toJson v.id), ("constant", toJson (v.origin.constName?.map Name.toString)),
    ("seed", toJson v.seed), ("structure_seed", toJson v.structureSeed),
    ("target_part", toJson v.targetPart), ("opaque", toJson v.opaqueDecl),
    ("independent_lookup", runJson v.independentLookup),
    ("independent_lookup_detail", toJson v.independentLookupDetail),
    ("reverse_lookup", runJson v.reverseLookup),
    ("reverse_lookup_detail", toJson v.reverseLookupDetail)])),
  ("presentation_complete", toJson r.presentationComplete),
  ("baseline_interval", intervalJson r.baseline),
  ("paired_interval", intervalJson r.paired),
  ("baseline_k1", intervalJson r.baselineK1), ("paired_k1", intervalJson r.pairedK1),
  ("baseline_visible", intervalJson r.baselineVisible), ("paired_visible", intervalJson r.pairedVisible),
  ("baseline_probe", runJson r.baselineProbe.outcome), ("paired_probe", runJson r.pairedProbe.outcome),
  ("baseline_probe_detail", toJson r.baselineProbe.detail),
  ("paired_probe_detail", toJson r.pairedProbe.detail),
  ("baseline_zero_checked", toJson r.baselineProof?.isSome),
  ("paired_zero_checked", toJson r.pairedProof?.isSome),
  ("selected_seeds", toJson r.selectedSeeds),
  ("seed_baseline_intervals", toJson (r.selectedSeedDepths.map fun (id, interval) =>
    Json.mkObj [("id", toJson id), ("interval", intervalJson interval)])),
  ("B_used", toJson (r.graph.vertices.filter (·.seed) |>.map fun v =>
    Json.mkObj [("id", toJson v.id), ("constant", toJson (v.origin.constName?.map Name.toString)),
      ("opaque", toJson v.opaqueDecl)])),
  ("c_histogram", Json.mkObj (([EdgeCost.zero, .one, .unknown]).map fun c =>
    (reprStr c, toJson (r.graph.edges.filter (fun edge => edgeActive edge && edge.cost == c)).length))),
  ("priced_edges", toJson (r.graph.edges.map fun edge => Json.mkObj [
    ("conclusion", toJson edge.conclusion), ("premises", toJson edge.premises),
    ("head", toJson (edge.source.map Name.toString)), ("window", toJson edge.window),
    ("baseline_active", toJson (edgeActive edge)),
    ("paired_active", toJson (edgeActive edge true)),
    ("analytic_premises", toJson edge.analytic),
    ("synthetic_premises", toJson (edge.premises.filter fun p => !edge.analytic.contains p)),
    ("used_premises", toJson edge.usedPremises),
    ("paired_used_premises", toJson edge.pairedUsedPremises),
    ("shared_data", toJson edge.sharedData?),
    ("coupled", toJson (edge.sharedData?.map fun shared =>
      if shared then "coupled" else "independent")),
    ("cost", toJson (if edgeActive edge then some (reprStr edge.cost) else none)),
    ("paired_cost", toJson (if edgeActive edge true then some (reprStr edge.pairedCost) else none)),
    ("certificate", toJson (edge.certificate?.map ObviousCertificate.render)),
    ("paired_certificate", toJson (edge.pairedCertificate?.map ObviousCertificate.render)),
    ("query", queryJson edge.query), ("paired_query", queryJson edge.pairedQuery),
    ("detail", toJson edge.detail)])),
  ("witness_edges", toJson r.witnessEdges),
  ("witness_kinds", Json.mkObj [
    ("cut", toJson r.witnessEdges), ("proof_hard", toJson r.proofHardSeeds)]),
  ("no_auxiliary", toJson r.noAuxiliary),
  ("opaque_declarations", toJson (r.graph.vertices.filter (·.opaqueDecl)).length),
  ("target_part_complete", toJson r.targetPartComplete),
  ("d_cut", intervalJson r.baseline), ("d_given", intervalJson r.baselineVisible),
  ("paired_uses_seed", toJson r.pairedUsesSeed),
  ("verdict", toJson (reprStr (classifyGraph r))),
  ("closure", toJson ((classifyClosure r).map fun c =>
    match c with | .zero => "zero" | .partial_ => "partial"))]

/-- Diagnostic stops retain their query/arm context; none supplies a price. -/
def terminationDetails (r : Observation) : Array String := Id.run do
  let mut details := if r.reason.isEmpty then #[] else #[r.reason]
  if let some reading := r.graph? then
    for (arm, probe) in [("baseline", reading.baselineProbe), ("paired", reading.pairedProbe)] do
      if let .incomplete _ := probe.outcome then
        details := details.push s!"{arm}-root:{probe.detail}"
    for edge in reading.graph.edges do
      if edge.cost == .unknown || edge.pairedCost == .unknown then
        details := details.push s!"edge:{edge.source}:{edge.detail}"
    if !reading.targetPartComplete then
      details := details.push "target-part-guard-incomplete"
      for id in reading.selectedSeeds do
        if let some vertex := reading.graph.vertices.find? (·.id == id) then
          details := details.push s!"seed:{id}:independent:{vertex.independentLookupDetail}"
          details := details.push s!"seed:{id}:reverse:{vertex.reverseLookupDetail}"
  return details.toList.eraseDups.toArray

/-- A human-readable projection. No code reads it back for classification. -/
def computationalJson (r : Observation) (baselineCommit : String := "") : Json := Json.mkObj [
  ("reference", toJson "R_lookup"),
  ("execution_version", toJson lookupExecutionVersion),
  ("configuration", toJson (if r.graph?.any (fun g => !g.lookupEnabled) then
    "R_loc-decl/analytic-cut-k2/200000;lookup-ablation" else r.configuration)),
  ("scope", toJson r.scope), ("B_load_count", toJson r.loadedModules.size),
  ("B0_count", toJson r.catalogCount), ("B_load_subset_B0", toJson r.catalogVerified),
  ("B_load", toJson (r.loadedModules.map Name.toString)),
  ("B0_excluded", toJson (r.catalogExcluded.map Name.toString)),
  ("paired_structure_use", toJson (r.pairedStructureUse.map Name.toString)), ("baseline_commit", toJson baselineCommit),
  ("mathlib", toJson mathlibRevision), ("maxHeartbeats", toJson localBudget),
  ("budget_limits", Json.mkObj [
    ("local-closure-heartbeat", toJson localBudget),
    ("candidate-search-kappa", toJson lookupCandidateBudget),
    ("candidate-preparation-limit", toJson lookupPreparationBudget),
    ("G-truncated", toJson lookupCoverageBudget),
    ("isolation-reconstruction", toJson reconstructionBudget)]),
  ("termination_details", toJson (terminationDetails r)),
  ("preparationMaxHeartbeats", toJson lookupPreparationBudget),
    ("candidateMaxHeartbeats", toJson lookupCandidateBudget),
    ("coverageMaxHeartbeats", toJson lookupCoverageBudget),
    ("queryAnswerMemoization", toJson (r.graph?.any (·.queryAnswerMemoization))),
  ("membershipNormalizationFuel", toJson DiskLookup.membershipNormalizationFuel),
  ("target", toJson r.target.toString),
  ("verdict", toJson (r.graph?.map (fun g => dispositionName (classifyDisposition g)) |>.getD "incomplete")),
  ("legacy_verdict", toJson (verdictName r.verdict)),
  ("blocker", blockerJson r),
  ("baseline", runJson r.base), ("paired", runJson r.paired),
  ("presentation", runJson r.presentation),
  ("presentation_source", toJson (r.presentationEvidence?.map (·.source.toString))),
  ("presentation_axioms", toJson (r.presentationEvidence?.map (·.axioms.map Name.toString))),
  ("presentation_detail", toJson r.presentationDetail),
  ("target_checked", toJson r.targetChecked),
  ("structure_checked", toJson r.structureChecked),
  ("structure_clean", toJson r.structureClean),
  ("isolation_checks", Json.mkObj [
    ("budget_semantics", toJson "independent_units"),
    ("m", toJson r.isolationUnitCount),
    ("unit_limit_external", toJson reconstructionBudget),
    ("original_limit_external", toJson reconstructionBudget),
    ("preregistered_total_external", toJson ((r.isolationUnitCount + 1) * reconstructionBudget)),
    ("internal_per_external", toJson (1000 : Nat)),
    ("units", toJson r.isolationUnits)]),
  ("attempt_count", toJson r.attempts.size),
  ("paired_attempt_count", toJson r.pairAttempts.size),
  ("attempts", Json.arr (r.attempts.map attemptJson)),
  ("paired_attempts", Json.arr (r.pairAttempts.map attemptJson)), ("reason", toJson r.reason),
  ("graph", toJson (r.graph?.map graphJson))]

theorem report_computational_unchanged (r : Observation) (information : InformationReading)
    (baselineCommit : String) :
    computationalJson (withInformation r information) baselineCommit =
      computationalJson r baselineCommit := rfl

def observationJson (r : Observation) (baselineCommit : String := "") : Json :=
  let fields := (computationalJson r baselineCommit).getObj?.toOption.get!.toArray.toList
  Json.mkObj (fields ++ [
    ("information_face", toJson r.information.face.label),
    ("information_tag", toJson (informationTag r.verdict r.information.face)),
    ("information_application", toJson (r.information.application.map Name.toString)),
    ("information_registration", toJson (r.information.registration.map Name.toString)),
    ("information_ordinary_records", Json.arr r.information.ordinaryRecords)])

private def runExpr : Run → Expr
  | .found => mkConst ``Run.found
  | .exhausted => mkConst ``Run.exhausted
  | .incomplete failure => mkApp (mkConst ``Run.incomplete)
      (mkConst <| match failure with
        | .missing => ``LeanInformationAudit.SearchReduction.Failure.missing
        | .isolation => ``LeanInformationAudit.SearchReduction.Failure.isolation
        | .execution => ``LeanInformationAudit.SearchReduction.Failure.execution
        | .heartbeat => ``LeanInformationAudit.SearchReduction.Failure.heartbeat
        | .timeout => ``LeanInformationAudit.SearchReduction.Failure.timeout
        | .cancelled => ``LeanInformationAudit.SearchReduction.Failure.cancelled
        | .undecided => ``LeanInformationAudit.SearchReduction.Failure.undecided)

private def edgeCostExpr : EdgeCost → Expr
  | .zero => mkConst ``EdgeCost.zero
  | .one => mkConst ``EdgeCost.one
  | .unknown => mkConst ``EdgeCost.unknown

/- The live graph contains compiler expressions and checked proof terms whose
   source environment is intentionally not imported by an audit module.  The
   classifier reads only the finite graph/interval/run data below, so publish
   a dependency-free GraphReading value with expression payloads erased. -/
private def kernelGraphReading (reading : GraphReading) : GraphReading :=
  { reading with
    graph := { reading.graph with
      vertices := reading.graph.vertices.map fun vertex =>
        { vertex with
          type := .sort .zero
          structureProof? := none
          origin := .sort .zero }
      edges := reading.graph.edges.map fun edge =>
        { edge with zeroProof := none, pairedZeroProof := none }
    }
    baselineProof? := none
    pairedProof? := none }

private def verdictExpr : Verdict → Expr
  | .bindOnly => mkConst ``Verdict.bindOnly
  | .nonBindOnly => mkConst ``Verdict.nonBindOnly
  | .insufficient => mkConst ``Verdict.insufficient

/-- Only dependencies of checked witness terms are exported. No source
extension entries are copied into the proof environment. -/
private partial def exportConstant (source : Environment) (target n : Name) : MetaM Unit := do
  if n == target then throwError "search.target_in_exported_proof"
  if (← getEnv).contains n then return
  let some info := (source.setExporting false).find? n
    | throwError "search.missing_export_dependency: {n}"
  if (projectionShape info).isSome then
    transportVocabulary {source, target} n
    return
  match info with
  | .thmInfo value =>
    for dep in info.getUsedConstantsAsSet do exportConstant source target dep
    discard <| checkProof n value.levelParams value.type value.value
  | _ => transportVocabulary {source, target} n

/-- Publication compiles finite constructor data and checks proofs independently
of the search and of the request wrapper's elaborator recursion limit. -/
def withPublicationContext {α : Type} (action : MetaM α) : MetaM α :=
  withOptions (fun opts => (opts.set `maxRecDepth (max 100000 (maxRecDepth.get opts)))
    |>.setBool `Elab.async false) <|
    withTheReader Core.Context (fun ctx => {ctx with maxHeartbeats := 0}) action

/-- The typed result is computed by the same compiled classifier as A1. -/
def publish (name : Name) (r : Observation) (source? : Option Environment := none)
    (targetHeader? : Option (List Name × Expr) := none) : MetaM Unit :=
    withPublicationContext do
  let targetHeader := do
    if let some info := ((source?.getD (← getEnv)).setExporting false).find? r.target then
      return (info.levelParams, info.type)
    if let some header := targetHeader? then return header
    throwError "search.missing_export_target"
  unless (r.presentation == .found) == r.presentationEvidence?.isSome do
    throwError "search.presentation_witness_mismatch"
  let baseName := name ++ `baseline
  let pairName := name ++ `paired
  for (n, value) in #[(baseName, runExpr r.base), (pairName, runExpr r.paired),
      (name ++ `presentation, runExpr r.presentation)] do
    addAndCompile (.defnDecl {
      name := n, levelParams := [], type := mkConst ``Run,
      value, hints := .abbrev, safety := .safe })
  addAndCompile (.defnDecl {
    name := name ++ `reason, levelParams := [], type := mkConst ``String,
    value := toExpr r.reason, hints := .abbrev, safety := .safe })
  for (label, value) in #[(`scope, toExpr r.scope), (`configuration, toExpr r.configuration)] do
    addAndCompile (.defnDecl {
      name := name ++ label, levelParams := [],
      type := mkConst ``String, value, hints := .abbrev, safety := .safe})
  for (label, value) in #[(`loadedCount, r.loadedModules.size), (`catalogCount, r.catalogCount)] do
    addAndCompile (.defnDecl {
      name := name ++ label, levelParams := [],
      type := mkConst ``Nat, value := toExpr value, hints := .abbrev, safety := .safe})
  for (label, value) in #[(`loadedModules, toExpr r.loadedModules),
      (`catalogExcluded, toExpr r.catalogExcluded), (`pairedStructureUse, toExpr r.pairedStructureUse),
      (`catalogVerified, toExpr r.catalogVerified)] do
    addAndCompile (.defnDecl {
      name := name ++ label, levelParams := [], type := ← inferType value,
      value, hints := .abbrev, safety := .safe})
  if let some evidence := r.presentationEvidence? then
    addAndCompile (.defnDecl {
      name := name ++ `presentationSource, levelParams := [], type := mkConst ``Name,
      value := toExpr evidence.source, hints := .abbrev, safety := .safe })
    let source := source?.getD (← getEnv)
    let (levels, type) ← targetHeader
    for dep in type.getUsedConstants ++ evidence.conversionType.getUsedConstants ++
        evidence.conversion.getUsedConstants ++ evidence.proof.getUsedConstants do
      exportConstant source r.target dep
    discard <| checkProof (name ++ `presentationConversion) levels
      evidence.conversionType evidence.conversion
    discard <| checkProof (name ++ `presentationProof) levels type evidence.proof
  let reading := kernelGraphReading (r.graph?.getD {})
  let graphName := name ++ `graphReading
  let graphValue := toExpr reading
  addAndCompile (.defnDecl {
    name := graphName, levelParams := [], type := mkConst ``GraphReading,
    value := graphValue, hints := .abbrev, safety := .safe })
  let value := mkApp (mkConst ``classifyGraph) (mkConst graphName)
  addAndCompile (.defnDecl {
    name, levelParams := [], type := mkConst ``Verdict,
    value, hints := .abbrev, safety := .safe })
  let equalityType := mkApp2 (mkApp (mkConst ``Eq [1]) (mkConst ``Verdict))
    (mkApp (mkConst ``classifyGraph) (mkConst graphName)) (verdictExpr r.verdict)
  let equalityProof ← synthesizeUsingTactic' (u := .zero) equalityType (← `(tactic| decide))
  addAndCompile (.thmDecl {
    name := name ++ `verdictProof, levelParams := [], type := equalityType,
    value := equalityProof })
  for (label, mapped) in #[(`publishedDisposition, reading),
      (`a1Disposition, kernelGraphReading (priceMappingV18 reading))] do
    let mappedName := name ++ label ++ `reading
    addAndCompile (.defnDecl {
      name := mappedName, levelParams := [],
      type := mkConst ``GraphReading, value := toExpr mapped, hints := .abbrev, safety := .safe})
    let value := mkApp (mkConst ``classifyDisposition) (mkConst mappedName)
    addAndCompile (.defnDecl {
      name := name ++ label, levelParams := [],
      type := mkConst ``Disposition, value, hints := .abbrev, safety := .safe})
    let type := mkApp2 (mkApp (mkConst ``Eq [1]) (mkConst ``Disposition)) value
      (toExpr (classifyDisposition mapped))
    let proof ← synthesizeUsingTactic' (u := .zero) type (← `(tactic| decide))
    discard <| checkProof (name ++ label ++ `proof) [] type proof
  let baselineProbe := mkApp (mkConst ``GraphReading.baselineProbe) (mkConst graphName)
  let baselineOutcome := mkApp (mkConst ``ProbeResult.outcome) baselineProbe
  let noHitType ← mkArrow (mkApp (mkConst ``NoHit) baselineOutcome) equalityType
  let noHitProof ← synthesizeUsingTactic' (u := .zero) noHitType
    (← `(tactic| intro _; decide))
  addAndCompile (.thmDecl {
    name := name ++ `verdictWithNoHit, levelParams := [], type := noHitType,
    value := noHitProof })
  if let some reading := r.graph? then
    let source := source?.getD (← getEnv)
    for (edge, i) in reading.graph.edges.zipIdx do
      let edgeName := name ++ Name.num `edge i
      let record := (edge.conclusion, edge.window, edge.premises,
        reprStr edge.cost, reprStr edge.pairedCost)
      let value := toExpr record
      addAndCompile (.defnDecl {
        name := edgeName, levelParams := [], type := ← inferType value,
        value, hints := .abbrev, safety := .safe})
      for (arm, cost, used) in #[(`baseline, edge.cost, edge.usedPremises),
          (`paired, edge.pairedCost, edge.pairedUsedPremises)] do
        addAndCompile (.defnDecl {
          name := edgeName ++ arm ++ `cost, levelParams := [], type := mkConst ``EdgeCost,
          value := edgeCostExpr cost, hints := .abbrev, safety := .safe})
        let value := toExpr used
        addAndCompile (.defnDecl {
          name := edgeName ++ arm ++ `usedPremises, levelParams := [], type := ← inferType value,
          value, hints := .abbrev, safety := .safe})
      for (arm, certificate?, proof?) in #[
          (`baseline, edge.certificate?, edge.zeroProof),
          (`paired, edge.pairedCertificate?, edge.pairedZeroProof)] do
        if let some certificate := certificate? then
          addAndCompile (.defnDecl {
            name := edgeName ++ arm ++ `certificate, levelParams := [],
            type := mkConst ``ObviousCertificate, value := certificate.toExpr,
            hints := .abbrev, safety := .safe})
        if let some proof := proof? then
          for dep in proof.getUsedConstants do exportConstant source r.target dep
          let type ← inferType proof
          let levels := (collectLevelParams {} type).params.toList
          if ← isProp type then
            discard <| checkProof (edgeName ++ arm ++ `proof) levels type proof
          else
            checkLocalProof type proof
            addDecl (.defnDecl {
              name := edgeName ++ arm ++ `proof, levelParams := levels, type, value := proof,
              hints := .abbrev, safety := .safe})
    let value := toExpr (reading.certificatePool.map CertificateNomination.encode)
    addAndCompile (.defnDecl {
      name := name ++ `certificatePool, levelParams := [], type := ← inferType value,
      value, hints := .abbrev, safety := .safe})
    let value := toExpr (reading.certificateBindings.map fun (owner, n) => (owner, n.encode))
    addAndCompile (.defnDecl {
      name := name ++ `certificateBindings, levelParams := [], type := ← inferType value,
      value, hints := .abbrev, safety := .safe})
  for (label, rows) in #[(`baselineProof, r.attempts), (`pairedProof, r.pairAttempts)] do
    if let some row := rows.find? (fun row => row.proof?.isSome) then
      if let some proof := row.proof? then
        let source := source?.getD (← getEnv)
        let (levels, type) ← targetHeader
        for dep in type.getUsedConstants ++ proof.getUsedConstants do
          exportConstant source r.target dep
        discard <| checkProof (name ++ label) levels type proof

syntax (name := referenceBaselineProbeTac) "reference_baseline " ident " at " str
  " baseline " "[" ident,* "]" " from " "[" ident,* "]" : tactic

/-- Only normal exhaustion fails inside the negative guard. An incomplete
replay returns successfully with an error, so `fail_if_success` rejects it
without rolling the diagnostic back as an ordinary tactic exception. -/
@[tactic referenceBaselineProbeTac] unsafe def evalReferenceBaselineProbe : Tactic := fun stx => do
  match stx with
  | `(tactic| reference_baseline $target:ident at $sha:str baseline [$bs:ident,*]
      from [$owners:ident,*]) =>
    profilePhase "imports/source"
    let (source, shared) ← match ← activeProbe.get with
      | some context => pure context
      | none => do
        let (source, shared, _) ← importSource (owners.getElems.map fun n => {module := n.getId})
        pure (source, shared)
    let replay := (← activeReferenceRequest.get).filter fun request =>
      request.target == target.getId && request.baselineCommit == sha.getString &&
        request.baseline == bs.getElems.map (fun x => x.getId)
    let request := replay.getD {
      target := target.getId, «baseline» := bs.getElems.map (fun x => x.getId),
      baselineCommit := sha.getString }
    let result ← run source request shared (← activeReferenceFixture.get)
    if result.presentation == .found then
      evalTactic (← `(tactic| exact True.intro))
      return
    match result.base with
    | .found => evalTactic (← `(tactic| exact True.intro))
    | .exhausted =>
      if let .incomplete failure := result.presentation then
        logError m!"search.presentation_replay_incomplete: {reprStr failure}"
        return
      throwError "search.normal_exhaustion"
    | .incomplete failure =>
      logError m!"search.replay_incomplete: {reprStr failure}: {result.reason}"
      return
  | _ => throwUnsupportedSyntax

syntax (name := searchReductionProbeCmd) "#search_reduction_probe " ident " at " str
  " baseline " "[" ident,* "]" " using " "[" ident,* "]"
  " from " "[" ident,* "]" " as " ident : command

/-- Name ASTs cross the process boundary in a Lean module's binary expression
payload. Numeric segments never pass through identifier syntax or text parsing. -/
private def writeRequest (path : System.FilePath) (request : Request)
    (owners : Array Name) (result : Name) (fixture : Bool := false) : CommandElabM Unit := do
  let env ← match ← requestEnvironment.get with
    | some env => pure env
    | none => do
      let env ← importModules #[{module := `Lean}] options 0
        (leakEnv := true) (loadExts := false)
      requestEnvironment.set (some env)
      pure env
  let env ← liftTermElabM <| withEnv (env.setMainModule `SearchReductionRequest) do
    for (name, value) in #[(`target, toExpr request.target),
        (`baseline, toExpr request.baseline), (`additions, toExpr request.additions),
        (`informationApplication, toExpr request.informationApplication),
        (`certificates, toExpr (request.certificates.map CertificateNomination.encode)),
        (`edgeCertificates, toExpr (request.edgeCertificates.map fun (owner, n) => (owner, n.encode))),
        (`owners, toExpr owners), (`result, toExpr result), (`commit, toExpr request.baselineCommit),
        (`fixture, toExpr fixture)] do
      let type ← inferType value
      addDecl (.defnDecl {
        name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
    getEnv
  writeModule env path (writeIR := false)

/-- Inspect the actual transitive source closure of checked terms. -/
def certificateSourceDependencies (source : Environment) (proofs : Array Expr)
    (forbidden : Array Name) : Except String Nat := do
  let mut todo := proofs.foldl (fun names proof => names ++ proof.getUsedConstants) #[]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let constant := todo.back!
    todo := todo.pop
    if seen.contains constant then continue
    seen := seen.insert constant
    if forbidden.contains constant then
      throw s!"search.source_certificate_leak:{constant}"
    let some info := (source.setExporting false).find? constant
      | throw s!"search.source_certificate_unresolved:{constant}"
    for dependency in info.getUsedConstantsAsSet do todo := todo.push dependency
  return seen.size

/-- Mandatory source audit reuses checked terms without repeating graph
evaluation or certificate assembly. -/
private def auditProbeCertificates (source : Environment) (request : Request)
    (result : Observation) : CommandElabM Unit := do
  let some reading := result.graph? | return
  let baselineProofs := reading.graph.edges.toArray.filterMap (·.zeroProof) ++
    reading.baselineProbe.proof?.toArray ++ reading.baselineProof?.toArray
  let paired := reading.graph.edges.toArray.filterMap (·.pairedZeroProof) ++
    reading.pairedProbe.proof?.toArray ++ reading.pairedProof?.toArray
  for (arm, proofs, forbidden) in #[("baseline", baselineProofs, #[request.target] ++ request.additions),
      ("paired", paired, #[request.target])] do
    let count ← match certificateSourceDependencies source proofs forbidden with
      | .ok count => pure count
      | .error error => throwError "{arm}: {error}"
    emitLookupRecord s!"PRODUCTION_SOURCE_AUDIT {Json.mkObj [
      ("target", toJson request.target.toString), ("arm", toJson arm),
      ("certificates", toJson proofs.size), ("transitive_constants", toJson count),
      ("forbidden", toJson (forbidden.map Name.toString)),
      ("no_forbidden_dependency", toJson true),
      ("assembled_zero", toJson (if arm == "baseline" then reading.baselineProof?.isSome
        else reading.pairedProof?.isSome))] |>.compress}"

/-- Complete typed probe data; the runner authenticates the bytes before Lean
deserializes them. JSON projections are never accepted as probe evidence. -/
structure ProbeCacheRecord where
  identity : String
  targetHeader : List Name × Expr
  result : Observation
  dependencies : Array Declaration := #[]
  dependencyModule? : Option Name := none

/-- Current mathematical data, including bodies, inductive rules and the
target's import population. Procedure implementations are not input bytes. -/
def probeSourceInputs (source : Environment) (request : Request) :
    Except String (Array Name × Array ConstantInfo) := do
  let source := source.setExporting false
  let roots := #[request.target] ++ request.additions
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut declarations : Array ConstantInfo := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := source.find? name | throw s!"search.cache_source_missing:{name}"
    declarations := declarations.push info
    let dependencies := info.getUsedConstantsAsSet.toArray.qsort Name.quickLt
    todo := todo ++ dependencies
    if let .inductInfo value := info then
      todo := todo ++ value.all.toArray ++ value.ctors.toArray
    if let .ctorInfo value := info then todo := todo.push value.induct
    if let .recInfo value := info then todo := todo ++ value.all.toArray
  let mut modules := request.baseline.foldl (·.insert ·) ({} : NameSet)
  for name in roots do
    if let some index := source.getModuleIdxFor? name then
      modules := modules.insert source.header.moduleNames[index.toNat]!
  let mut changed := true
  while changed do
    changed := false
    for i in [:source.header.moduleNames.size] do
      if !modules.contains source.header.moduleNames[i]! then continue
      for imported in source.header.moduleData[i]!.imports do
        unless modules.contains imported.module do
          modules := modules.insert imported.module
          changed := true
  return (modules.toArray.qsort Name.quickLt, declarations)

/-- Compiled mathematical inputs are data. Runtime/compiler packages are pinned
by explicit versions, and judge modules never contribute program bytes. -/
private def snapshotProbeSourceData (directory : System.FilePath)
    (source : Environment) (request : Request) : IO Unit := do
  let (scope, declarations) ← IO.ofExcept (probeSourceInputs source request)
  for root in #[request.target] ++ request.additions do
    unless (source.getModuleIdxFor? root).isSome do
      throw <| IO.userError s!"search.cache_source_without_compiled_owner:{root}"
  let program := fun (name : Name) =>
    name.toString.startsWith "LeanInformationAudit" &&
      !name.toString.startsWith "LeanInformationAuditRegTests."
  let mut modules := scope.foldl (·.insert ·) ({} : NameSet)
  for info in declarations do
    if let some index := source.getModuleIdxFor? info.name then
      let module := source.header.moduleNames[index.toNat]!
      if program module then throw <| IO.userError s!"search.cache_program_dependency:{module}"
      modules := modules.insert module
  let mut files : Array String := #[]
  let list := directory / "source-input-files.json"
  if ← list.pathExists then
    files ← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile list))
  for module in modules.toArray.qsort Name.quickLt do
    let name := module.toString
    if program module || #["Init", "Lean", "Std", "Lake", "Batteries", "Aesop", "Qq",
        "Plausible", "LeanSearchClient", "ImportGraph", "ProofWidgets"].any
        (fun stem => name == stem || name.startsWith (stem ++ ".")) then continue
    let olean ← IO.FS.realPath (← findOLean module)
    for part in #[olean, OLeanLevel.server.adjustFileName olean,
        OLeanLevel.private.adjustFileName olean] do
      unless files.contains part.toString do files := files.push part.toString
  IO.FS.createDirAll directory
  IO.FS.writeFile list ((toJson (files.qsort (· < ·))).compress)
  let result ← IO.Process.output {
    cmd := "python3", args := #["tools/scripts/search-reduction-probe-cache.py",
      "--snapshot-source-data", directory.toString] }
  unless result.exitCode == 0 do
    throw <| IO.userError s!"search.cache_source_snapshot_failed:{result.stderr}"

private def probeIdentity (request : Request) (owners : Array Name) (name : Name)
    (fixture : Bool) : IO String := do
  return reprStr (localConfiguration, certificateLanguageVersion, transportVersion,
    "probe-record-v9", ← IO.getEnv "SEARCH_REDUCTION_PROBE_ID", request.target,
    request.baseline, request.additions, request.baselineCommit, request.informationApplication,
    request.certificates.map CertificateNomination.encode,
    request.edgeCertificates.map (fun (n, c) => (n, c.encode)), owners, name, fixture)

private def probeProofs (result : Observation) : Array Expr := Id.run do
  let mut proofs := (result.attempts ++ result.pairAttempts).filterMap (·.proof?)
  if let some evidence := result.presentationEvidence? then
    proofs := proofs ++ #[evidence.conversion, evidence.proof]
  if let some reading := result.graph? then
    proofs := proofs ++ reading.graph.vertices.toArray.filterMap (·.structureProof?) ++
      reading.graph.edges.toArray.filterMap (·.zeroProof) ++
      reading.graph.edges.toArray.filterMap (·.pairedZeroProof) ++
      reading.baselineProbe.proof?.toArray ++ reading.pairedProbe.proof?.toArray ++
      reading.baselineProof?.toArray ++ reading.pairedProof?.toArray
  return proofs

def checkCachedProbeCertificates (result : Observation) : MetaM Unit := withPublicationContext do
  let proofs := probeProofs result
  let before ← getEnv
  try
    -- Every certificate crosses the kernel separately. A temporary root then
    -- collects their union of axioms in one shared Lean traversal, so common
    -- dependency bodies are visited once. A standard union certifies each arm.
    let mut bundle := mkConst ``True.intro
    for proof in proofs do
      let type ← instantiateMVars (← inferType proof)
      let proof ← instantiateMVars proof
      unless !type.hasMVar && !type.hasFVar && !proof.hasMVar &&
          !proof.hasFVar && !proof.hasSorry do
        throwError "graph.unclosed_local_certificate"
      let name ← mkFreshUserName `_cachedCertificate
      let levels := (collectLevelParams {} type).params.toList
      timeLookup "certificate/kernel" do
        if ← isProp type then
          addDecl (.thmDecl {name, levelParams := levels, type, value := proof})
        else
          addDecl (.defnDecl {
            name, levelParams := levels, type, value := proof,
            hints := .abbrev, safety := .safe})
      bundle := .letE name type (mkConst name (levels.map mkLevelParam)) bundle false
    let name ← mkFreshUserName `_cachedCertificateClosure
    let levels := (collectLevelParams {} bundle).params.toList
    addDecl (.thmDecl {
      name, levelParams := levels, type := mkConst ``True, value := bundle})
    let axioms ← timeLookup "certificate/axioms-batch" <| collectAxioms name
    unless standardAxioms axioms do throwError "graph.nonstandard_axioms: {axioms}"
  finally setEnv before
  emitLookupRecord s!"PROBE_CACHE_KERNEL_CERTIFICATES count={proofs.size} standard_axioms=true"

/-- Freeze only kernel-checked dependency declarations into an ordinary Lean
module. Hot imports use the same compiled-module trust boundary as cold imports;
certificates and the classifier are still checked in the current process. -/
def writeCacheDependencyModule (directory : System.FilePath) (identity : String)
    (base : Environment) (dependencies : Array Declaration) : MetaM Name := do
  let module := s!"SearchReductionDependencies_{hash identity}" |>.toName
  withEnv base <| withPublicationContext do
    replayCacheDependencies dependencies
    IO.FS.createDirAll directory
    writeModule ((← getEnv).setMainModule module)
      (directory / (module.toString ++ ".olean")) (writeIR := false)
  return module

/-- Typed dependency declarations are either imported from a kernel-checked
module or replayed through the kernel before current certificate checks. -/
unsafe def saveProbeCache (directory : System.FilePath) (identity : String)
    (source : Environment) (request : Request) (result : Observation)
    (base? : Option Environment := none) (importDependencies : Bool := false)
    (moduleMinDependencies : Nat := 0) : CommandElabM Unit := do
  let some info := (source.setExporting false).find? request.target
    | throwError "search.cache_missing_target"
  let path := directory / s!"probe-{hash identity}.pickle"
  let mut base := base?.getD (← getEnv)
  let roots ← liftTermElabM <| withPublicationContext do
    let mut roots := #[]
    if result.presentationEvidence?.isSome ||
        (result.attempts ++ result.pairAttempts).any (·.proof?.isSome) then
      roots := info.type.getUsedConstants
    for proof in probeProofs result do
      let type ← withEnv source (inferType proof)
      roots := roots ++ type.getUsedConstants ++ proof.getUsedConstants
    if let some evidence := result.presentationEvidence? then
      roots := roots ++ evidence.conversionType.getUsedConstants
    pure roots
  let mut dependencies ← match captureCacheDependencies source base request.target roots with
    | .ok declarations => pure declarations
    | .error error => throwError "{error}"
  let useModule := importDependencies && dependencies.size >= moduleMinDependencies
  if useModule then
    -- Allocate current extension states after source registration. Only large
    -- closures pay for a second import; small closures keep live kernel replay.
    -- This cutoff selects cache work, independently of every search parameter.
    enableInitializersExecution
    base ← withImporting <| importModules
      #[{module := `LeanInformationAuditRegAnalysis.SearchReduction.Commands}]
      options 0 (leakEnv := false) (loadExts := false)
    dependencies ← match captureCacheDependencies source base request.target roots with
      | .ok declarations => pure declarations
      | .error error => throwError "{error}"
  let dependencyModule? ← if useModule then
    pure (some (← liftTermElabM <| writeCacheDependencyModule directory identity base dependencies))
    else pure none
  IO.FS.createDirAll directory
  let temporary := path.addExtension "tmp"
  pickle temporary ({
    identity, targetHeader := (info.levelParams, info.type), result, dependencies,
    dependencyModule?} : ProbeCacheRecord)
  IO.FS.rename temporary path

unsafe def replayProbeCache (directory : System.FilePath) (identity : String)
    (request : Request) (owners : Array Name) (name : Name) : CommandElabM Bool := do
  let path := directory / s!"probe-{hash identity}.pickle"
  unless ← path.pathExists do return false
  profilePhase "probe/cache-load-start"
  let (record, region) ← unpickle ProbeCacheRecord path
  profilePhase "probe/cache-unpickle-end"
  probeRegions.modify (·.push region)
  unless record.identity == identity && record.result.target == request.target do
    throwError "search.probe_cache_identity_mismatch"
  if let some module := record.dependencyModule? then
    let imported ← getEnv
    unless imported.allImportedModuleNames.contains module &&
        record.dependencies.all (fun declaration =>
          declaration.getNames.all imported.isImportedConst) do
      throwError "search.cache_dependency_module_not_imported:{module}"
    emitLookupRecord s!"PROBE_CACHE_IMPORTED_DEPENDENCIES count={record.dependencies.size} module={module}"
  else
    liftTermElabM <| withPublicationContext <| replayCacheDependencies record.dependencies
  let source ← getEnv
  profilePhase "probe/cache-load-end"
  let mainModule := (← getEnv).header.mainModule
  modifyEnv fun _ => source.setMainModule mainModule
  profilePhase "probe/cache-kernel-start"
  liftTermElabM <| withPublicationContext <| checkCachedProbeCertificates record.result
  profilePhase "probe/cache-kernel-end"
  auditProbeCertificates source request record.result
  profilePhase "probe/publication-start"
  liftTermElabM <| publish name record.result (some source) (some record.targetHeader)
  emitLookupRecord "PROBE_CACHE_CURRENT_CLASSIFIER checked=true input_versions=explicit"
  profilePhase "probe/publication-end"
  let auditModule := s!"SearchReductionAudit_{hash request.target}_{← IO.monoNanosNow}"
  let auditDirectory : System.FilePath := "build/lean-inspector/search-reduction-audits/" ++ auditModule
  IO.FS.createDirAll auditDirectory
  let auditDirectory ← IO.FS.realPath auditDirectory
  let payload := auditDirectory / "request.olean"
  writeRequest payload request owners name
  let auditSource := auditDirectory / (auditModule ++ ".lean")
  IO.FS.writeFile auditSource ("import LeanInformationAuditRegAnalysis.SearchReduction.Commands\n" ++
    s!"run_cmd LeanInformationAudit.SearchReduction.executeProbeFile {repr payload.toString}\n")
  let output := auditDirectory / (auditModule ++ ".olean")
  writeModule ((← getEnv).setMainModule auditModule.toName) output (writeIR := false)
  emitLookupRecord s!"PROBE_CACHE hit=authenticated kernel_recomputed=true"
  emitLookupRecord s!"SEARCH_REDUCTION_AUDIT {Json.mkObj [
    ("target", toJson request.target.toString), ("source", toJson auditSource.toString),
    ("module", toJson output.toString), ("payload", toJson payload.toString),
    ("negative_semantics", toJson "authenticated cached meta-computed full R; not an object-level unprovability proof")] |>.compress}"
  logInfo (observationJson record.result request.baselineCommit).compress
  return true

/-- Count every requested probe, including wrappers that fail before dispatch.
A hot entry may replace the wrapper only for a complete single-probe plan. -/
private def recordProbePlan : IO Unit := do
  if let some directory ← IO.getEnv "SEARCH_REDUCTION_PROBE_WRITE" then
    IO.FS.createDirAll directory
    IO.FS.withFile (System.FilePath.mk directory / "entry-plan") .append fun handle =>
      handle.putStrLn "probe"

unsafe def executeProbe (request : Request) (owners : Array Name) (name : Name)
    (fixture : Bool := false) : CommandElabM Unit := do
  unless (← IO.getEnv "SEARCH_REDUCTION_PROBE_PLANNED") == some "1" do recordProbePlan
  let cacheBase ← getEnv
  let identity ← probeIdentity request owners name fixture
  if let some directory ← IO.getEnv "SEARCH_REDUCTION_PROBE_READ" then
    if ← replayProbeCache directory identity request owners name then return
  emitLookupRecord "PROBE_CACHE miss"
  let auditModule := s!"SearchReductionAudit_{hash request.target}_{← IO.monoNanosNow}"
  let auditDirectory : System.FilePath := "build/lean-inspector/search-reduction-audits/" ++ auditModule
  IO.FS.createDirAll auditDirectory
  let auditDirectory ← IO.FS.realPath auditDirectory
  let auditPayload := auditDirectory / "request.olean"
  writeRequest auditPayload request owners name fixture
  let auditSource := auditDirectory / (auditModule ++ ".lean")
  IO.FS.writeFile auditSource
    ("import LeanInformationAuditRegAnalysis.SearchReduction.Commands\n" ++
      s!"run_cmd LeanInformationAudit.SearchReduction.executeProbeFile {repr auditPayload.toString}\n")
  profilePhase "probe/source-import-start"
  let imports := owners.map fun n => {module := n : Import}
  let (source, shared, _) ← importSource imports
  profilePhase "probe/source-import-end"
  let cacheInputsReady ← if let some directory ← IO.getEnv "SEARCH_REDUCTION_PROBE_WRITE" then
    try
      profilePhase "probe/source-data-snapshot-start"
      snapshotProbeSourceData directory source request
      profilePhase "probe/source-data-snapshot-end"
      pure true
    catch ex =>
      emitLookupRecord s!"PROBE_CACHE save_rejected={← ex.toMessageData.toString}"
      pure false
    else pure false
  -- Exported proof expressions retain source module storage; transient
  -- environment maps and extension states need not be made persistent.
  probeRegions.modify (· ++ source.header.regions)
  let computational ← run source request shared fixture
  profilePhase "probe/information-start"
  let information ← acquireInformation source request.target request.additions request.informationApplication
  profilePhase "probe/information-end"
  let result := withInformation computational information
  profilePhase "probe/negative-guard-start"
  let guardProof? ← if result.verdict == .nonBindOnly then
    liftTermElabM <| withTheReader Core.Context (fun ctx => {ctx with maxHeartbeats := 0}) do
      -- Replay precedes publication, so author extension initializers cannot
      -- affect either independent baseline search in this compiler process.
      let target := mkIdent request.target
      let sha := Syntax.mkStrLit request.baselineCommit
      let bs := request.baseline.map mkIdent
      let os := owners.map mkIdent
      withReferenceProbeContext (request? := some request) (fixture := fixture) source shared do
        return some (← synthesizeUsingTactic' (u := .zero) (mkConst ``True)
          (← `(tactic|
            (fail_if_success (reference_baseline $target at $sha baseline [$bs,*] from [$os,*]))
            <;> exact True.intro)))
    else pure none
  profilePhase "probe/negative-guard-end"
  profilePhase "probe/source-audit-start"
  auditProbeCertificates source request result
  profilePhase "probe/source-audit-end"
  -- Source metadata belongs to its own environment. R has already used a
  -- separately imported baseline, without source attributes or instances.
  let mainModule := (← getEnv).header.mainModule
  modifyEnv fun _ => source.setMainModule mainModule
  profilePhase "probe/publication-start"
  liftTermElabM <| withTheReader Core.Context (fun ctx => {ctx with maxHeartbeats := 0}) do
    if let some guardProof := guardProof? then
      discard <| checkProof (name ++ `baselineFailureGuard) [] (mkConst ``True) guardProof
    publish name result (some source)
  profilePhase "probe/publication-end"
  let auditOutput := auditDirectory / (auditModule ++ ".olean")
  writeModule ((← getEnv).setMainModule auditModule.toName) auditOutput (writeIR := false)
  emitLookupRecord s!"SEARCH_REDUCTION_AUDIT {Json.mkObj [
    ("target", toJson request.target.toString), ("source", toJson auditSource.toString),
    ("module", toJson auditOutput.toString), ("payload", toJson auditPayload.toString),
    ("negative_semantics", toJson "meta-computed full R; not an object-level unprovability proof")] |>.compress}"
  if let some directory ← IO.getEnv "SEARCH_REDUCTION_PROBE_WRITE" then
    unless cacheInputsReady do
      logInfo (observationJson result request.baselineCommit).compress
      return
    profilePhase "probe/cache-save-start"
    try
      saveProbeCache directory identity source request result (some cacheBase)
        (importDependencies := true) (moduleMinDependencies := 4096)
      -- The runner authenticates this entry only after the entire original
      -- request succeeds. Hot execution retains executeProbe's source audit,
      -- certificate kernel checks and fresh GraphReading publication, while
      -- reusing the successful request wrapper's imports and diagnostics.
      let entry := s!"entry-{hash identity}"
      let payloadName := entry ++ ".olean"
      -- Reuse the checked payload emitted before importing the source.
      -- Its small environment predates any newly initialized source extensions.
      IO.FS.writeBinFile (directory / payloadName) (← IO.FS.readBinFile auditPayload)
      let dependencyModule := s!"SearchReductionDependencies_{hash identity}"
      let moduleExists ← (System.FilePath.mk directory / (dependencyModule ++ ".olean")).pathExists
      let entryImport := if moduleExists then dependencyModule
        else "LeanInformationAuditRegAnalysis.SearchReduction.Commands"
      IO.FS.writeFile (directory / (entry ++ ".lean"))
        (s!"import {entryImport}\n" ++
          "set_option Elab.async false\nset_option maxHeartbeats 0\n" ++
          "run_cmd do\n" ++
          "  let some directory ← IO.getEnv \"SEARCH_REDUCTION_PROBE_READ\"\n" ++
          "    | throwError \"search.cache_entry_without_authenticated_record\"\n" ++
          s!"  LeanInformationAudit.SearchReduction.executeProbeFile (System.FilePath.mk directory / {repr payloadName})\n")
    catch ex => emitLookupRecord s!"PROBE_CACHE save_rejected={← ex.toMessageData.toString}"
    profilePhase "probe/cache-save-end"
  logInfo (observationJson result request.baselineCommit).compress

/-- Only closed, kernel-checked Name/array/string expression values are read.
No result JSON or source proof is used to construct the request. -/
unsafe def executeProbeFile (path : System.FilePath) : CommandElabM Unit := do
  let (data, region) ← readModuleData path
  probeRegions.modify (·.push region)
  let requestData ← liftTermElabM do
    let getValue := fun name => do
      let some (.defnInfo info) := data.constants.find? (·.name == name)
        | throwError "search.request_data_missing: {name}"
      pure info.value
    let target ← evalExpr Name (mkConst ``Name) (← getValue `target)
    let bs ← evalExpr (Array Name) (mkApp (mkConst ``Array [.zero]) (mkConst ``Name))
      (← getValue `baseline)
    let additions ← evalExpr (Array Name) (mkApp (mkConst ``Array [.zero]) (mkConst ``Name))
      (← getValue `additions)
    let informationApplication ← evalExpr (Option Name)
      (mkApp (mkConst ``Option [.zero]) (mkConst ``Name)) (← getValue `informationApplication)
    let encoded ← evalExpr (Array (Nat × Name × String))
      (toTypeExpr (Array (Nat × Name × String))) (← getValue `certificates)
    let certificates ← encoded.mapM fun n =>
      match CertificateNomination.decode n with
      | .ok value => pure value
      | .error message => throwError "{message}"
    let encodedBindings ← evalExpr (Array (Name × (Nat × Name × String)))
      (toTypeExpr (Array (Name × (Nat × Name × String)))) (← getValue `edgeCertificates)
    let edgeCertificates ← encodedBindings.mapM fun (owner, n) =>
      match CertificateNomination.decode n with
      | .ok value => pure (owner, value)
      | .error message => throwError "{message}"
    let owners ← evalExpr (Array Name) (mkApp (mkConst ``Array [.zero]) (mkConst ``Name))
      (← getValue `owners)
    let name ← evalExpr Name (mkConst ``Name) (← getValue `result)
    let commit ← evalExpr String (mkConst ``String) (← getValue `commit)
    let fixture ← match data.constants.find? (·.name == `fixture) with
      | some (.defnInfo info) => evalExpr Bool (mkConst ``Bool) info.value
      | _ => pure false
    let request : Request := {
      target := target
      «baseline» := bs
      additions := additions
      baselineCommit := commit
      informationApplication := informationApplication
      certificates
      edgeCertificates }
    pure (request, owners, name, fixture)
  executeProbe requestData.1 requestData.2.1 requestData.2.2.1 requestData.2.2.2

@[command_elab searchReductionProbeCmd] unsafe def elabSearchReductionProbe : CommandElab := fun stx => do
  match stx with
  | `(#search_reduction_probe $target:ident at $sha:str baseline [$bs:ident,*]
      using [$ss:ident,*] from [$owners:ident,*] as $name:ident) =>
    executeProbe {
      target := target.getId, «baseline» := bs.getElems.map (·.getId),
      additions := ss.getElems.map (·.getId), baselineCommit := sha.getString,
      certificates := ← submittedCertificates.get,
      edgeCertificates := ← submittedEdgeCertificates.get}
      (owners.getElems.map (·.getId)) name.getId
      ((← getEnv).header.mainModule.toString.startsWith "LeanInformationAuditRegTests.SearchReduction.")
  | _ => throwUnsupportedSyntax

/-- Recheck child publication data and proofs in the parent environment. -/
unsafe def replayPublication (constants : Array ConstantInfo) (target name : Name) : MetaM Unit :=
    withPublicationContext do
  for n in #[name ++ `baseline, name ++ `paired, name ++ `reason,
      name ++ `presentation, name ++ `scope, name ++ `configuration,
      name ++ `loadedCount, name ++ `catalogCount, name ++ `loadedModules,
      name ++ `catalogExcluded, name ++ `pairedStructureUse,
      name ++ `catalogVerified, name ++ `presentationSource,
      name ++ `presentationConversion, name ++ `presentationProof,
      name ++ `graphReading, name ++ `verdictProof,
      name ++ `publishedDisposition ++ `reading, name ++ `publishedDisposition,
      name ++ `publishedDisposition ++ `proof,
      name ++ `a1Disposition ++ `reading, name ++ `a1Disposition,
      name ++ `a1Disposition ++ `proof,
      name ++ `verdictWithNoHit, name,
      name ++ `baselineProof, name ++ `pairedProof,
      name ++ `baselineFailureGuard] do
    match constants.find? (·.name == n) with
    | some (.defnInfo info) => addAndCompile (.defnDecl info)
    | some (.thmInfo info) =>
      -- The child may use baseline vocabulary loaded for fixed tactics
      -- that the request module itself does not import. Reconstruct that
      -- support before rechecking the exported proof in the parent.
      let dependencies := info.type.getUsedConstants ++ info.value.getUsedConstants
      unless dependencies.all (← getEnv).contains do
        enableInitializersExecution
        let source ← referenceEnvironment
        for dependency in dependencies do
          exportConstant source target dependency
      discard <| checkProof n info.levelParams info.type info.value
    | _ => pure ()

syntax (name := searchReductionCmd) "#search_reduction " ident " at " str
  " baseline " "[" ident,* "]" " using " "[" ident,* "]"
  (" information " ident)? " as " ident : command

/-- Separate compiler processes also isolate Mathlib's process-global lazy
indexes. Only compiled Lean declarations are read back; JSON is print-only. -/
@[command_elab searchReductionCmd] unsafe def elabSearchReduction : CommandElab := fun stx => do
  match stx with
  | `(#search_reduction $target:ident at $sha:str baseline [$bs:ident,*] using [$ss:ident,*]
      $[information $app:ident]? as $name:ident) =>
    profilePhase "request/command-start"
    recordProbePlan
    let source ← getEnv
    let fixture := source.header.mainModule.toString.startsWith "LeanInformationAuditRegTests.SearchReduction."
    for module in bs.getElems do
      unless source.header.moduleNames.contains module.getId do
        let failed : Observation := {
          target := target.getId, base := .incomplete .missing, paired := .incomplete .missing,
          verdict := .insufficient, reason := s!"search.baseline_owner_not_imported: {module.getId}" }
        liftTermElabM <| publish name.getId failed
        logInfo (observationJson failed sha.getString).compress
        return
    let mut modules := #[`LeanInformationAuditRegAnalysis.SearchReduction.Commands] ++
      bs.getElems.map (fun x => x.getId)
    for n in #[target.getId] ++ ss.getElems.map (fun x => x.getId) ++
        (app.toArray.map (·.getId)) do
      if n != target.getId && (source.getModuleIdxFor? n).isNone then continue
      let some idx := source.getModuleIdxFor? n
        | let failed : Observation := {
            target := target.getId, base := .incomplete .missing, paired := .incomplete .missing,
            verdict := .insufficient, reason := s!"search.missing_compiled_owner: {n}" }
          liftTermElabM <| publish name.getId failed
          logInfo (observationJson failed sha.getString).compress
          return
      let owner := source.header.moduleNames[idx.toNat]!
      unless modules.contains owner do modules := modules.push owner
    let namePrefix := String.ofList (name.getId.toString.toList.take 48)
    let safeName := (namePrefix.map (fun c => if c.isAlphanum then c else '_')) ++
      s!"_{hash name.getId}"
    let moduleName := "SearchReductionProbe_" ++ safeName
    let directory : System.FilePath := ".lake/build/search-reduction/" ++ safeName ++
      s!"_{← IO.Process.getPID}"
    IO.FS.createDirAll directory
    let directory ← IO.FS.realPath directory
    let input := directory / (moduleName ++ ".lean")
    let output := directory / (moduleName ++ ".olean")
    let imports := "import LeanInformationAuditRegAnalysis.SearchReduction.Commands\n"
    let payload := directory / "request.olean"
    profilePhase "request/payload-start"
    writeRequest payload {
      target := target.getId, «baseline» := bs.getElems.map (·.getId),
      additions := ss.getElems.map (·.getId), baselineCommit := sha.getString,
      informationApplication := app.map (·.getId),
      certificates := ← submittedCertificates.get,
      edgeCertificates := ← submittedEdgeCertificates.get} modules name.getId
      fixture
    profilePhase "request/payload-end"
    let command := s!"run_cmd LeanInformationAudit.SearchReduction.executeProbeFile {repr payload.toString}\n"
    IO.FS.writeFile input (imports ++ command)
    let workers := min 8 <| max 1 <|
      ((← IO.getEnv "SEARCH_REDUCTION_WORKERS").bind String.toNat?).getD 8
    profilePhase "request/child-start"
    let child ← IO.Process.output {
      cmd := "lean", args := #[s!"-j{workers}", "--root=" ++ directory.toString,
        "-o", output.toString, input.toString],
      env := #[("SEARCH_REDUCTION_PROBE_PLANNED", some "1")]}
    profilePhase "request/child-end"
    if child.exitCode == 75 then IO.Process.exit 75
    if child.exitCode != 0 then
      unless fixture do
        throwError "search.probe_compile_failed: exit {child.exitCode}\n{child.stdout}\n{child.stderr}"
      if (← IO.getEnv "SEARCH_REDUCTION_VERIFY_INDEX") == some "1" then
        IO.eprintln s!"{child.stdout}\n{child.stderr}"
        IO.Process.exit 1
      let failed : Observation := {
        target := target.getId, base := .incomplete .execution, paired := .incomplete .execution,
        verdict := .insufficient, reason := s!"search.probe_compile_failed: exit {child.exitCode}" }
      liftTermElabM <| publish name.getId failed
      logWarning m!"{child.stdout}\n{child.stderr}"
      logInfo (observationJson failed sha.getString).compress
      return
    logInfo child.stdout
    unless child.stderr.isEmpty do logInfo child.stderr
    let (projected, region) ← readModuleData output
    probeRegions.modify (·.push region)
    profilePhase "request/replay-publication-start"
    liftTermElabM <| replayPublication projected.constants target.getId name.getId
    profilePhase "request/replay-publication-end"
  | _ => throwUnsupportedSyntax

syntax (name := searchReductionCatalogCmd) "#search_reduction_catalog " str : command
@[command_elab searchReductionCatalogCmd] unsafe def elabSearchReductionCatalog : CommandElab := fun stx => do
  let `(#search_reduction_catalog $sha:str) := stx | throwUnsupportedSyntax
  enableInitializersExecution
  let base ← referenceEnvironment
  let catalog ← baselineCatalog sha.getString #[] base
  logInfo (Json.mkObj [
    ("baseline_commit", toJson sha.getString), ("unit", toJson "frozen-D5-module"),
    ("frozen_modules", toJson (catalog.frozen.map Name.toString)),
    ("B0_count", toJson catalog.eligible.size)]).compress

syntax (name := searchReductionConfigCmd) "#search_reduction_config" : command
@[command_elab searchReductionConfigCmd] unsafe def elabSearchReductionConfig : CommandElab := fun _ => do
  logInfo (Json.mkObj [("version", toJson "R_lookup"), ("maxHeartbeats", toJson localBudget),
    ("preparationMaxHeartbeats", toJson lookupPreparationBudget),
    ("candidateMaxHeartbeats", toJson lookupCandidateBudget),
    ("coverageMaxHeartbeats", toJson lookupCoverageBudget),
    ("queryAnswerMemoization", toJson (← localMemoEnabled)),
    ("membershipNormalizationFuel", toJson DiskLookup.membershipNormalizationFuel),
    ("transport", toJson transportVersion), ("reconstructionMaxHeartbeats", toJson reconstructionBudget),
    ("reconstructionBudgetSemantics", toJson "independent_units"),
    ("pinnedDeriving", toJson (pinnedDerivingClasses.map Name.toString)),
    ("configuration", toJson localConfiguration),
    ("lean", toJson Lean.versionString), ("mathlib", toJson mathlibRevision),
    ("k", toJson (2 : Nat)), ("graphUnit", toJson "live-declaration"),
    ("strategies", toJson (["intro", "assumption", "rfl", "And/Iff/Exists/Subtype", "ordered-apply-depth2", "simp-only-direct-eq-iff/no-simprocs", "omega/no-mvars", "ring", "ring_nf", "linarith-only-direct", "positivity", "norm_num1", "decide/no-quantifiers"] : List String))]).compress

end LeanInformationAudit.SearchReduction
