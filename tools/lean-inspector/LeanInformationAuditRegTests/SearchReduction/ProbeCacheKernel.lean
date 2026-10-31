import LeanInformationAuditRegAnalysis.SearchReduction.Commands

/-! Reused probe evidence must cross both kernel checks in the live path. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction

run_cmd do
  let result : Observation := {
    target := `cacheFaultRegression, base := .exhausted, paired := .found,
    verdict := .insufficient }
  unless probeCacheable result do throwError "complete probe was not cacheable"
  for failure in [Failure.missing, .execution, .heartbeat, .timeout, .cancelled] do
    if probeCacheable {result with base := .incomplete failure} then
      throwError "fault was cacheable: {repr failure}"
  for terminal in [RQuery.fault "preparation", .fault "resource-guard", .notRun] do
    if probeCacheable {result with graph? := some {queryRecords := [{
        role := "requested", target := 0, premises := [], terminal}]}} then
      throwError "requested fault/not-run was cacheable"
  if probeCacheable {result with graph? := some {queryRecords := [{
      role := "requested", target := 0, premises := [], terminal := .miss .exhaustive,
      encounteredFaults := #["preparation"]}]}} then
    throwError "absorbed fault was cached"
  match certificateSourceDependencies (← getEnv) #[mkConst `missingSource] #[] with
  | .error (.unresolved `missingSource) => pure ()
  | _ => throwError "unresolved source was classified as a semantic rejection"
  logInfo "probe cache: faults and requested NotRun excluded; unresolved source remains a fault"

run_cmd liftTermElabM do
  let result : Observation := {
    target := `cacheRegression
    base := .incomplete .undecided
    paired := .incomplete .undecided
    verdict := .insufficient
    attempts := #[{ strategy := "cached", outcome := .found, proof? := some (mkConst ``True.intro) }] }
  checkCachedProbeCertificates result
  let invalid := mkApp
    (mkLambda `h .default (mkConst ``False) (mkBVar 0)) (mkConst ``True.intro)
  let rejected ← try
    checkCachedProbeCertificates {result with
      attempts := #[{strategy := "cached", outcome := .found, proof? := some invalid}]}
    pure false
    catch _ => pure true
  unless rejected do throwError "cached invalid certificate bypassed the kernel"
  let result := {result with attempts := #[]}
  let before ← getEnv
  publish `cacheRegression result
  let axioms ← collectAxioms `cacheRegression.verdictProof
  unless standardAxioms axioms do throwError "cached verdict has nonstandard axioms"
  setEnv before
  let rejected ← try
    publish `cacheRegression {result with verdict := .bindOnly}
    pure false
    catch _ => pure true
  unless rejected do throwError "cached verdict bypassed kernel recomputation"
  logInfo "probe cache: invalid certificate and altered verdict rejected by kernel"

run_cmd liftTermElabM do
  let before ← getEnv
  let publicName := `cacheReplayCollision.eq_1
  let privateName := Name.str (Name.str
    (Name.num (Name.str (Name.str .anonymous "_private") "CacheReplay") 0)
    "cacheReplayCollision") "eq_1"
  let privateProof : Declaration := .thmDecl {
    name := privateName, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }
  let publicProof : Declaration := .thmDecl {
    name := publicName, levelParams := [], type := mkConst ``True, value := mkConst privateName }
  let checked ← ofExceptKernelException <|
    before.toKernelEnv.addDeclCore 0 0 privateProof (cancelTk? := none)
  let checked ← ofExceptKernelException <|
    checked.addDeclCore 0 0 publicProof (cancelTk? := none)
  let source := Environment.ofKernelEnv checked
  let dependencies ← match captureCacheDependencies source before `cacheReplayTarget #[publicName] with
    | .ok declarations => pure declarations
    | .error message => throwError "{message}"
  unless dependencies.size == 2 do throwError "private proof dependency was omitted"
  try
    replayCacheDependencies dependencies
    checkLocalProof (mkConst ``True) (mkConst publicName)
    unless standardAxioms (← collectAxioms publicName) do
      throwError "private replay introduced a nonstandard axiom"
    logInfo "probe cache: private/public normalized-name collision replayed through kernel"
  finally setEnv before

run_cmd liftTermElabM do
  let rows := (List.range 3).toArray.map fun _ =>
    ({strategy := "shared closure", outcome := .found,
      proof? := some (mkConst ``True.intro)} : Attempt)
  let result : Observation := {
    target := `cacheBatchRegression, base := .incomplete .undecided,
    paired := .incomplete .undecided, verdict := .insufficient, attempts := rows }
  profilePhase "regression/shared-axiom-closure-start"
  checkCachedProbeCertificates result
  if let some path ← IO.getEnv "SEARCH_REDUCTION_PROFILE" then
    let trace ← IO.FS.readFile path
    let trace := (trace.splitOn "regression/shared-axiom-closure-start").getLast!
    unless (trace.splitOn "certificate/kernel/start").length == 4 do
      throwError "cached certificate batch did not check all three proofs"
    unless (trace.splitOn "certificate/axioms-batch/start").length == 2 &&
        (trace.splitOn "certificate/axioms/start").length == 1 do
      throwError "cached certificates repeated the common axiom traversal"
  logInfo "probe cache: three kernel checks share one complete axiom traversal"
