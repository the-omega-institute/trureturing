import LeanInformationAuditRegAnalysis.SearchReduction.Commands

/-! Reused probe evidence must cross both kernel checks in the live path. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction

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
