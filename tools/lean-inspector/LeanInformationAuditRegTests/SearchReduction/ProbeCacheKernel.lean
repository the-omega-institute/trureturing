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
