import LeanInformationAuditRegAnalysis.SearchReduction.Index

/-! Retrieval keeps the original environment boundary and the empty-index
contract even when subsequent proof checking adds declarations. -/
namespace LeanInformationAudit.Tests.SearchReduction.IndexQueries
open Lean Meta Elab LeanInformationAudit.SearchReduction

run_elab do
  let index ← factIndex
  let late := `LeanInformationAudit.Tests.SearchReduction.IndexQueries.late
  let type := mkConst ``True
  addDecl (.thmDecl {name := late, levelParams := [], type, value := mkConst ``True.intro})
  let oldStatements ← (statementCandidates type.hash).run' index
  let oldMatchers ← (matcherCandidates (statementHead type)).run' index
  if oldStatements.contains late || oldMatchers.contains late then
    throwError "query-local retrieval leaked a later declaration"
  let current ← factIndex
  let newStatements ← (statementCandidates type.hash).run' current
  let newMatchers ← (matcherCandidates (statementHead type)).run' current
  unless newStatements.contains late && newMatchers.contains late do
    throwError "query-local retrieval lost a declaration in its own snapshot"
  unless (← (statementCandidates type.hash).run' {}).isEmpty &&
      (← (matcherCandidates (statementHead type)).run' {}).isEmpty &&
      (← (projectionCandidates type).run' {}).isEmpty do
    throwError "default empty index acquired ambient facts"
  logInfo "index query contracts: immutable snapshot and empty default checked"

end LeanInformationAudit.Tests.SearchReduction.IndexQueries
