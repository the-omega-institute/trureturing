import LeanInformationAudit.Tests.Occurrence.ImportedArenaSource
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open Lean Lean.Elab.Command LeanInformationAudit

run_cmd do
  let env := (← getEnv).setExporting false
  for (left, right) in #[(
      `ProvenanceProbe.aliasArena, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.localFunctionAlias, `ProvenanceProbe.localFunctionCopy)] do
    let leftInfo ← getConstInfo left
    let rightInfo ← getConstInfo right
    unless leftInfo.value! == rightInfo.value! do
      throwError "compiled arena fixture values differ"
    let leftOwner ← ofExcept <| resolveCanonicalArenaName (env.find? ·) left
    let rightOwner ← ofExcept <| resolveCanonicalArenaName (env.find? ·) right
    unless leftOwner == rightOwner do
      throwError "identical compiled arena values must resolve identically"
  for name in #[`ProvenanceProbe.arena, `ProvenanceProbe.explicitMk,
      `ProvenanceProbe.projected, `ProvenanceProbe.rangeMissing] do
    let .defnInfo _ ← getConstInfo name | throwError "expected definition"
    let resolved ← ofExcept <| resolveCanonicalArenaName (env.find? ·) name
    unless (env.find? resolved).isSome do throwError "arena identity names a missing constant"

/-- error: IE-C003 ArenaResolutionBudgetExceeded arena=ProvenanceProbe.expensive limit=4096 -/
#guard_msgs (error) in
run_cmd do
  discard <| ofExcept <| resolveCanonicalArenaName ((← getEnv).find? ·) `ProvenanceProbe.expensive
