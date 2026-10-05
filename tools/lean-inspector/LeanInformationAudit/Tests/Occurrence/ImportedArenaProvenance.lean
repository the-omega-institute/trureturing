import LeanInformationAudit.Tests.Occurrence.ImportedArenaSource
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open Lean Lean.Elab.Command LeanInformationAudit

run_cmd do
  for (left, right) in #[(
      `ProvenanceProbe.aliasArena, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.localFunctionAlias, `ProvenanceProbe.localFunctionCopy)] do
    let leftInfo ← getConstInfo left
    let rightInfo ← getConstInfo right
    unless leftInfo.value! == rightInfo.value! do
      throwError "compiled arena fixture values differ"
    let leftOwner ← liftTermElabM <| resolveCanonicalArenaName left
    let rightOwner ← liftTermElabM <| resolveCanonicalArenaName right
    unless leftOwner == rightOwner do
      throwError "identical compiled arena values must resolve identically"
  for name in #[`ProvenanceProbe.arena, `ProvenanceProbe.explicitMk,
      `ProvenanceProbe.projected, `ProvenanceProbe.rangeMissing] do
    let .defnInfo info ← getConstInfo name | throwError "expected definition"
    let value ← liftTermElabM <| ArenaProvenance.declarationValue info
    unless value == info.value do throwError "arena decoder changed compiled expression"

/-- error: IE-C003 ArenaResolutionBudgetExceeded arena=ProvenanceProbe.expensive limit=4096 -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <| resolveCanonicalArenaName `ProvenanceProbe.expensive
