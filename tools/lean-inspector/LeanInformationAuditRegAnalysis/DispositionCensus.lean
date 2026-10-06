import LeanInformationAuditRegAnalysis.Projection.AnalysisInventory
import LeanInformationAuditRegAnalysis.Census.Manifest


namespace LeanInformationAudit

open Lean

namespace DispositionCensus

def artifact (report : FrozenReport) (inventory : DispositionInventory)
    (sources : Array ProvenanceSource := #[]) : Except String Json := do
  checkCoverage report.headSha report.theorems inventory
  let counts := count inventory
  checkCounts inventory counts
  return Json.mkObj [
    ("schema", toJson "lean-information-disposition-census"),
    ("head_sha", toJson report.headSha), ("report_sha256", toJson report.reportSha256),
    ("source_inputs", toJson sources),
    ("theorem_count", toJson report.theorems.size), ("counts", toJson counts),
    ("certified_complete", toJson (counts.observed == 0)),
    ("rows", Json.arr <| inventory.sortedEntries.map dispositionRowJson)]

/-- Independently checks an output projection against its input inventory. -/
def checkArtifact (report : FrozenReport) (inventory : DispositionInventory)
    (candidate : Json) (sources : Array ProvenanceSource := #[]) : Except String Unit := do
  let expected ← artifact report inventory sources
  for field in censusArtifactFields do
    let expectedValue ← expected.getObjVal? field
    let actual ← match candidate.getObjVal? field with
      | .ok value => pure value
      | .error _ => throw <| censusError report.headSha field expectedValue.compress "missing"
    unless expectedValue.compress == actual.compress do
      throw <| censusError report.headSha field expectedValue.compress actual.compress
  validateAnalysisInventory .anonymous candidate


end DispositionCensus
end LeanInformationAudit
