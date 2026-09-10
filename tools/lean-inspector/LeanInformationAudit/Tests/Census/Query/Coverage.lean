import LeanInformationAudit.Census.Publish

open Lean LeanInformationAudit

namespace LeanInformationAudit.Tests.Census.Query

private def rows : CensusKeyManifest :=
  ⟨"head", "digest", `Scope, [0, 1]⟩

example : CensusKeyManifest.IdCoverage rows.keys 2 rows.keys.toFinset :=
  CensusKeyManifest.idCoverage_of_certificate _ _ _ ⟨by decide, rfl, rfl⟩

private def assembled : CensusKeyManifest :=
  { rows with keys := [[0], [], [1]].flatten }

example : CensusKeyManifest.IdCoverage assembled.keys 2 rows.keys.toFinset :=
  CensusKeyManifest.idCoverage_of_certificate _ _ _ ⟨by decide, rfl, rfl⟩

example : !strictlyAscending [0, 0] := by decide
example : !strictlyAscending [1, 0] := by decide

end LeanInformationAudit.Tests.Census.Query
