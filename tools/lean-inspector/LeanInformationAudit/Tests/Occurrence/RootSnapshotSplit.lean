import LeanInformationAudit.SealCommand

open Lean LeanInformationAudit

namespace LeanInformationAudit.Tests.RootSnapshotSplit

run_cmd do
  let empty ← Lean.Elab.Command.liftIO mkEmptyEnvironment
  let frozen := expectedOccurrencesForRoot empty frozenInformationRootId
  let designated := expectedOccurrencesForRoot empty designatedInformationRootId
  unless frozen.size == 11 && designated.size == 13 do
    throwError "ROOT-B-snapshot-split: expected frozen=11 designated=13, got {frozen.size}/{designated.size}"
  unless frozen.all (fun row => row.registrationModuleName == frozenInformationRootId) do
    throwError "ROOT-B-snapshot-split: frozen contributor changed"
  let causal := designated.filter (·.registrationModuleName != frozenInformationRootId)
  unless causal.size == 2 && causal.all (fun row =>
      row.objectArenaName ==
        `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena &&
      row.registrationModuleName ==
        `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalRegistration) do
    throwError "ROOT-B-snapshot-split: causal occurrence identity changed"
  let ordinary := `LeanInformationAudit.Tests.RootSnapshotSplit
  unless (expectedOccurrencesForRoot empty ordinary).isEmpty do
    throwError "ROOT-B-snapshot-split: ordinary roots acquired fixed expectations"

end LeanInformationAudit.Tests.RootSnapshotSplit
