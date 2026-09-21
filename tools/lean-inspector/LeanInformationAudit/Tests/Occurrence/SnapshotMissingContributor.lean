import LeanInformationAudit.Tests.Occurrence.RootCatalog.Snapshot

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.Occurrence.RootCatalog

namespace LeanInformationAudit.Tests.SnapshotMissingContributor

-- Import expectations and pure premises, but neither native contributor.
run_cmd do
  let original ← getEnv
  try
    modifyEnv (·.setMainModule designatedRoot)
    RootCatalogs.declare designatedContract
    unless (InformationRegistry.entries (← getEnv)).isEmpty do
      throwError "missing-contributor control imported registrations"
    let expected := sourceRows.map (fun row =>
      row.objectArenaName.toString ++ "/" ++ row.theoremName.toString) |>.qsort (· < ·)
    unless expected.size == 3 do throwError "missing-contributor control lost expectations"
    let savedMessages := (← get).messages
    modify fun state => { state with messages := {} }
    elabCommand (← `(command| #seal_information_theory))
    let errors := (← get).messages.toArray.filter (·.severity == .error)
    modify fun state => { state with messages := savedMessages }
    unless errors.size == 1 do throwError "missing-contributor control needs one seal error"
    let message ← errors[0]!.data.toString
    let wanted := s!"IE-C028 AnalysisCertificateMismatch root={designatedRoot} " ++
      "catalog=registry-snapshot component=member-set " ++
      s!"expected={(toJson expected).compress} actual=[]"
    unless message == wanted do throwError "missing-contributor control: {message}"
    unless (SealRecords.forRoot (← getEnv) designatedRoot).isEmpty do
      throwError "missing-contributor failure published seal records"
    logInfo "supplied root rejects both missing contributors with exact member-set payload"
  finally
    setEnv original

end LeanInformationAudit.Tests.SnapshotMissingContributor
