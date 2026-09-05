import LeanInformationAudit.Registry
import LeanInformationAudit.SnapshotTypes

open Lean LeanInformationAudit

/-- Capture the existing repository enumerator's complete module/source table. -/
private def sourceTable (repository : System.FilePath) : IO (Array (Name × String)) := do
  let enumerator := repository / "tools/scripts/report/lean-report-input.sh"
  let output ← IO.Process.output {
    cmd := enumerator.toString
    args := #["modules", "--repository", repository.toString]
  }
  unless output.exitCode == 0 do
    throw <| IO.userError s!"module enumeration failed: {output.stderr}"
  output.stdout.trimAscii.toString.splitOn "\n" |>.toArray.mapM fun line => do
    match line.splitOn "\t" with
    | [moduleName, sourcePath] =>
        let bytes ← IO.FS.readBinFile (repository / sourcePath)
        pure (moduleName.toName, sourcePath ++ "\tsha256:" ++ Sha256.hex bytes)
    | _ => throw <| IO.userError "invalid enumerator module row"

/-- Producer command: persist expectations from a separate full-source environment.
The generated declaration is imported as data; seals never invoke this command. -/
unsafe def main (args : List String) : IO Unit := do
  let [repositoryArg, outputPath] := args
    | throw <| IO.userError "usage: SnapshotEnumerator REPOSITORY OUTPUT.lean"
  let repository : System.FilePath := repositoryArg
  let table ← sourceTable repository
  let revision ← IO.Process.output {
    cmd := "git", args := #["-C", repositoryArg, "rev-parse", "HEAD"]
  }
  unless revision.exitCode == 0 do
    throw <| IO.userError "source revision is unavailable"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (table.map fun row => { module := row.1 }) {}
    (trustLevel := 0) (loadExts := true)
  let entries := InformationRegistry.entries env |>.qsort fun left right =>
    left.occurrenceKeyString < right.occurrenceKeyString
  if entries.isEmpty then
    throw <| IO.userError "no registrations in the enumerated source snapshot"
  let occurrences := entries.map fun entry => ({
    objectArenaName := entry.canonicalObjectArenaName
    theoremName := entry.theoremName
    statementIdentity := entry.statementIdentity
    registrationModuleName := entry.registrationModuleName
  } : SnapshotOccurrence)
  unless (← sourceTable repository) == table do
    throw <| IO.userError "source snapshot changed during enumeration"
  let snapshot : InformationSourceSnapshot := {
    sourceIdentity := "sha256:" ++ Sha256.hex (reprStr table).toUTF8
    sourceRevision := revision.stdout.trimAscii.toString
    enumeratorIdentity := "sha256:" ++ Sha256.hex
      (← IO.FS.readBinFile (repository / "tools/scripts/report/lean-report-input.sh"))
    moduleCount := table.size
    occurrences
  }
  IO.FS.writeFile outputPath <|
    "import LeanInformationAudit.SnapshotTypes\n\n" ++
    "namespace LeanInformationAudit\n\n" ++
    "-- Produced by SnapshotEnumerator from the identified source snapshot.\n" ++
    "def fixedInformationSourceSnapshot : InformationSourceSnapshot :=\n" ++
    reprStr snapshot ++ "\n\nend LeanInformationAudit\n"
  IO.println s!"snapshot={snapshot.sourceIdentity} modules={table.size} occurrences={entries.size}"
