import LeanInformationAuditRegAnalysis.SearchReduction.DiskLookup

open Lean LeanInformationAudit.SearchReduction.DiskLookup

unsafe def main (args : List String) : IO UInt32 := do
  let basis :: directory :: rest := args
    | IO.eprintln "usage: searchReductionIndex BASIS DIRECTORY [MODULE ...]"; return 2
  initSearchPath (← findSysroot)
  let mut roots := rest.toArray.map String.toName
  let checkSources := rest.isEmpty
  if roots.isEmpty then
    let output ← IO.Process.output {cmd := "git", args := #["ls-tree", "-r", "--name-only", basis,
      "--", "Golden/Frozen/state/D5"]}
    unless output.exitCode == 0 do IO.eprintln output.stderr; return 2
    roots := #[`Mathlib]
    for path in output.stdout.splitOn "\n" do
      if path.endsWith ".lean.json" then
        let name := ((path.drop "Golden/Frozen/state/".length).toString.dropEnd ".lean.json".length).toString
        roots := roots.push (name.replace "/" ".").toName
  let header ← produceMature directory basis "56a005855ea17e0b0958f73ec801ae140b0a1679" roots checkSources
  return if header.complete then 0 else 1
