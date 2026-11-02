import Lean

/-! The real-negative fixtures need every protected D5 ancestor, including
transitive imports. Read compiler headers rather than maintaining another
source-import parser or a fixed list of those ancestors. -/
open Lean

private def targets : Array Name := #[
  `D5.S0.Tower.NonPisotVerdict.SubstitutionTowerClause,
  `D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeFactivity]

private def basis : String := "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"

private def ownedName (name : Name) : Name :=
  (String.ofList name.toString.toList).toName

@[noinline] private unsafe def imports (name : Name) : IO (Array Name) := do
  let (names, region) ← do
    let (data, region) ← readModuleData (← findOLean name)
    pure (data.imports.map fun i => ownedName i.module, region)
  region.free
  return names

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let result ← IO.Process.output {cmd := "git", args := #[
    "ls-tree", "-r", "--name-only", basis, "--", "Golden/Frozen/state/D5"]}
  unless result.exitCode == 0 do IO.eprintln result.stderr; return 2
  let frozen := result.stdout.splitOn "\n" |>.filterMap fun path => do
    unless path.endsWith ".lean.json" do none
    return ((path.drop "Golden/Frozen/state/".length).toString.dropEnd
      ".lean.json".length).toString.replace "/" "." |>.toName
  let mut todo := targets
  let mut seen : NameSet := {}
  let mut roots : Array Name := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    todo := todo ++ ((← imports name).filter (·.toString.startsWith "D5."))
    if !targets.contains name && frozen.contains name then roots := roots.push name
  unless !roots.isEmpty do IO.eprintln "fixture has no protected D5 ancestors"; return 2
  IO.println (String.intercalate " " ((roots.qsort Name.quickLt).toList.map Name.toString))
  return 0

